#include <bits/stdc++.h>
#include <cstdlib>
#include <iostream>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
using namespace std;
//#define DEBUG
# define likely(x)  __builtin_expect(!!(x), 1)
# define unlikely(x)    __builtin_expect(!!(x), 0)
typedef uint32_t uint;
#define getTime(x) std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - x).count()

#define MAX_EDGE_NUM 2500000
#define MAX_NODE_NUM 1000000
#define MAX_HASH_NUM 0x3FFFFF
#define THREAD_NUM 12
#define TASK_SIZE 100
#define HEAP_KIND 4
#define MAX_PREV_NUM 150


const char* inputPath = "/data/test_data.txt";
const char* outputPath = "/projects/student/result.txt";

//const char* inputPath = "resources/test_data3.txt";
//const char* outputPath = "resources/ans3.txt";

struct EdgeShort{
    uint to_idx;
    ushort val;
};

struct ResultInfo{
    double delta;
    double bc;
};

struct ThreadInfo{
    priority_queue<ushort,vector<ushort>,greater<ushort>> que_short;
    vector<uint> dis_vector[65535];
    ushort sigma[MAX_NODE_NUM];
    ResultInfo resultInfo[MAX_NODE_NUM];
    uint node_stack[MAX_NODE_NUM];
    uint prev_nodes[MAX_NODE_NUM][MAX_PREV_NUM];

    inline vector<uint>* getVector(const ushort cur_dis){
        return &dis_vector[cur_dis];
    }
};
uint edges[MAX_EDGE_NUM][3];
pair<uint, double> bc_count[MAX_NODE_NUM];
uint trf[MAX_NODE_NUM];
uint bfs_idx2idx[MAX_NODE_NUM];
int in_old[MAX_NODE_NUM];
int out_old[MAX_NODE_NUM];
int in[MAX_NODE_NUM];
int out[MAX_NODE_NUM];
int graph_size[MAX_NODE_NUM];

EdgeShort graphShort[MAX_EDGE_NUM];
uint dis_global[THREAD_NUM][MAX_NODE_NUM];
int graph_info[MAX_NODE_NUM];
EdgeShort graph_old[MAX_EDGE_NUM];
int graph_info_old[MAX_NODE_NUM];
int myHash[MAX_HASH_NUM][2];
ThreadInfo infos[THREAD_NUM];

uint node_weight[MAX_NODE_NUM];
uint bfs_queue[MAX_NODE_NUM];
bool bfs_walked[MAX_NODE_NUM];
char *buf;
int ans_num = 0;
uint node_size = 0;
mutex thread_lock;
int cur_task_idx;

bool rvs_double_cmp(pair<uint, double>& a, pair<uint, double>& b){
    return abs(a.second - b.second) <= 0.0001 ? a.first < b.first : a.second > b.second;
}

int hash_get(int key){
    int pos = key & MAX_HASH_NUM;
    while(myHash[pos&MAX_HASH_NUM][0] != -1){
        if(myHash[pos&MAX_HASH_NUM][0] == key)
            return myHash[pos&MAX_HASH_NUM][1];
        pos++;
    }
    return -1;
}

void hash_set(int key,int value){
    int pos = key & MAX_HASH_NUM;
    while(myHash[pos & MAX_HASH_NUM][0] != -1){
        pos++;
    }
    myHash[pos & MAX_HASH_NUM][0] = key;
    myHash[pos & MAX_HASH_NUM][1] = value;
}


void inputFile(){
    memset(myHash,0xff, MAX_HASH_NUM * 2 * sizeof(int));
    int fd = open(inputPath,O_RDONLY);
    uint test_data_size = lseek(fd,0,SEEK_END);
    buf = (char *)mmap(nullptr, test_data_size, PROT_READ, MAP_PRIVATE, fd,0);
    uint offset = 0, fr = 0, to = 0, fr_idx = 0, to_idx = 0, val = 0;
    char *start = buf,*end = buf + test_data_size;
    uint  edges_size = 0;
    uint tmp_cnt = 0;
    while(start < end) {
        fr = 0,to = 0,val = 0,offset=0;
        do{
            fr = fr * 10 + start[offset] - '0';
        }while(start[++offset] != ',');

        if (hash_get(fr) == -1) {
            hash_set(fr,node_size);
            trf[node_size] = fr;
            node_size++;
        }
        start = start+offset+1;offset=0;
        //to
        do{
            to = to * 10 + start[offset] - '0';
        }while (start[++offset] != ',');

        if (hash_get(to) == -1) {
            hash_set(to,node_size);
            trf[node_size] = to;
            node_size++;
        }
        offset ++;
        //val
        do{
            val = val * 10 + start[offset] - '0';
        }while (start[++offset] > '/');
        offset += start[offset] == '\r' ? 2 : 1;
        start += offset;
        if(val == 0) {
            tmp_cnt ++;
            continue;
        }
        fr_idx = hash_get(fr);
        to_idx = hash_get(to);
        edges[edges_size][0] = fr_idx;
        edges[edges_size][1] = to_idx;
        edges[edges_size++][2] = val;
        in_old[to_idx] ++;
        out_old[fr_idx] ++;
    }
    // graph_info
    for(int i = 1; i <= node_size; i++){
        graph_info_old[i] = graph_info_old[i - 1] + out_old[i - 1];
    }

    uint edge_fr_idx, edge_to_idx, edge_value;
    for(int i = 0;i < edges_size; i++){
        edge_fr_idx = edges[i][0], edge_to_idx = edges[i][1], edge_value = edges[i][2];
        graph_old[graph_info_old[edge_fr_idx] + graph_size[edge_fr_idx]].to_idx = edge_to_idx;
        graph_old[graph_info_old[edge_fr_idx] + graph_size[edge_fr_idx]].val = edge_value;
        graph_size[edge_fr_idx]++;
    }
#ifdef DEBUG
    cout << "pass 0 num:" << tmp_cnt << endl;
    cout << "node_size:" << node_size << " edge_size:" << edges_size << endl;
#endif
}


void searchOnePointShort(const int point,const int tid){
    ushort* dis = (ushort*)dis_global[tid];
    ushort* sigma = infos[tid].sigma;
    priority_queue<ushort,vector<ushort>,greater<ushort>>& heap = infos[tid].que_short;
    ResultInfo* resultInfo = infos[tid].resultInfo;
    uint* node_stack = infos[tid].node_stack;
    ThreadInfo* info = infos + tid;
    // init
    dis[point] = 0;
    sigma[point] = 1;
    heap.push(0);
    info->dis_vector[0].push_back(point);
    int node_stack_size = 0;
    // dijkstra
    while(!heap.empty()){
        register ushort next_dis;
        register ushort cur_dis = heap.top();
        heap.pop();
        for(int v: *infos[tid].getVector(cur_dis)){
            if(dis[v] < cur_dis)
                continue;
            const ushort cur_sigma = sigma[v];
            node_stack[node_stack_size] = v;
            ++node_stack_size;
            for(int i2 = graph_info[v], to = graph_info[v+1]; i2 < to; i2++){
                uint w = graphShort[i2].to_idx;
                next_dis = graphShort[i2].val + cur_dis;
                if(dis[w] < next_dis){
                }else if(dis[w] > next_dis){
                    dis[w] = next_dis;
                    sigma[w] = cur_sigma;
                    infos[tid].prev_nodes[w][0] = 1;
                    infos[tid].prev_nodes[w][1] = v;
                    vector<uint>* each = infos[tid].getVector(next_dis);
                    if(each->empty())
                        heap.push(next_dis);
                    each->push_back(w);
                }else{
                    sigma[w] += cur_sigma;
                    infos[tid].prev_nodes[w][++infos[tid].prev_nodes[w][0]] = v;
                }
            }
        }
        infos[tid].getVector(cur_dis)->resize(0);
    }

    double weight = node_weight[point];
    resultInfo[point].bc += (weight - 1) * (node_stack_size - 1);
    while(--node_stack_size){
        const uint w = node_stack[node_stack_size];
        const double tmp = 1.0 / sigma[w] + resultInfo[w].delta;
        resultInfo[w].bc += weight * resultInfo[w].delta * sigma[w];
        dis[w] = -1;
        resultInfo[w].delta = 0.0;
        uint* prev_nodes = info->prev_nodes[w];
        for(uint pos = 1; pos <= prev_nodes[0];pos++){
            resultInfo[prev_nodes[pos]].delta += tmp;
        }
    }
    dis[point] = -1;
    resultInfo[point].delta = 0.0;
}

void writeFile(){
    for(int i = 0; i < node_size; i++){
        bc_count[i].first = trf[bfs_queue[i]];
    }
    for(auto & info : infos){
        for(int j = 0;j < node_size;j++)
            bc_count[j].second += info.resultInfo[j].bc;
    }
    sort(bc_count, bc_count + node_size, rvs_double_cmp);
    ofstream fout(outputPath);
    for(int i = 0; i < 100; i++){
        fout<< bc_count[i].first << "," << fixed <<setprecision(3) << bc_count[i].second << endl;
    }
}

void prepare(){
    // init params
    for(int i = 0; i < THREAD_NUM; i++){
        memset(dis_global[i], -1, sizeof(uint) * MAX_NODE_NUM);
    }
    //bfs rebuild graph
    //1. rebuild trf
    int start = 0, end = 0;
    for(int i = 0; i < node_size; i++){
        if(bfs_walked[i])
            continue;
        bfs_walked[i] = true;
        out[end] = out_old[i];
        in[end] = in_old[i];
        bfs_idx2idx[i] = end;
        bfs_queue[end ++] = i;
        while(start < end){
            uint v = bfs_queue[start++];
            for(int j = graph_info_old[v]; j < graph_info_old[v + 1]; j++){
                uint w = graph_old[j].to_idx;
                if(bfs_walked[w])
                    continue;
                bfs_walked[w] = true;
                out[end] = out_old[w];
                in[end] = in_old[w];
                bfs_idx2idx[w] = end;
                bfs_queue[end++] = w;
            }
        }
    }
    //cout << end << endl;
    //2. rebuild graph and precess out=1 in=0 node
    fill(node_weight, node_weight + node_size, 1);
    uint cur_bfs_pos = 0;
    for(int i = 0; i < node_size; i++){
        uint v = bfs_queue[i];
        if(out[i] == 1 && in[i] == 0) {
            node_weight[bfs_idx2idx[graph_old[graph_info_old[v]].to_idx]]++;
            graph_info[i + 1] = graph_info[i];
            continue;
        }
        for(int j = graph_info_old[v]; j < graph_info_old[v + 1]; j++){
            graphShort[cur_bfs_pos].to_idx = bfs_idx2idx[graph_old[j].to_idx];
            graphShort[cur_bfs_pos].val = graph_old[j].val;
            cur_bfs_pos++;
        }
        graph_info[i + 1] = graph_info[i] + graph_info_old[v + 1] - graph_info_old[v];
    }
    //cout << cur_bfs_pos << endl;
}

void threadWork(int tid){
    int task_idx,fr,to;
    while(true){
        thread_lock.lock();
        task_idx = cur_task_idx++;
        thread_lock.unlock();
        fr = task_idx * TASK_SIZE;
        if(fr >= node_size)
            break;
        to = min(fr + TASK_SIZE, (int)node_size);
        for(int i = fr;i < to;i ++){
            if(out[i] == 1 && in[i] == 0)
                continue;
            searchOnePointShort(i,tid);
        }
    }
}

void getResult(){
    thread threads[THREAD_NUM - 1];
    for(int i = 0; i < THREAD_NUM-1; i++){
        threads[i] = thread(threadWork, i);
    }
    threadWork(THREAD_NUM-1);
    for(int i = 0; i < THREAD_NUM - 1; i++){
        threads[i].join();
    }
}

int main(){
    nice(-20);
#ifdef DEBUG
    chrono::steady_clock::time_point st0, st1;
    st0 = st1 = chrono::steady_clock::now();
#endif
    inputFile();
#ifdef DEBUG
    cout << "input file time cost:" << getTime(st1) << "ms" << endl;
    st1 = chrono::steady_clock::now();
#endif
    prepare();
#ifdef DEBUG
    cout << "prepare time cost:" << getTime(st1) << "ms" << endl;
    st1 = chrono::steady_clock::now();
#endif
    getResult();
#ifdef DEBUG
    cout << "findCycle time cost:" << getTime(st1) << "ms" << endl;
    st1 = chrono::steady_clock::now();
#endif
    writeFile();
#ifdef DEBUG
    cout << "writeFile time cost:" << getTime(st1) << "ms" << endl;
    cout << "total time cost:" << getTime(st0) << "ms" << endl;
    cout << "ans_num:" << ans_num << endl;
#endif
}