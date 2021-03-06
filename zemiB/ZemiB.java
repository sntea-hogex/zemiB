package zemiB;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Scanner;
import java.util.Set;

class Trie {
	private List<Node> nodes;
	public Trie() {
		nodes = new ArrayList<Node>();
		nodes.add(new Node(0, nodes));
	}
	
	public void add(List<Integer> s) {
		nodes.get(0).add(s, 0);
	}
	
	public boolean isContain(List<Integer> s) {
		return nodes.get(0).isContain(s, 0);
	}
	
	public void debug() {
		System.out.println(nodes.size());
	}
	
	public Node getRoot() {
		return nodes.get(0);
	}
	
	public Node getNode(int i) {
		return nodes.get(i);
	}
}

class Node {
	private Map<Integer, Node> nextNodes;
	private List<Node> nodes;
	// なんかの役にたつかもしれないのでノードごとに番号をふってます
	private int number;
	private boolean endFlag;
	private Integer len;
	
	public Node(int number, List<Node> nodes) {
		this.nodes = nodes;
		nextNodes = new HashMap<Integer, Node>();
		this.number = number;
		this.endFlag = false;
	}
	
	//sのインデックスi番目以降を挿入する
	public void add(List<Integer> s, int i) {
		if(i == s.size()){
			this.endFlag = true;
			len = s.size();
			return;
		}
		Node next = nextNodes.get(s.get(i));
		if(next == null) {
			next = new Node(nodes.size(), nodes);
			nextNodes.put(s.get(i), next);
			nodes.add(next);
		}
		next.add(s, i+1);
	}
	
	public boolean isContain(List<Integer> s, int i) {
		if(s.size() == i) {
			return this.endFlag;
		}
		Node next = nextNodes.get(s.get(i));
		if(next != null) {
			return next.isContain(s, i+1);
		}
		return false;
	}
	
	public boolean isEnd() {
		return this.endFlag;
	}
	
	public int getNumber() {
		return number;
	}
	
	public Node getNextNode(int character) {
		return nextNodes.get(character);
	}
	
	public int getLen() {
		return this.len;
	}
}

// ビームサーチのノード
class BNode {
	static final int height = 20;
	static final int width = 20;
	// このdx, dyで方向に番号をつける
	// たとえば (-1, 0)方向は0
	static final int dx[] = {-1, 0, 1, 0};
	static final int dy[] = {0, -1, 0, 1};
	static final int NONE = -1;
	// boolean[x][y][方向の番号] ですでに使った辺を管理する
	boolean[][][] usedFlag;
	// 現在の位置
	int x, y;
	int[][] field;
	int eval = 0;
	
	// ログ
	int startX;
	int startY;
	ArrayDeque<Byte> log;
	
	
	public BNode(int[][] field, int x, int y) {
		usedFlag = new boolean[height][width][4];
		for(int i = 0; i < height; i++) {
			for(int j = 0; j < width; j++) {
				Arrays.fill(usedFlag[i][j], false);
			}
		}
		this.eval = 0;
		this.field = field;
		this.x = x;
		this.y = y;
		this.startX = x;
		this.startY = y;
		this.log = new ArrayDeque<Byte>();
	}
	
	public BNode(int[][] field, int eval, int x, int y, int startX, int startY, ArrayDeque<Byte> log, boolean[][][] usedFlag) {
		this.usedFlag = new boolean[height][width][4];
		this.log = log.clone();
		this.startX = startX;
		this.startY = startY;
		
		for(int i = 0; i < height; i++) {
			for(int j = 0; j < width; j++) {
				this.usedFlag[i][j] = usedFlag[i][j].clone();
			}
		}
		this.eval = eval;
		this.field = field;
		this.x = x;
		this.y = y;
	}
	
	private boolean checkRange(int x, int y) {
		return 0 <= x && x < height && 0 <= y && y < width;
	}
	
	static final int ROOT = 100;
	private byte[][] bfs(boolean[][][] usedEdgeFlag, int x, int y) {
		Queue<Point> qu = new ArrayDeque<Point>();
		qu.add(new Point(x, y));
		// 前にどの方向からきたのかをメモっておく
		byte[][] preDirection = new byte[height][width];
		for(byte[] a : preDirection) {
			Arrays.fill(a, (byte)NONE);
		}
		preDirection[x][y] = ROOT;
		while(!qu.isEmpty()) {
			Point currentPoint = qu.poll();
			for(int k = 0; k < 4; k++) {
				if(usedEdgeFlag[currentPoint.getX()][currentPoint.getY()][k]) {
					continue;
				}
				
				int nx = currentPoint.getX()+dx[k];
				int ny = currentPoint.getY()+dy[k];
				if(!checkRange(nx, ny) || preDirection[nx][ny] != NONE){
					continue;
				}
				preDirection[nx][ny] = (byte) ((k+2)%4);
				if(field[nx][ny] == NONE) {
					qu.add(new Point(nx, ny));
				}
			}
		}
		return preDirection;
	}
	
	private List<BNode> enumerate(int x, int y, Node current, boolean[][][] usedEdgeFlag) {
		// まずBFS
		byte[][] preDirection = bfs(usedEdgeFlag, x, y);
		
		// そして次のノードを決める
		List<BNode> res = new ArrayList<BNode>();
		if(current.isEnd()) {
			int length = current.getLen();
//			System.out.println("lengyh: " + length);
//			printPath();
//			printUsedEdge();
			res.add(new BNode(field, eval + length + length*length, x, y, startX, startY, log, usedFlag));
		}
		for(int i = 0; i < height; i++) {
			for(int j = 0; j < width; j++) {
				if(preDirection[i][j] == NONE || field[i][j] == NONE) continue;
				Node next = current.getNextNode(field[i][j]);
				if(next == null) continue;

				int curi = i, curj = j;
				List<Byte> logTmp = new ArrayList<Byte>();
				while(preDirection[curi][curj] != ROOT) {
					int dir = preDirection[curi][curj];
					
					assert(!usedEdgeFlag[curi][curj][dir]);
					usedEdgeFlag[curi][curj][dir] = true;
					assert(!usedEdgeFlag[curi+dx[dir]][curj+dy[dir]][(dir+2)%4]);
					curi += dx[dir];
					curj += dy[dir];
					usedEdgeFlag[curi][curj][(dir+2)%4] = true;
					logTmp.add((byte)((dir+2)%4));
				}
				assert(curi == x); assert(curj == y);
				
//				printPath();
				int unko = log.size();
				for(int ind = logTmp.size()-1; ind >= 0; ind--) {
					log.offerFirst(logTmp.get(ind));
				}
//				printPath();
				
				List<BNode> tmp = enumerate(i, j, next, usedEdgeFlag);
				
				for(int a = 0; a < logTmp.size(); a++) {
					log.pollFirst();
				}
				assert(unko == log.size());
				
				
				curi = i;
				curj = j;
				while(preDirection[curi][curj] != ROOT) {
					int dir = preDirection[curi][curj];
					assert(usedEdgeFlag[curi][curj][dir]);
					usedEdgeFlag[curi][curj][dir] = false;
					curi += dx[dir];
					curj += dy[dir];
					assert(usedEdgeFlag[curi][curj][(dir+2)%4]);
					usedEdgeFlag[curi][curj][(dir+2)%4] = false;
				}
				
				if(tmp.size() > res.size()) {
					List<BNode> a = tmp;
					tmp = res;
					res = a;
				}
				res.addAll(tmp);
			}
		}
//		System.out.println(res.size());
		return res;
	}
	
	public int eval() {
		// 評価値を返す
		return eval;
	}
	
	public List<BNode> generateNextFirst(Trie dictionary) {
		Node node = dictionary.getRoot().getNextNode(field[x][y]);
		if(node == null) {
			return new ArrayList<BNode>();
		}
		return enumerate(x, y, node,usedFlag);
	}
	
	public Deque<Byte> getLog() {
		return log;
	}
	
	static final byte SEPARATOR = 101;
	public List<BNode> generateNext(Trie dictionary) {
		// 次のステップのノードを返す
		byte[][] preDirection = bfs(usedFlag, x, y);
		List<BNode> res = new ArrayList<BNode>();
		
		this.log.offerFirst(SEPARATOR);
		for(int i = 0; i < height; i++) {
			for(int j = 0; j < width; j++) {
				if(i == x && j == y) continue;
				if(field[i][j] == NONE || preDirection[i][j] == NONE) continue;
				Node next = dictionary.getRoot().getNextNode(field[i][j]);
				if(next == null) continue;
				
				int curi = i, curj = j;
				List<Byte> logTmp = new ArrayList<Byte>();
				while(preDirection[curi][curj] != ROOT) {
					int dir = preDirection[curi][curj];
					
					assert(!usedFlag[curi][curj][dir]);
					usedFlag[curi][curj][dir] = true;
					assert(!usedFlag[curi+dx[dir]][curj+dy[dir]][(dir+2)%4]);
					curi += dx[dir];
					curj += dy[dir];
					usedFlag[curi][curj][(dir+2)%4] = true;
					logTmp.add((byte)((dir+2)%4));
				}
				assert(curi == x); assert(curj == y);
				
				int unko = log.size();
				for(int ind = logTmp.size()-1; ind >= 0; ind--) {
					log.offerFirst(logTmp.get(ind));
				}
				
				
				List<BNode> list = enumerate(i, j, next, usedFlag);
				
				for(int tmp = 0; tmp < logTmp.size(); tmp++) {
					log.pollFirst();
				}
				assert(unko == log.size());
				
				curi = i;
				curj = j;
				while(preDirection[curi][curj] != ROOT) {
					int dir = preDirection[curi][curj];
					assert(usedFlag[curi][curj][dir]);
					usedFlag[curi][curj][dir] = false;
					curi += dx[dir];
					curj += dy[dir];
					assert(usedFlag[curi][curj][(dir+2)%4]);
					usedFlag[curi][curj][(dir+2)%4] = false;
				}
					
				res.addAll(list);
			}
		}
		this.log.pollFirst();
		
		return res;
	}
	
	public Point getStart() {
		return new Point(startX, startY);
	}
	
	public boolean[][][] debug() {
		return usedFlag;
	}
	
	public void printPath() {
		Point start = getStart();
		System.out.println("(sx, sy): "+ start.getX() + ", " + start.getY());
		int x = start.getX();
		int y = start.getY();
//		ArrayDeque<Byte> tmp = log.clone();
//		while(!tmp.isEmpty()) {
//			Byte e = tmp.remove();
//			x += dx[e];
//			y += dy[e];
//			System.out.println(e);
//			System.out.println("(x, y): "+ x + ", " + y);
//		}
		ArrayDeque<Byte> hoge = log.clone();
		while(!hoge.isEmpty()) {
			Byte e = hoge.pollLast();
			if(e == SEPARATOR) continue;
			x += dx[e];
			y += dy[e];
			System.out.println("dir: " + e);
			System.out.println("(x, y): "+ x + ", " + y);
		}
//		for(Byte e : log) {
//			x += dx[e];
//			y += dy[e];
//			System.out.println("dir: " + e);
//			System.out.println("(x, y): "+ x + ", " + y);
//		}
	}
	
	public void printAnswer(int[][] field) {
		Point start = getStart();
//		System.out.println("(sx, sy): "+ start.getX() + ", " + start.getY());
		System.out.print((field[start.getX()][start.getY()]+1) + " ");
		int x = start.getX();
		int y = start.getY();
		ArrayDeque<Byte> hoge = log.clone();
		while(!hoge.isEmpty()) {
			Byte e = hoge.pollLast();
			if(e == SEPARATOR) {
				System.out.println();
				continue;
			}
			x += dx[e];
			y += dy[e];
//			System.out.println(field[x][y]);
//			System.out.println(tmp);
			if(field[x][y] != NONE){
				int tmp = field[x][y]+1;
//				System.out.println(field[x][y]);
//				System.out.println(tmp);
				System.out.print(tmp + " ");
			}
		}
		System.out.println();
	}
	
	private void printUsedEdge() {
		int cnt = 0;
		for(int i = 0; i < height; i++) {
			for(int j = 0; j < width; j++) {
				for(int k = 0; k < 4; k++) {
					if(usedFlag[i][j][k]) {
						System.out.print(1);
						cnt += 1;
					} else {
						System.out.print(0);
					}
				}
				System.out.print(" ");
			}
			System.out.println("");
		}
		System.out.println("sum: "+cnt);
	}
}

class Point {
	private int x;
	private int y;

	public Point(int x, int y) {
		this.x = x;
		this.y = y;
	}
	
	public int getX() {
		return x;
	}
	
	public int getY() {
		return y;
	}
}

class BNodeComparator implements Comparator<BNode> {

	@Override
	public int compare(BNode o1, BNode o2) {
		int val1 = o1.eval();
		int val2 = o2.eval();
		if(val1 < val2) {
			return 1;
		} else if(val1 == val2) {
			return 0;
		} else {
			return -1;
		}
	}
	
}

public class ZemiB {

	
	static final int dx[] = {-1, 0, 1, 0};
	static final int dy[] = {0, -1, 0, 1};
	final int height = 20;
	final int width = 20;
	int[][] field;
	Trie dictionary;
	final int NONE = -1;
	
	public ZemiB() {
		field = new int[height][width];
	}
	
	
	
	public static void main(final String[] args) throws FileNotFoundException {
		try {
			(new ZemiB()).run("input.txt", "dictionary.txt");
		} catch (IOException e) {
			// TODO 自動生成された catch ブロック
			e.printStackTrace();
		}
	}

	public void run(final String inputFileName, final String dictFileName) throws IOException{
		for(int i = 0; i < height; i++) {
			Arrays.fill(field[i], NONE);
		}
		
		Map<Integer, Integer> charCount = new HashMap<Integer, Integer>();
		FileReader fr = new FileReader(inputFileName);
		BufferedReader br = new BufferedReader(fr);
		String line;
		while((line = br.readLine()) != null) {
			String[] tmp = line.split(" ", 0);
			int c = Integer.parseInt(tmp[2]);
			int x = Integer.parseInt(tmp[0]);
			int y = Integer.parseInt(tmp[1]);
			c--; x--; y--;
			field[x][y] = c;
			Integer val = charCount.get(c);
			if(val != null) {
				charCount.put(c, val + 1);
			} else {
				charCount.put(c, 1);
			}
		}
		br.close();
		System.out.println("FIELD---------");
		for(int i = 0; i < height; i++) {
			for(int j = 0; j < width; j++) {
				System.out.print(field[i][j] + " ");
			}
			System.out.println("");
		}
		System.out.println("FIELD---------");
		
		dictionary = new Trie();
		fr = new FileReader(dictFileName);
		br = new BufferedReader(fr);
//		String line;
		while ((line = br.readLine()) != null) {
			String[] hoge = line.split(" ", 0);
			List<Integer> tmp = new ArrayList<Integer>();
			Map<Integer, Integer> countTmp = new HashMap<Integer, Integer>();
			for(int i = 0; i < hoge.length; i++) {
				int c = Integer.parseInt(hoge[i])-1;
				Integer val = countTmp.get(c);
				if(val != null) {
					countTmp.put(c, val + 1);
				} else {
					countTmp.put(c, 1);
				}
				tmp.add(c);
			}
			boolean addFlag = true;
			for(Map.Entry<Integer, Integer> e : countTmp.entrySet()) {
				Integer all = charCount.get(e.getKey());
				if(all == null || all < e.getValue()) {
					addFlag = false;
				}
			}
			if(addFlag) dictionary.add(tmp);
		}
		dictionary.debug();
		{
			ArrayList<Integer> tmp = new ArrayList<>();
			tmp.add(6);
			System.out.println(dictionary.isContain(tmp));
		}
		br.close();
		
		for(Map.Entry<Integer, Integer> e : charCount.entrySet()) {
			System.out.println(e.getKey() + ", " + e.getValue());
		}
		BNode ans = search();
		print(ans.debug());
		System.out.println(ans.eval());
		
//		{
//			int sum = 0;
//			Set<Integer> s = new HashSet<Integer>();
//			for(int i = 0; i < height; i++) {
//				for(int j = 0; j < width; j++) {
//					if(field[i][j] == NONE) continue;
//					Node next = dictionary.getRoot().getNextNode(field[i][j]);
//					if(next == null) continue;
//					System.out.println("");
//					System.out.println("char : " + field[i][j]);
//					boolean[][][] usedEdgeFlag = new boolean[height][width][4];
//					for(boolean[][] a : usedEdgeFlag) {
//						for(boolean[] b : a) {
//							Arrays.fill(b, false);
//						}
//					}
//					List<Integer> list = enumerate(i, j, next, usedEdgeFlag);
//					s.addAll(list);
//					System.out.println(list.size());
//					sum += list.size();
//					System.out.println(s.size());
//				}
//			}
//			System.out.println("sum : " + sum);
//			System.out.println("set : " + s.size());
//		}
	}
	
	private boolean checkRange(int x, int y) {
		return 0 <= x && x < height && 0 <= y && y < width;
	}
	
	private void check(boolean[][][] usedEdgeFlag) {
		for(int i = 0; i < height; i++) {
			for(int j = 0; j < width; j++) {
				for(int k = 0; k < 4; k++) {
					if(usedEdgeFlag[i][j][k]) {
						assert(usedEdgeFlag[i+dx[k]][j+dy[k]][(k+2)%4]);
					}
				}
			}
		}
	}
	
	private void print(boolean[][][] usedEdgeFlag) {
		int cnt = 0;
		for(int i = 0; i < height; i++) {
			for(int j = 0; j < width; j++) {
				for(int k = 0; k < 4; k++) {
					if(usedEdgeFlag[i][j][k]) {
						System.out.print(1);
						cnt += 1;
					} else {
						System.out.print(0);
					}
				}
				System.out.print(" ");
			}
			System.out.println("");
		}
		System.out.println("sum: "+cnt);
	}
	
	private void print_dirs(int[][] hoge) {
		for(int i = 0; i < height; i++) {
			for(int j = 0; j < width; j++) {
				System.out.print(hoge[i][j]+" ");
			}
			System.out.println("");
		}
	}
	
	
	private List<Integer> enumerate(int x, int y, Node current, boolean[][][] usedEdgeFlag) {
		// まずBFS
//		System.out.println("x : " + x);
//		System.out.println("y : " + y);
//		System.out.println("START  (x, y) : " + "(" + x + ", " + y + ")");
		Queue<Point> qu = new ArrayDeque<Point>();
		qu.add(new Point(x, y));
		// 前にどの方向からきたのかをメモっておく
		int[][] preDirection = new int[height][width];
		for(int[] a : preDirection) {
			Arrays.fill(a, NONE);
		}
		final int ROOT = 100;
		preDirection[x][y] = ROOT;
		while(!qu.isEmpty()) {
			Point currentPoint = qu.poll();
			for(int k = 0; k < 4; k++) {
				if(usedEdgeFlag[currentPoint.getX()][currentPoint.getY()][k]) {
					continue;
				}
				
				int nx = currentPoint.getX()+dx[k];
				int ny = currentPoint.getY()+dy[k];
//				System.out.println(nx + ", " + ny + ", " + k);
				if(!checkRange(nx, ny) || preDirection[nx][ny] != NONE){
//					System.out.println("hoge");
					continue;
				}
//				System.out.println(nx + ", " + ny + ", " + k);
//				System.out.println("cur " + currentPoint.getX() + ", " + currentPoint.getY() + ", " + k);
//				System.out.println(dx[k] + " " + dy[k]);
				preDirection[nx][ny] = (k+2)%4;
//				print_dirs(preDirection);
				if(field[nx][ny] == NONE) {
					qu.add(new Point(nx, ny));
				}
			}
		}
		
//		System.out.println("unnko");
		
		// そして次のノードを決める
		List<Integer> res = new ArrayList<Integer>();
		if(current.isEnd()) {
			res.add(current.getNumber());
		}
//		print_dirs(preDirection);
		for(int i = 0; i < height; i++) {
			for(int j = 0; j < width; j++) {
				if(preDirection[i][j] == NONE || field[i][j] == NONE) continue;
				Node next = current.getNextNode(field[i][j]);
				if(next == null) continue;
				
				int curi = i, curj = j;
				while(preDirection[curi][curj] != ROOT) {
					int dir = preDirection[curi][curj];
					
					assert(!usedEdgeFlag[curi][curj][dir]);
					usedEdgeFlag[curi][curj][dir] = true;
					assert(!usedEdgeFlag[curi+dx[dir]][curj+dy[dir]][(dir+2)%4]);
					curi += dx[dir];
					curj += dy[dir];
					assert(curi > 0 && curj > 0);
					usedEdgeFlag[curi][curj][(dir+2)%4] = true;
				}
//				check(usedEdgeFlag);
				assert(curi == x); assert(curj == y);
				
				List<Integer> tmp = enumerate(i, j, next, usedEdgeFlag);
				
				curi = i;
				curj = j;
				while(preDirection[curi][curj] != ROOT) {
					int dir = preDirection[curi][curj];
					assert(usedEdgeFlag[curi][curj][dir]);
					usedEdgeFlag[curi][curj][dir] = false;
					curi += dx[dir];
					curj += dy[dir];
					assert(usedEdgeFlag[curi][curj][(dir+2)%4]);
					usedEdgeFlag[curi][curj][(dir+2)%4] = false;
				}
				
				if(tmp.size() > res.size()) {
					List<Integer> a = tmp;
					tmp = res;
					res = a;
				}
				res.addAll(tmp);
			}
		}
//		System.out.println("END  (x, y) : " + "(" + x + ", " + y + ")");
		return res;
	}
	
	
	private void printNodes(List<BNode> nodes) {
		for(BNode e : nodes) {
			System.out.print(e.eval() + " ");
		}
		System.out.println("");
	}
	
	private BNode search() {
		final int BeamWidth = 300;
		List<BNode> nodes = new ArrayList<BNode>();
		// スタートを列挙
		for(int i = 0; i < height; i++) {
			for(int j = 0; j < width; j++) {
				if(field[i][j] == NONE) continue;
				nodes.addAll((new BNode(field, i, j)).generateNextFirst(dictionary));
				System.out.println("beamnode.size: " + nodes.size());
				Collections.sort(nodes, new BNodeComparator());
				while(nodes.size() > BeamWidth) {
					nodes.remove(nodes.size()-1);
				}
			}
		}
		Collections.sort(nodes, new BNodeComparator());
		while(nodes.size() > BeamWidth) {
			nodes.remove(nodes.size()-1);
		}
		printNodes(nodes);
		
		// 返り値
		BNode res = null;
		// 探索
		do {
			List<BNode> nextNodes = new ArrayList<BNode>();
			for(BNode node : nodes) {
				nextNodes.addAll(node.generateNext(dictionary));
//				System.out.println("nextnodes.size: " + nextNodes.size());
				Collections.sort(nextNodes, new BNodeComparator());
				while(nextNodes.size() > BeamWidth) {
					nextNodes.remove(nextNodes.size()-1);
				}
			}
//			System.out.println("beamsize : " + nextNodes.size());
			if(nextNodes.isEmpty()) break;
			// 大きい順にソート
			Collections.sort(nextNodes, new BNodeComparator());
			// 枝を刈る
			nodes.clear();
			for(int i = 0; i < BeamWidth && i < nextNodes.size(); i++) {
				nodes.add(nextNodes.get(i));
			}
			printNodes(nodes);
			if(res == null) {
				res = nodes.get(0);
			} else {
				if(res.eval() < nodes.get(0).eval()) {
					res = nodes.get(0);
				}
			}
//			System.out.println("eval:" + res.eval());
		} while(true);
		
		res.printPath();
		res.printAnswer(field);
		return res;
	}

}


