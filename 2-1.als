module tour/addressBook1

sig Name, Addr {}
sig Book{
	addr:  Name -> lone Addr
}

pred show (b:Book) {
	// アドレス帳 b における名前からアドレスへの対応の個数
	#b.addr > 1
	// b における名前からアドレスへの対応のうち，すべての名前 Name が指し示すアドレスの集合の個数
	#Name.(b.addr) >1
}

run show for 3 but 1 Book

pred add (b, b' : Book, n: Name, a: Addr){
	b'.addr = b.addr + n -> a
}

pred showAdd (b, b' : Book, n: Name, a: Addr){
	// addの呼び出し
	add[b, b', n, a]
	// 制約
	#Name.(b'.addr) > 1
}

run showAdd for 3 but 2 Book

// 前のアドレス帳 b から名前 n に対応するリンクを全て削除
pred del (b, b' : Book, n: Name) {
	b'.addr = b.addr - n-> Addr
}

// bのaddrが含む対応関係のうち，名前 n が指し示すアドレスの集合を参照する
fun lookup (b: Book, n: Name) : set Addr {
	n.(b.addr)
}

/**
  * 加えて削除したら元に戻ることを確認
  */
// b にエントリを加えて b' にした後，同じ名前のエントリを削除した b''におけるアドレスの対応は
// 元のアドレス帳bにおける対応とおなじになることを確認する
assert delUndoesAdd {
	all b, b', b'' : Book , n: Name, a: Addr |
		no n.(b.addr) and add [b, b', n, a] and del [b', b'', n] 
			implies b.addr = b''.addr
}

check delUndoesAdd for 10 but 3 Book

// addはべき等か？
assert addIdempotent {
	all b, b', b'' : Book, n: Name, a: Addr |
		add [b, b', n, a] and add [b', b'', n, a] implies b'.addr = b''.addr
}

// addは局所的か？
// 名前 n のエントリを追加しても，異なる名前 n'が指し示すアドレスの集合は変化しないか？
assert addLocal {
	all b, b' : Book, n, n' : Name, a : Addr |
		add [b, b', n, a] and n != n' implies lookup [b, n'] = lookup [b', n']
}

check addIdempotent for 3
check addLocal for 3 but 2 Book
