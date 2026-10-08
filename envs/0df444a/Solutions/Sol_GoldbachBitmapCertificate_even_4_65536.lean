-- Prove2me | solution 1 for GoldbachBitmapCertificate.even_4_65536
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T01:27:33.230016+00:00
-- url     : https://prove2.me/submissions/407b8d7e-564a-4da9-a975-2425dd9efc7f

import Definitions.Def_GoldbachBitmapCertificate
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace GoldbachCertificate

private lemma primeCheck_spec (p : ℕ) : primeCheck p = true ↔ Nat.Prime p := by
  simp only [primeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun m hm hms => ?_⟩
    exact (h m (by omega)).resolve_left (by omega)
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun m hm => ?_⟩
    by_cases hm2 : m < 2
    · exact Or.inl hm2
    · exact Or.inr (h m (by omega) (by omega))

private lemma PrimeTree.contains_prime (tree : PrimeTree) (n : ℕ)
    (hc : tree.check = true) (hn : tree.contains n = true) : Nat.Prime n := by
  induction tree with
  | empty => simp [PrimeTree.contains] at hn
  | node p left right ihl ihr =>
    simp only [PrimeTree.check, Bool.and_eq_true] at hc
    simp only [PrimeTree.contains] at hn
    split_ifs at hn with heq hlt
    · subst n
      exact (primeCheck_spec p).mp hc.1.1
    · exact ihl hc.1.2 hn
    · exact ihr hc.2 hn

end GoldbachCertificate

namespace GoldbachBitmapCertificate
open GoldbachCertificate

private lemma primeBits_sound (tree : PrimeTree) (base i : ℕ)
    (ht : tree.check = true) (hb : (primeBits base tree).testBit i = true) :
    ∃ q : ℕ, q.Prime ∧ q % 2 = 1 ∧ q / 2 = base + i := by
  induction tree with
  | empty => simp [primeBits] at hb
  | node p left right ihl ihr =>
    simp only [PrimeTree.check, Bool.and_eq_true] at ht
    simp only [primeBits, Nat.testBit_lor, Bool.or_eq_true] at hb
    rcases hb with (hb | hb) | hb
    · split_ifs at hb with hp
      · rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hb
        have hi : p / 2 - base = i := of_decide_eq_true hb
        exact ⟨p, (primeCheck_spec p).mp ht.1.1, hp.1, by omega⟩
      · simp at hb
    · exact ihl ht.1.2 hb
    · exact ihr ht.2 hb

private lemma sumBits_sound (left : List ℕ) (tree : PrimeTree)
    (ht : tree.check = true) (right smallBound i : ℕ)
    (hl : leftCheck smallBound tree left = true)
    (hb : (sumBits right left).testBit i = true) :
    ∃ p j : ℕ, p.Prime ∧ p % 2 = 1 ∧ p ≤ smallBound ∧
      right.testBit j = true ∧ i = j + p / 2 + 1 := by
  induction left with
  | nil => simp [sumBits] at hb
  | cons p ps ih =>
    simp only [leftCheck, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
    simp only [sumBits, Nat.testBit_lor, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hb
      exact ⟨p, i - (p / 2 + 1), tree.contains_prime p ht hl.1.1,
        hl.1.2.1, hl.1.2.2, hb.2, by omega⟩
    · exact ih hl.2 hb

private lemma intervalMask_bit (first count i : ℕ) (hlo : first ≤ i)
    (hhi : i < first + count) : (intervalMask first count).testBit i = true := by
  simp only [intervalMask, Nat.testBit_shiftLeft, Nat.one_shiftLeft,
    Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq]
  omega

private lemma covers_bit (base first count i : ℕ) (tree : PrimeTree) (left : List ℕ)
    (hc : covers base first count tree left = true) (hlo : first ≤ i)
    (hhi : i < first + count) : (sumBits (primeBits base tree) left).testBit i = true := by
  have heq : (sumBits (primeBits base tree) left &&& intervalMask first count) =
      intervalMask first count := of_decide_eq_true hc
  have hb := congrArg (fun x : ℕ => x.testBit i) heq
  rw [Nat.testBit_land, intervalMask_bit first count i hlo hhi] at hb
  simpa using hb

private lemma block_sound (base first count smallBound : ℕ) (tree : PrimeTree)
    (left : List ℕ) (ht : tree.check = true)
    (hl : leftCheck smallBound tree left = true)
    (hc : covers base first count tree left = true)
    (n : ℕ) (hlo : 2 * (base + first) ≤ n)
    (hhi : n < 2 * (base + first + count)) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ smallBound ∧ n = p + q := by
  obtain ⟨k, hk⟩ := he
  have hi : first ≤ n / 2 - base := by omega
  have hi' : n / 2 - base < first + count := by omega
  have hb := covers_bit base first count (n / 2 - base) tree left hc hi hi'
  obtain ⟨p, j, hp, hpo, hpb, hj, heq⟩ :=
    sumBits_sound left tree ht (primeBits base tree) smallBound (n / 2 - base) hl hb
  obtain ⟨q, hq, hqo, hqj⟩ := primeBits_sound tree base j ht hj
  exact ⟨p, q, hp, hq, hpb, by omega⟩

end GoldbachBitmapCertificate

namespace GoldbachBitmapData4_65536_greedy
open GoldbachCertificate GoldbachBitmapCertificate

def primes : PrimeTree := (.node 3251 (.node 1447 (.node 631 (.node 271 (.node 109 (.node 47 (.node 19 (.node 7 (.node 3 (.node 2 .empty .empty) (.node 5 .empty .empty)) (.node 13 (.node 11 .empty .empty) (.node 17 .empty .empty))) (.node 37 (.node 29 (.node 23 .empty .empty) (.node 31 .empty .empty)) (.node 43 (.node 41 .empty .empty) .empty))) (.node 79 (.node 67 (.node 59 (.node 53 .empty .empty) (.node 61 .empty .empty)) (.node 73 (.node 71 .empty .empty) .empty)) (.node 101 (.node 89 (.node 83 .empty .empty) (.node 97 .empty .empty)) (.node 107 (.node 103 .empty .empty) .empty)))) (.node 193 (.node 157 (.node 137 (.node 127 (.node 113 .empty .empty) (.node 131 .empty .empty)) (.node 149 (.node 139 .empty .empty) (.node 151 .empty .empty))) (.node 179 (.node 167 (.node 163 .empty .empty) (.node 173 .empty .empty)) (.node 191 (.node 181 .empty .empty) .empty))) (.node 233 (.node 223 (.node 199 (.node 197 .empty .empty) (.node 211 .empty .empty)) (.node 229 (.node 227 .empty .empty) .empty)) (.node 257 (.node 241 (.node 239 .empty .empty) (.node 251 .empty .empty)) (.node 269 (.node 263 .empty .empty) .empty))))) (.node 449 (.node 367 (.node 317 (.node 293 (.node 281 (.node 277 .empty .empty) (.node 283 .empty .empty)) (.node 311 (.node 307 .empty .empty) (.node 313 .empty .empty))) (.node 349 (.node 337 (.node 331 .empty .empty) (.node 347 .empty .empty)) (.node 359 (.node 353 .empty .empty) .empty))) (.node 409 (.node 389 (.node 379 (.node 373 .empty .empty) (.node 383 .empty .empty)) (.node 401 (.node 397 .empty .empty) .empty)) (.node 433 (.node 421 (.node 419 .empty .empty) (.node 431 .empty .empty)) (.node 443 (.node 439 .empty .empty) .empty)))) (.node 547 (.node 491 (.node 467 (.node 461 (.node 457 .empty .empty) (.node 463 .empty .empty)) (.node 487 (.node 479 .empty .empty) .empty)) (.node 521 (.node 503 (.node 499 .empty .empty) (.node 509 .empty .empty)) (.node 541 (.node 523 .empty .empty) .empty))) (.node 593 (.node 571 (.node 563 (.node 557 .empty .empty) (.node 569 .empty .empty)) (.node 587 (.node 577 .empty .empty) .empty)) (.node 613 (.node 601 (.node 599 .empty .empty) (.node 607 .empty .empty)) (.node 619 (.node 617 .empty .empty) .empty)))))) (.node 1021 (.node 827 (.node 733 (.node 677 (.node 653 (.node 643 (.node 641 .empty .empty) (.node 647 .empty .empty)) (.node 661 (.node 659 .empty .empty) (.node 673 .empty .empty))) (.node 709 (.node 691 (.node 683 .empty .empty) (.node 701 .empty .empty)) (.node 727 (.node 719 .empty .empty) .empty))) (.node 773 (.node 757 (.node 743 (.node 739 .empty .empty) (.node 751 .empty .empty)) (.node 769 (.node 761 .empty .empty) .empty)) (.node 811 (.node 797 (.node 787 .empty .empty) (.node 809 .empty .empty)) (.node 823 (.node 821 .empty .empty) .empty)))) (.node 929 (.node 877 (.node 857 (.node 839 (.node 829 .empty .empty) (.node 853 .empty .empty)) (.node 863 (.node 859 .empty .empty) .empty)) (.node 907 (.node 883 (.node 881 .empty .empty) (.node 887 .empty .empty)) (.node 919 (.node 911 .empty .empty) .empty))) (.node 977 (.node 953 (.node 941 (.node 937 .empty .empty) (.node 947 .empty .empty)) (.node 971 (.node 967 .empty .empty) .empty)) (.node 1009 (.node 991 (.node 983 .empty .empty) (.node 997 .empty .empty)) (.node 1019 (.node 1013 .empty .empty) .empty))))) (.node 1229 (.node 1117 (.node 1069 (.node 1049 (.node 1033 (.node 1031 .empty .empty) (.node 1039 .empty .empty)) (.node 1061 (.node 1051 .empty .empty) (.node 1063 .empty .empty))) (.node 1097 (.node 1091 (.node 1087 .empty .empty) (.node 1093 .empty .empty)) (.node 1109 (.node 1103 .empty .empty) .empty))) (.node 1181 (.node 1153 (.node 1129 (.node 1123 .empty .empty) (.node 1151 .empty .empty)) (.node 1171 (.node 1163 .empty .empty) .empty)) (.node 1213 (.node 1193 (.node 1187 .empty .empty) (.node 1201 .empty .empty)) (.node 1223 (.node 1217 .empty .empty) .empty)))) (.node 1319 (.node 1283 (.node 1259 (.node 1237 (.node 1231 .empty .empty) (.node 1249 .empty .empty)) (.node 1279 (.node 1277 .empty .empty) .empty)) (.node 1301 (.node 1291 (.node 1289 .empty .empty) (.node 1297 .empty .empty)) (.node 1307 (.node 1303 .empty .empty) .empty))) (.node 1399 (.node 1367 (.node 1327 (.node 1321 .empty .empty) (.node 1361 .empty .empty)) (.node 1381 (.node 1373 .empty .empty) .empty)) (.node 1429 (.node 1423 (.node 1409 .empty .empty) (.node 1427 .empty .empty)) (.node 1439 (.node 1433 .empty .empty) .empty))))))) (.node 2311 (.node 1873 (.node 1627 (.node 1549 (.node 1489 (.node 1471 (.node 1453 (.node 1451 .empty .empty) (.node 1459 .empty .empty)) (.node 1483 (.node 1481 .empty .empty) (.node 1487 .empty .empty))) (.node 1523 (.node 1499 (.node 1493 .empty .empty) (.node 1511 .empty .empty)) (.node 1543 (.node 1531 .empty .empty) .empty))) (.node 1597 (.node 1571 (.node 1559 (.node 1553 .empty .empty) (.node 1567 .empty .empty)) (.node 1583 (.node 1579 .empty .empty) .empty)) (.node 1613 (.node 1607 (.node 1601 .empty .empty) (.node 1609 .empty .empty)) (.node 1621 (.node 1619 .empty .empty) .empty)))) (.node 1753 (.node 1699 (.node 1667 (.node 1657 (.node 1637 .empty .empty) (.node 1663 .empty .empty)) (.node 1693 (.node 1669 .empty .empty) (.node 1697 .empty .empty))) (.node 1733 (.node 1721 (.node 1709 .empty .empty) (.node 1723 .empty .empty)) (.node 1747 (.node 1741 .empty .empty) .empty))) (.node 1811 (.node 1787 (.node 1777 (.node 1759 .empty .empty) (.node 1783 .empty .empty)) (.node 1801 (.node 1789 .empty .empty) .empty)) (.node 1861 (.node 1831 (.node 1823 .empty .empty) (.node 1847 .empty .empty)) (.node 1871 (.node 1867 .empty .empty) .empty))))) (.node 2089 (.node 1997 (.node 1933 (.node 1901 (.node 1879 (.node 1877 .empty .empty) (.node 1889 .empty .empty)) (.node 1913 (.node 1907 .empty .empty) (.node 1931 .empty .empty))) (.node 1979 (.node 1951 (.node 1949 .empty .empty) (.node 1973 .empty .empty)) (.node 1993 (.node 1987 .empty .empty) .empty))) (.node 2039 (.node 2017 (.node 2003 (.node 1999 .empty .empty) (.node 2011 .empty .empty)) (.node 2029 (.node 2027 .empty .empty) .empty)) (.node 2081 (.node 2063 (.node 2053 .empty .empty) (.node 2069 .empty .empty)) (.node 2087 (.node 2083 .empty .empty) .empty)))) (.node 2213 (.node 2141 (.node 2129 (.node 2111 (.node 2099 .empty .empty) (.node 2113 .empty .empty)) (.node 2137 (.node 2131 .empty .empty) .empty)) (.node 2179 (.node 2153 (.node 2143 .empty .empty) (.node 2161 .empty .empty)) (.node 2207 (.node 2203 .empty .empty) .empty))) (.node 2269 (.node 2243 (.node 2237 (.node 2221 .empty .empty) (.node 2239 .empty .empty)) (.node 2267 (.node 2251 .empty .empty) .empty)) (.node 2293 (.node 2281 (.node 2273 .empty .empty) (.node 2287 .empty .empty)) (.node 2309 (.node 2297 .empty .empty) .empty)))))) (.node 2749 (.node 2549 (.node 2417 (.node 2377 (.node 2347 (.node 2339 (.node 2333 .empty .empty) (.node 2341 .empty .empty)) (.node 2357 (.node 2351 .empty .empty) (.node 2371 .empty .empty))) (.node 2393 (.node 2383 (.node 2381 .empty .empty) (.node 2389 .empty .empty)) (.node 2411 (.node 2399 .empty .empty) .empty))) (.node 2473 (.node 2447 (.node 2437 (.node 2423 .empty .empty) (.node 2441 .empty .empty)) (.node 2467 (.node 2459 .empty .empty) .empty)) (.node 2531 (.node 2503 (.node 2477 .empty .empty) (.node 2521 .empty .empty)) (.node 2543 (.node 2539 .empty .empty) .empty)))) (.node 2671 (.node 2617 (.node 2591 (.node 2557 (.node 2551 .empty .empty) (.node 2579 .empty .empty)) (.node 2609 (.node 2593 .empty .empty) .empty)) (.node 2657 (.node 2633 (.node 2621 .empty .empty) (.node 2647 .empty .empty)) (.node 2663 (.node 2659 .empty .empty) .empty))) (.node 2707 (.node 2689 (.node 2683 (.node 2677 .empty .empty) (.node 2687 .empty .empty)) (.node 2699 (.node 2693 .empty .empty) .empty)) (.node 2729 (.node 2713 (.node 2711 .empty .empty) (.node 2719 .empty .empty)) (.node 2741 (.node 2731 .empty .empty) .empty))))) (.node 2999 (.node 2861 (.node 2803 (.node 2789 (.node 2767 (.node 2753 .empty .empty) (.node 2777 .empty .empty)) (.node 2797 (.node 2791 .empty .empty) (.node 2801 .empty .empty))) (.node 2843 (.node 2833 (.node 2819 .empty .empty) (.node 2837 .empty .empty)) (.node 2857 (.node 2851 .empty .empty) .empty))) (.node 2927 (.node 2903 (.node 2887 (.node 2879 .empty .empty) (.node 2897 .empty .empty)) (.node 2917 (.node 2909 .empty .empty) .empty)) (.node 2963 (.node 2953 (.node 2939 .empty .empty) (.node 2957 .empty .empty)) (.node 2971 (.node 2969 .empty .empty) .empty)))) (.node 3119 (.node 3049 (.node 3023 (.node 3011 (.node 3001 .empty .empty) (.node 3019 .empty .empty)) (.node 3041 (.node 3037 .empty .empty) .empty)) (.node 3083 (.node 3067 (.node 3061 .empty .empty) (.node 3079 .empty .empty)) (.node 3109 (.node 3089 .empty .empty) .empty))) (.node 3187 (.node 3167 (.node 3137 (.node 3121 .empty .empty) (.node 3163 .empty .empty)) (.node 3181 (.node 3169 .empty .empty) .empty)) (.node 3217 (.node 3203 (.node 3191 .empty .empty) (.node 3209 .empty .empty)) (.node 3229 (.node 3221 .empty .empty) .empty)))))))) (.node 5153 (.node 4159 (.node 3697 (.node 3469 (.node 3359 (.node 3313 (.node 3271 (.node 3257 (.node 3253 .empty .empty) (.node 3259 .empty .empty)) (.node 3301 (.node 3299 .empty .empty) (.node 3307 .empty .empty))) (.node 3331 (.node 3323 (.node 3319 .empty .empty) (.node 3329 .empty .empty)) (.node 3347 (.node 3343 .empty .empty) .empty))) (.node 3413 (.node 3389 (.node 3371 (.node 3361 .empty .empty) (.node 3373 .empty .empty)) (.node 3407 (.node 3391 .empty .empty) .empty)) (.node 3461 (.node 3449 (.node 3433 .empty .empty) (.node 3457 .empty .empty)) (.node 3467 (.node 3463 .empty .empty) .empty)))) (.node 3583 (.node 3539 (.node 3517 (.node 3499 (.node 3491 .empty .empty) (.node 3511 .empty .empty)) (.node 3529 (.node 3527 .empty .empty) (.node 3533 .empty .empty))) (.node 3559 (.node 3547 (.node 3541 .empty .empty) (.node 3557 .empty .empty)) (.node 3581 (.node 3571 .empty .empty) .empty))) (.node 3637 (.node 3617 (.node 3607 (.node 3593 .empty .empty) (.node 3613 .empty .empty)) (.node 3631 (.node 3623 .empty .empty) .empty)) (.node 3673 (.node 3659 (.node 3643 .empty .empty) (.node 3671 .empty .empty)) (.node 3691 (.node 3677 .empty .empty) .empty))))) (.node 3929 (.node 3823 (.node 3767 (.node 3727 (.node 3709 (.node 3701 .empty .empty) (.node 3719 .empty .empty)) (.node 3739 (.node 3733 .empty .empty) (.node 3761 .empty .empty))) (.node 3797 (.node 3779 (.node 3769 .empty .empty) (.node 3793 .empty .empty)) (.node 3821 (.node 3803 .empty .empty) .empty))) (.node 3881 (.node 3853 (.node 3847 (.node 3833 .empty .empty) (.node 3851 .empty .empty)) (.node 3877 (.node 3863 .empty .empty) .empty)) (.node 3917 (.node 3907 (.node 3889 .empty .empty) (.node 3911 .empty .empty)) (.node 3923 (.node 3919 .empty .empty) .empty)))) (.node 4051 (.node 4003 (.node 3967 (.node 3943 (.node 3931 .empty .empty) (.node 3947 .empty .empty)) (.node 4001 (.node 3989 .empty .empty) .empty)) (.node 4021 (.node 4013 (.node 4007 .empty .empty) (.node 4019 .empty .empty)) (.node 4049 (.node 4027 .empty .empty) .empty))) (.node 4111 (.node 4091 (.node 4073 (.node 4057 .empty .empty) (.node 4079 .empty .empty)) (.node 4099 (.node 4093 .empty .empty) .empty)) (.node 4139 (.node 4129 (.node 4127 .empty .empty) (.node 4133 .empty .empty)) (.node 4157 (.node 4153 .empty .empty) .empty)))))) (.node 4657 (.node 4423 (.node 4283 (.node 4241 (.node 4217 (.node 4201 (.node 4177 .empty .empty) (.node 4211 .empty .empty)) (.node 4229 (.node 4219 .empty .empty) (.node 4231 .empty .empty))) (.node 4261 (.node 4253 (.node 4243 .empty .empty) (.node 4259 .empty .empty)) (.node 4273 (.node 4271 .empty .empty) .empty))) (.node 4357 (.node 4337 (.node 4297 (.node 4289 .empty .empty) (.node 4327 .empty .empty)) (.node 4349 (.node 4339 .empty .empty) .empty)) (.node 4397 (.node 4373 (.node 4363 .empty .empty) (.node 4391 .empty .empty)) (.node 4421 (.node 4409 .empty .empty) .empty)))) (.node 4547 (.node 4483 (.node 4457 (.node 4447 (.node 4441 .empty .empty) (.node 4451 .empty .empty)) (.node 4481 (.node 4463 .empty .empty) .empty)) (.node 4517 (.node 4507 (.node 4493 .empty .empty) (.node 4513 .empty .empty)) (.node 4523 (.node 4519 .empty .empty) .empty))) (.node 4603 (.node 4583 (.node 4561 (.node 4549 .empty .empty) (.node 4567 .empty .empty)) (.node 4597 (.node 4591 .empty .empty) .empty)) (.node 4643 (.node 4637 (.node 4621 .empty .empty) (.node 4639 .empty .empty)) (.node 4651 (.node 4649 .empty .empty) .empty))))) (.node 4933 (.node 4793 (.node 4729 (.node 4691 (.node 4673 (.node 4663 .empty .empty) (.node 4679 .empty .empty)) (.node 4721 (.node 4703 .empty .empty) (.node 4723 .empty .empty))) (.node 4783 (.node 4751 (.node 4733 .empty .empty) (.node 4759 .empty .empty)) (.node 4789 (.node 4787 .empty .empty) .empty))) (.node 4871 (.node 4817 (.node 4801 (.node 4799 .empty .empty) (.node 4813 .empty .empty)) (.node 4861 (.node 4831 .empty .empty) .empty)) (.node 4909 (.node 4889 (.node 4877 .empty .empty) (.node 4903 .empty .empty)) (.node 4931 (.node 4919 .empty .empty) .empty)))) (.node 5021 (.node 4973 (.node 4957 (.node 4943 (.node 4937 .empty .empty) (.node 4951 .empty .empty)) (.node 4969 (.node 4967 .empty .empty) .empty)) (.node 5003 (.node 4993 (.node 4987 .empty .empty) (.node 4999 .empty .empty)) (.node 5011 (.node 5009 .empty .empty) .empty))) (.node 5087 (.node 5059 (.node 5039 (.node 5023 .empty .empty) (.node 5051 .empty .empty)) (.node 5081 (.node 5077 .empty .empty) .empty)) (.node 5113 (.node 5101 (.node 5099 .empty .empty) (.node 5107 .empty .empty)) (.node 5147 (.node 5119 .empty .empty) .empty))))))) (.node 26801 (.node 8353 (.node 5419 (.node 5297 (.node 5231 (.node 5189 (.node 5171 (.node 5167 .empty .empty) (.node 5179 .empty .empty)) (.node 5209 (.node 5197 .empty .empty) (.node 5227 .empty .empty))) (.node 5273 (.node 5237 (.node 5233 .empty .empty) (.node 5261 .empty .empty)) (.node 5281 (.node 5279 .empty .empty) .empty))) (.node 5381 (.node 5333 (.node 5309 (.node 5303 .empty .empty) (.node 5323 .empty .empty)) (.node 5351 (.node 5347 .empty .empty) .empty)) (.node 5407 (.node 5393 (.node 5387 .empty .empty) (.node 5399 .empty .empty)) (.node 5417 (.node 5413 .empty .empty) .empty)))) (.node 5527 (.node 5479 (.node 5443 (.node 5437 (.node 5431 .empty .empty) (.node 5441 .empty .empty)) (.node 5471 (.node 5449 .empty .empty) (.node 5477 .empty .empty))) (.node 5507 (.node 5501 (.node 5483 .empty .empty) (.node 5503 .empty .empty)) (.node 5521 (.node 5519 .empty .empty) .empty))) (.node 5839 (.node 5569 (.node 5557 (.node 5531 .empty .empty) (.node 5563 .empty .empty)) (.node 5821 (.node 5647 .empty .empty) .empty)) (.node 7151 (.node 6469 (.node 6047 .empty .empty) (.node 6779 .empty .empty)) (.node 7673 (.node 7573 .empty .empty) .empty))))) (.node 17791 (.node 13751 (.node 11383 (.node 9859 (.node 9227 (.node 8647 .empty .empty) (.node 9323 .empty .empty)) (.node 10499 (.node 9931 .empty .empty) (.node 10859 .empty .empty))) (.node 12421 (.node 11867 (.node 11681 .empty .empty) (.node 12203 .empty .empty)) (.node 12527 (.node 12457 .empty .empty) .empty))) (.node 15383 (.node 14423 (.node 14197 (.node 14071 .empty .empty) (.node 14293 .empty .empty)) (.node 15149 (.node 14779 .empty .empty) .empty)) (.node 16381 (.node 15923 (.node 15427 .empty .empty) (.node 16189 .empty .empty)) (.node 17029 (.node 16619 .empty .empty) .empty)))) (.node 21991 (.node 20071 (.node 19379 (.node 18371 (.node 17807 .empty .empty) (.node 18461 .empty .empty)) (.node 19993 (.node 19813 .empty .empty) .empty)) (.node 21647 (.node 20963 (.node 20947 .empty .empty) (.node 21323 .empty .empty)) (.node 21929 (.node 21799 .empty .empty) .empty))) (.node 25583 (.node 23981 (.node 22769 (.node 22279 .empty .empty) (.node 23743 .empty .empty)) (.node 24091 (.node 24077 .empty .empty) .empty)) (.node 26539 (.node 25847 (.node 25771 .empty .empty) (.node 26263 .empty .empty)) (.node 26731 (.node 26693 .empty .empty) .empty)))))) (.node 45841 (.node 36587 (.node 32119 (.node 29209 (.node 27847 (.node 27103 (.node 26993 .empty .empty) (.node 27779 .empty .empty)) (.node 28559 (.node 28099 .empty .empty) (.node 29017 .empty .empty))) (.node 31393 (.node 30253 (.node 29537 .empty .empty) (.node 30593 .empty .empty)) (.node 32051 (.node 31541 .empty .empty) .empty))) (.node 34253 (.node 32831 (.node 32257 (.node 32183 .empty .empty) (.node 32441 .empty .empty)) (.node 34141 (.node 33809 .empty .empty) .empty)) (.node 35311 (.node 34939 (.node 34369 .empty .empty) (.node 35117 .empty .empty)) (.node 35977 (.node 35803 .empty .empty) .empty)))) (.node 40927 (.node 39239 (.node 37811 (.node 36973 (.node 36599 .empty .empty) (.node 37699 .empty .empty)) (.node 39023 (.node 38317 .empty .empty) .empty)) (.node 40129 (.node 39631 (.node 39383 .empty .empty) (.node 39983 .empty .empty)) (.node 40693 (.node 40529 .empty .empty) .empty))) (.node 43271 (.node 42589 (.node 41897 (.node 41641 .empty .empty) (.node 42473 .empty .empty)) (.node 42961 (.node 42701 .empty .empty) .empty)) (.node 44971 (.node 44417 (.node 43669 .empty .empty) (.node 44579 .empty .empty)) (.node 45503 (.node 45289 .empty .empty) .empty))))) (.node 54437 (.node 50129 (.node 48131 (.node 46687 (.node 46183 (.node 45863 .empty .empty) (.node 46663 .empty .empty)) (.node 47717 (.node 47491 .empty .empty) (.node 47969 .empty .empty))) (.node 48847 (.node 48731 (.node 48571 .empty .empty) (.node 48761 .empty .empty)) (.node 49757 (.node 49279 .empty .empty) .empty))) (.node 53149 (.node 51503 (.node 50767 (.node 50599 .empty .empty) (.node 51137 .empty .empty)) (.node 52957 (.node 51949 .empty .empty) .empty)) (.node 54163 (.node 53623 (.node 53231 .empty .empty) (.node 54101 .empty .empty)) (.node 54421 (.node 54293 .empty .empty) .empty)))) (.node 59743 (.node 56401 (.node 55631 (.node 54713 (.node 54443 .empty .empty) (.node 55487 .empty .empty)) (.node 56041 (.node 55819 .empty .empty) .empty)) (.node 59009 (.node 58477 (.node 56909 .empty .empty) (.node 58789 .empty .empty)) (.node 59333 (.node 59263 .empty .empty) .empty))) (.node 60497 (.node 60161 (.node 59929 (.node 59921 .empty .empty) (.node 59957 .empty .empty)) (.node 60443 (.node 60169 .empty .empty) .empty)) (.node 61291 (.node 60901 (.node 60689 .empty .empty) (.node 61057 .empty .empty)) (.node 64877 (.node 61507 .empty .empty) .empty)))))))))
def left : List ℕ := [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557,2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843,2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939,2953,2957,2963,2969,2971,2999,3001,3011,3019,3023,3037,3041,3049,3061,3067,3079,3083,3089,3109,3119,3121,3137,3163,3167,3169,3181,3187,3191,3203,3209,3217,3221,3229,3251,3253,3257,3259,3271,3299,3301,3307,3313,3319,3323,3329,3331,3343,3347,3359,3361,3371,3373,3389,3391,3407,3413,3433,3449,3457,3461,3463,3467,3469,3491,3499,3511,3517,3527,3529,3533,3539,3541,3547,3557,3559,3571,3581,3583,3593,3607,3613,3617,3623,3631,3637,3643,3659,3671,3673,3677,3691,3697,3701,3709,3719,3727,3733,3739,3761,3767,3769,3779,3793,3797,3803,3821,3823,3833,3847,3851,3853,3863,3877,3881,3889,3907,3911,3917,3919,3923,3929,3931,3943,3947,3967,3989,4001,4003,4007,4013,4019,4021,4027,4049,4051,4057,4073,4079,4091,4093,4099,4111,4127,4129,4133,4139,4153,4157,4159,4177,4201,4211,4217,4219,4229,4231,4241,4243,4253,4259,4261,4271,4273,4283,4289,4297,4327,4337,4339,4349,4357,4363,4373,4391,4397,4409,4421,4423,4441,4447,4451,4457,4463,4481,4483,4493,4507,4513,4517,4519,4523,4547,4549,4561,4567,4583,4591,4597,4603,4621,4637,4639,4643,4649,4651,4657,4663,4673,4679,4691,4703,4721,4723,4729,4733,4751,4759,4783,4787,4789,4793,4799,4801,4813,4817,4831,4861,4871,4877,4889,4903,4909,4919,4931,4933,4937,4943,4951,4957,4967,4969,4973,4987,4993,4999,5003,5009,5011,5021,5023,5039,5051,5059,5077,5081,5087,5099,5101,5107,5113,5119,5147,5153,5167,5171,5179,5189,5197,5209,5227,5231,5233,5237,5261,5273,5279,5281,5297,5303,5309,5323,5333,5347,5351,5381,5387,5393,5399,5407,5413,5417,5419,5431,5437,5441,5443,5449,5471,5477,5479,5483,5501,5503,5507,5519,5521,5527,5531,5557,5563,5569]

lemma primes_valid : primes.check = true := by
  simp (config := { maxSteps := 1000000 }) only
    [primes, PrimeTree.check, Bool.and_eq_true, GoldbachCertificate.primeCheck_spec]
  norm_num

lemma left_valid : leftCheck 5569 primes left = true := by decide +kernel
lemma coverage_valid : covers 0 3 32766 primes left = true := by decide +kernel

end GoldbachBitmapData4_65536_greedy

theorem solution (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 65536)
    (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ 5569 ∧ n = p + q := by
  by_cases hn : n = 4
  · subst n
    exact ⟨2, 2, by decide, by decide, by decide, rfl⟩
  · exact GoldbachBitmapCertificate.block_sound 0 3 32766 5569
      GoldbachBitmapData4_65536_greedy.primes GoldbachBitmapData4_65536_greedy.left GoldbachBitmapData4_65536_greedy.primes_valid
      GoldbachBitmapData4_65536_greedy.left_valid GoldbachBitmapData4_65536_greedy.coverage_valid n (by obtain ⟨k, hk⟩ := he; omega)
      (by omega) he

#print axioms solution
