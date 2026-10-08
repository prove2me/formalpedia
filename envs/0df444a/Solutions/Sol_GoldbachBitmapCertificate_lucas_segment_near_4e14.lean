-- Prove2me | solution 1 for GoldbachBitmapCertificate.lucas_segment_near_4e14
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T01:02:32.031219+00:00
-- url     : https://prove2.me/submissions/1ce224e6-ec23-4a36-80c9-c109c914083b

import Definitions.Def_GoldbachBitmapCertificate
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.BigOperators.Group.List.Defs

set_option autoImplicit false


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


namespace GoldbachPrimalityCertificate

private lemma prime_mem_of_dvd_prod (factors : List ℕ)
    (hp : ∀ r ∈ factors, Nat.Prime r) (q : ℕ) (hq : Nat.Prime q)
    (hd : q ∣ factors.prod) : q ∈ factors := by
  induction factors with
  | nil =>
    simp only [List.prod_nil] at hd
    exact (hq.not_dvd_one hd).elim
  | cons r rs ih =>
    simp only [List.prod_cons] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have hr := hp r (by simp)
      have heq : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp hd
      simp [heq]
    · exact List.mem_cons_of_mem r (ih (fun s hs => hp s (List.mem_cons_of_mem r hs)) hd)

end GoldbachPrimalityCertificate

private lemma lucas_from_prime_list (p : ℕ) (a : ZMod p) (factors : List ℕ)
    (hp : ∀ r ∈ factors, Nat.Prime r) (hprod : factors.prod = p - 1)
    (ha : a ^ (p - 1) = 1)
    (hd : ∀ r ∈ factors, a ^ ((p - 1) / r) ≠ 1) : Nat.Prime p := by
  apply lucas_primality p a ha
  intro q hq hqd
  have hmem : q ∈ factors := GoldbachPrimalityCertificate.prime_mem_of_dvd_prod factors hp q hq
    (by rwa [hprod])
  exact hd q hmem

namespace GoldbachLucasSegmentPrimes
private lemma prime_2 : Nat.Prime 2 := Nat.prime_two

private lemma prime_3 : Nat.Prime 3 := by
  apply lucas_from_prime_list 3 (2 : ZMod 3) [2]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · exact prime_2
  · decide +kernel
  · change (2 : ZMod 3) ^ 2 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · change (2 : ZMod 3) ^ 1 ≠ 1
      reduce_mod_char
      decide

private lemma prime_5 : Nat.Prime 5 := by
  apply lucas_from_prime_list 5 (2 : ZMod 5) [2,2]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_2
  · decide +kernel
  · change (2 : ZMod 5) ^ 4 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 5) ^ 2 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 5) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_7 : Nat.Prime 7 := by
  apply lucas_from_prime_list 7 (3 : ZMod 7) [2,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_3
  · decide +kernel
  · change (3 : ZMod 7) ^ 6 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (3 : ZMod 7) ^ 3 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 7) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_11 : Nat.Prime 11 := by
  apply lucas_from_prime_list 11 (2 : ZMod 11) [2,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_5
  · decide +kernel
  · change (2 : ZMod 11) ^ 10 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 11) ^ 5 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 11) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_13 : Nat.Prime 13 := by
  apply lucas_from_prime_list 13 (2 : ZMod 13) [2,2,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
  · decide +kernel
  · change (2 : ZMod 13) ^ 12 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 13) ^ 6 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 13) ^ 6 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 13) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_17 : Nat.Prime 17 := by
  apply lucas_from_prime_list 17 (3 : ZMod 17) [2,2,2,2]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
  · decide +kernel
  · change (3 : ZMod 17) ^ 16 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17) ^ 8 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 17) ^ 8 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 17) ^ 8 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 17) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_19 : Nat.Prime 19 := by
  apply lucas_from_prime_list 19 (2 : ZMod 19) [2,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (2 : ZMod 19) ^ 18 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 19) ^ 9 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 19) ^ 6 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 19) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_23 : Nat.Prime 23 := by
  apply lucas_from_prime_list 23 (5 : ZMod 23) [2,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_11
  · decide +kernel
  · change (5 : ZMod 23) ^ 22 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 23) ^ 11 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 23) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_29 : Nat.Prime 29 := by
  apply lucas_from_prime_list 29 (2 : ZMod 29) [2,2,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
  · decide +kernel
  · change (2 : ZMod 29) ^ 28 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 29) ^ 14 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 29) ^ 14 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 29) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_31 : Nat.Prime 31 := by
  apply lucas_from_prime_list 31 (3 : ZMod 31) [2,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (3 : ZMod 31) ^ 30 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 31) ^ 15 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 31) ^ 10 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 31) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_37 : Nat.Prime 37 := by
  apply lucas_from_prime_list 37 (2 : ZMod 37) [2,2,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (2 : ZMod 37) ^ 36 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37) ^ 18 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 37) ^ 18 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 37) ^ 12 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 37) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_41 : Nat.Prime 41 := by
  apply lucas_from_prime_list 41 (6 : ZMod 41) [2,2,2,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
  · decide +kernel
  · change (6 : ZMod 41) ^ 40 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 41) ^ 20 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 41) ^ 20 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 41) ^ 20 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 41) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_43 : Nat.Prime 43 := by
  apply lucas_from_prime_list 43 (3 : ZMod 43) [2,3,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel
  · change (3 : ZMod 43) ^ 42 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 43) ^ 21 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 43) ^ 14 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 43) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_47 : Nat.Prime 47 := by
  apply lucas_from_prime_list 47 (5 : ZMod 47) [2,23]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_23
  · decide +kernel
  · change (5 : ZMod 47) ^ 46 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 47) ^ 23 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 47) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_53 : Nat.Prime 53 := by
  apply lucas_from_prime_list 53 (2 : ZMod 53) [2,2,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_13
  · decide +kernel
  · change (2 : ZMod 53) ^ 52 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 53) ^ 26 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 53) ^ 26 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 53) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_59 : Nat.Prime 59 := by
  apply lucas_from_prime_list 59 (2 : ZMod 59) [2,29]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_29
  · decide +kernel
  · change (2 : ZMod 59) ^ 58 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 59) ^ 29 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 59) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_61 : Nat.Prime 61 := by
  apply lucas_from_prime_list 61 (2 : ZMod 61) [2,2,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (2 : ZMod 61) ^ 60 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61) ^ 30 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 61) ^ 30 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 61) ^ 20 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 61) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_67 : Nat.Prime 67 := by
  apply lucas_from_prime_list 67 (2 : ZMod 67) [2,3,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
  · decide +kernel
  · change (2 : ZMod 67) ^ 66 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 67) ^ 33 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 67) ^ 22 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 67) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_71 : Nat.Prime 71 := by
  apply lucas_from_prime_list 71 (7 : ZMod 71) [2,5,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel
  · change (7 : ZMod 71) ^ 70 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 71) ^ 35 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 71) ^ 14 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 71) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_73 : Nat.Prime 73 := by
  apply lucas_from_prime_list 73 (5 : ZMod 73) [2,2,2,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (5 : ZMod 73) ^ 72 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 73) ^ 36 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 73) ^ 36 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 73) ^ 36 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 73) ^ 24 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 73) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_79 : Nat.Prime 79 := by
  apply lucas_from_prime_list 79 (3 : ZMod 79) [2,3,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel
  · change (3 : ZMod 79) ^ 78 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 79) ^ 39 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 79) ^ 26 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 79) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_83 : Nat.Prime 83 := by
  apply lucas_from_prime_list 83 (2 : ZMod 83) [2,41]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_41
  · decide +kernel
  · change (2 : ZMod 83) ^ 82 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 83) ^ 41 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 83) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_89 : Nat.Prime 89 := by
  apply lucas_from_prime_list 89 (3 : ZMod 89) [2,2,2,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_11
  · decide +kernel
  · change (3 : ZMod 89) ^ 88 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 89) ^ 44 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 89) ^ 44 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 89) ^ 44 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 89) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_97 : Nat.Prime 97 := by
  apply lucas_from_prime_list 97 (5 : ZMod 97) [2,2,2,2,2,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
  · decide +kernel
  · change (5 : ZMod 97) ^ 96 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97) ^ 48 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 97) ^ 48 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 97) ^ 48 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 97) ^ 48 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 97) ^ 48 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 97) ^ 32 ≠ 1
      reduce_mod_char
      decide

private lemma prime_101 : Nat.Prime 101 := by
  apply lucas_from_prime_list 101 (2 : ZMod 101) [2,2,5,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_5
  · decide +kernel
  · change (2 : ZMod 101) ^ 100 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 101) ^ 50 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 101) ^ 50 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 101) ^ 20 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 101) ^ 20 ≠ 1
      reduce_mod_char
      decide

private lemma prime_103 : Nat.Prime 103 := by
  apply lucas_from_prime_list 103 (5 : ZMod 103) [2,3,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel
  · change (5 : ZMod 103) ^ 102 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (5 : ZMod 103) ^ 51 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 103) ^ 34 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 103) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_107 : Nat.Prime 107 := by
  apply lucas_from_prime_list 107 (2 : ZMod 107) [2,53]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_53
  · decide +kernel
  · change (2 : ZMod 107) ^ 106 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 107) ^ 53 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 107) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_109 : Nat.Prime 109 := by
  apply lucas_from_prime_list 109 (6 : ZMod 109) [2,2,3,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (6 : ZMod 109) ^ 108 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 109) ^ 54 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 109) ^ 54 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 109) ^ 36 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 109) ^ 36 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 109) ^ 36 ≠ 1
      reduce_mod_char
      decide

private lemma prime_113 : Nat.Prime 113 := by
  apply lucas_from_prime_list 113 (3 : ZMod 113) [2,2,2,2,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_7
  · decide +kernel
  · change (3 : ZMod 113) ^ 112 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 113) ^ 56 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 113) ^ 56 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 113) ^ 56 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 113) ^ 56 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 113) ^ 16 ≠ 1
      reduce_mod_char
      decide

private lemma prime_127 : Nat.Prime 127 := by
  apply lucas_from_prime_list 127 (3 : ZMod 127) [2,3,3,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_7
  · decide +kernel
  · change (3 : ZMod 127) ^ 126 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 127) ^ 63 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 127) ^ 42 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 127) ^ 42 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 127) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_131 : Nat.Prime 131 := by
  apply lucas_from_prime_list 131 (2 : ZMod 131) [2,5,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel
  · change (2 : ZMod 131) ^ 130 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 131) ^ 65 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 131) ^ 26 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 131) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_137 : Nat.Prime 137 := by
  apply lucas_from_prime_list 137 (3 : ZMod 137) [2,2,2,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_17
  · decide +kernel
  · change (3 : ZMod 137) ^ 136 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 137) ^ 68 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 137) ^ 68 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 137) ^ 68 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 137) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_139 : Nat.Prime 139 := by
  apply lucas_from_prime_list 139 (2 : ZMod 139) [2,3,23]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel
  · change (2 : ZMod 139) ^ 138 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 139) ^ 69 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 139) ^ 46 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 139) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_149 : Nat.Prime 149 := by
  apply lucas_from_prime_list 149 (2 : ZMod 149) [2,2,37]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_37
  · decide +kernel
  · change (2 : ZMod 149) ^ 148 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 149) ^ 74 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 149) ^ 74 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 149) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_151 : Nat.Prime 151 := by
  apply lucas_from_prime_list 151 (6 : ZMod 151) [2,3,5,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5
  · decide +kernel
  · change (6 : ZMod 151) ^ 150 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 151) ^ 75 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 151) ^ 50 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 151) ^ 30 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 151) ^ 30 ≠ 1
      reduce_mod_char
      decide

private lemma prime_157 : Nat.Prime 157 := by
  apply lucas_from_prime_list 157 (5 : ZMod 157) [2,2,3,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_13
  · decide +kernel
  · change (5 : ZMod 157) ^ 156 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 157) ^ 78 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 157) ^ 78 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 157) ^ 52 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 157) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_163 : Nat.Prime 163 := by
  apply lucas_from_prime_list 163 (2 : ZMod 163) [2,3,3,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (2 : ZMod 163) ^ 162 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 163) ^ 81 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 163) ^ 54 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 163) ^ 54 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 163) ^ 54 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 163) ^ 54 ≠ 1
      reduce_mod_char
      decide

private lemma prime_167 : Nat.Prime 167 := by
  apply lucas_from_prime_list 167 (5 : ZMod 167) [2,83]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_83
  · decide +kernel
  · change (5 : ZMod 167) ^ 166 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 167) ^ 83 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 167) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_173 : Nat.Prime 173 := by
  apply lucas_from_prime_list 173 (2 : ZMod 173) [2,2,43]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_43
  · decide +kernel
  · change (2 : ZMod 173) ^ 172 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 173) ^ 86 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 173) ^ 86 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 173) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_179 : Nat.Prime 179 := by
  apply lucas_from_prime_list 179 (2 : ZMod 179) [2,89]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_89
  · decide +kernel
  · change (2 : ZMod 179) ^ 178 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 179) ^ 89 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 179) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_181 : Nat.Prime 181 := by
  apply lucas_from_prime_list 181 (2 : ZMod 181) [2,2,3,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (2 : ZMod 181) ^ 180 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 181) ^ 90 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 181) ^ 90 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 181) ^ 60 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 181) ^ 60 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 181) ^ 36 ≠ 1
      reduce_mod_char
      decide

private lemma prime_191 : Nat.Prime 191 := by
  apply lucas_from_prime_list 191 (19 : ZMod 191) [2,5,19]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · decide +kernel
  · change (19 : ZMod 191) ^ 190 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (19 : ZMod 191) ^ 95 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 191) ^ 38 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 191) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_193 : Nat.Prime 193 := by
  apply lucas_from_prime_list 193 (5 : ZMod 193) [2,2,2,2,2,2,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
  · decide +kernel
  · change (5 : ZMod 193) ^ 192 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 193) ^ 96 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 193) ^ 96 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 193) ^ 96 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 193) ^ 96 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 193) ^ 96 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 193) ^ 96 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 193) ^ 64 ≠ 1
      reduce_mod_char
      decide

private lemma prime_197 : Nat.Prime 197 := by
  apply lucas_from_prime_list 197 (2 : ZMod 197) [2,2,7,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_7
  · decide +kernel
  · change (2 : ZMod 197) ^ 196 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 197) ^ 98 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 197) ^ 98 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 197) ^ 28 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 197) ^ 28 ≠ 1
      reduce_mod_char
      decide

private lemma prime_199 : Nat.Prime 199 := by
  apply lucas_from_prime_list 199 (3 : ZMod 199) [2,3,3,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_11
  · decide +kernel
  · change (3 : ZMod 199) ^ 198 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 199) ^ 99 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 199) ^ 66 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 199) ^ 66 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 199) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_211 : Nat.Prime 211 := by
  apply lucas_from_prime_list 211 (2 : ZMod 211) [2,3,5,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
  · decide +kernel
  · change (2 : ZMod 211) ^ 210 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 211) ^ 105 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 211) ^ 70 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 211) ^ 42 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 211) ^ 30 ≠ 1
      reduce_mod_char
      decide

private lemma prime_223 : Nat.Prime 223 := by
  apply lucas_from_prime_list 223 (3 : ZMod 223) [2,3,37]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_37
  · decide +kernel
  · change (3 : ZMod 223) ^ 222 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 223) ^ 111 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 223) ^ 74 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 223) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_227 : Nat.Prime 227 := by
  apply lucas_from_prime_list 227 (2 : ZMod 227) [2,113]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_113
  · decide +kernel
  · change (2 : ZMod 227) ^ 226 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 227) ^ 113 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 227) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_229 : Nat.Prime 229 := by
  apply lucas_from_prime_list 229 (6 : ZMod 229) [2,2,3,19]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_19
  · decide +kernel
  · change (6 : ZMod 229) ^ 228 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 229) ^ 114 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 229) ^ 114 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 229) ^ 76 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 229) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_233 : Nat.Prime 233 := by
  apply lucas_from_prime_list 233 (3 : ZMod 233) [2,2,2,29]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_29
  · decide +kernel
  · change (3 : ZMod 233) ^ 232 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 233) ^ 116 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 233) ^ 116 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 233) ^ 116 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 233) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_239 : Nat.Prime 239 := by
  apply lucas_from_prime_list 239 (7 : ZMod 239) [2,7,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_17
  · decide +kernel
  · change (7 : ZMod 239) ^ 238 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 239) ^ 119 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 239) ^ 34 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 239) ^ 14 ≠ 1
      reduce_mod_char
      decide

private lemma prime_241 : Nat.Prime 241 := by
  apply lucas_from_prime_list 241 (7 : ZMod 241) [2,2,2,2,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (7 : ZMod 241) ^ 240 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 241) ^ 120 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 241) ^ 120 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 241) ^ 120 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 241) ^ 120 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 241) ^ 80 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 241) ^ 48 ≠ 1
      reduce_mod_char
      decide

private lemma prime_251 : Nat.Prime 251 := by
  apply lucas_from_prime_list 251 (6 : ZMod 251) [2,5,5,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_5
  · decide +kernel
  · change (6 : ZMod 251) ^ 250 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 251) ^ 125 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 251) ^ 50 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 251) ^ 50 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 251) ^ 50 ≠ 1
      reduce_mod_char
      decide

private lemma prime_257 : Nat.Prime 257 := by
  apply lucas_from_prime_list 257 (3 : ZMod 257) [2,2,2,2,2,2,2,2]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
  · decide +kernel
  · change (3 : ZMod 257) ^ 256 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 257) ^ 128 ≠ 1
      reduce_mod_char
      decide

private lemma prime_263 : Nat.Prime 263 := by
  apply lucas_from_prime_list 263 (5 : ZMod 263) [2,131]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_131
  · decide +kernel
  · change (5 : ZMod 263) ^ 262 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 263) ^ 131 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 263) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_269 : Nat.Prime 269 := by
  apply lucas_from_prime_list 269 (2 : ZMod 269) [2,2,67]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_67
  · decide +kernel
  · change (2 : ZMod 269) ^ 268 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 269) ^ 134 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 269) ^ 134 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 269) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_271 : Nat.Prime 271 := by
  apply lucas_from_prime_list 271 (6 : ZMod 271) [2,3,3,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (6 : ZMod 271) ^ 270 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 271) ^ 135 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 271) ^ 90 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 271) ^ 90 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 271) ^ 90 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 271) ^ 54 ≠ 1
      reduce_mod_char
      decide

private lemma prime_277 : Nat.Prime 277 := by
  apply lucas_from_prime_list 277 (5 : ZMod 277) [2,2,3,23]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_23
  · decide +kernel
  · change (5 : ZMod 277) ^ 276 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 277) ^ 138 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 277) ^ 138 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 277) ^ 92 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 277) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_281 : Nat.Prime 281 := by
  apply lucas_from_prime_list 281 (3 : ZMod 281) [2,2,2,5,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_7
  · decide +kernel
  · change (3 : ZMod 281) ^ 280 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 281) ^ 140 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 281) ^ 140 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 281) ^ 140 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 281) ^ 56 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 281) ^ 40 ≠ 1
      reduce_mod_char
      decide

private lemma prime_283 : Nat.Prime 283 := by
  apply lucas_from_prime_list 283 (3 : ZMod 283) [2,3,47]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_47
  · decide +kernel
  · change (3 : ZMod 283) ^ 282 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 283) ^ 141 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 283) ^ 94 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 283) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_293 : Nat.Prime 293 := by
  apply lucas_from_prime_list 293 (2 : ZMod 293) [2,2,73]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_73
  · decide +kernel
  · change (2 : ZMod 293) ^ 292 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 293) ^ 146 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 293) ^ 146 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 293) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_307 : Nat.Prime 307 := by
  apply lucas_from_prime_list 307 (5 : ZMod 307) [2,3,3,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_17
  · decide +kernel
  · change (5 : ZMod 307) ^ 306 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 307) ^ 153 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 307) ^ 102 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 307) ^ 102 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 307) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_311 : Nat.Prime 311 := by
  apply lucas_from_prime_list 311 (17 : ZMod 311) [2,5,31]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_31
  · decide +kernel
  · change (17 : ZMod 311) ^ 310 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (17 : ZMod 311) ^ 155 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 311) ^ 62 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 311) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_317 : Nat.Prime 317 := by
  apply lucas_from_prime_list 317 (2 : ZMod 317) [2,2,79]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_79
  · decide +kernel
  · change (2 : ZMod 317) ^ 316 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 317) ^ 158 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 317) ^ 158 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 317) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_347 : Nat.Prime 347 := by
  apply lucas_from_prime_list 347 (2 : ZMod 347) [2,173]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_173
  · decide +kernel
  · change (2 : ZMod 347) ^ 346 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 347) ^ 173 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 347) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_349 : Nat.Prime 349 := by
  apply lucas_from_prime_list 349 (2 : ZMod 349) [2,2,3,29]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_29
  · decide +kernel
  · change (2 : ZMod 349) ^ 348 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 349) ^ 174 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 349) ^ 174 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 349) ^ 116 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 349) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_359 : Nat.Prime 359 := by
  apply lucas_from_prime_list 359 (7 : ZMod 359) [2,179]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_179
  · decide +kernel
  · change (7 : ZMod 359) ^ 358 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (7 : ZMod 359) ^ 179 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 359) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_401 : Nat.Prime 401 := by
  apply lucas_from_prime_list 401 (3 : ZMod 401) [2,2,2,2,5,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_5
  · decide +kernel
  · change (3 : ZMod 401) ^ 400 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 401) ^ 200 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 401) ^ 200 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 401) ^ 200 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 401) ^ 200 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 401) ^ 80 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 401) ^ 80 ≠ 1
      reduce_mod_char
      decide

private lemma prime_409 : Nat.Prime 409 := by
  apply lucas_from_prime_list 409 (21 : ZMod 409) [2,2,2,3,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_17
  · decide +kernel
  · change (21 : ZMod 409) ^ 408 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 409) ^ 204 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 409) ^ 204 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 409) ^ 204 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 409) ^ 136 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 409) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_503 : Nat.Prime 503 := by
  apply lucas_from_prime_list 503 (5 : ZMod 503) [2,251]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_251
  · decide +kernel
  · change (5 : ZMod 503) ^ 502 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 503) ^ 251 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 503) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_521 : Nat.Prime 521 := by
  apply lucas_from_prime_list 521 (3 : ZMod 521) [2,2,2,5,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · decide +kernel
  · change (3 : ZMod 521) ^ 520 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 521) ^ 260 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 521) ^ 260 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 521) ^ 260 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 521) ^ 104 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 521) ^ 40 ≠ 1
      reduce_mod_char
      decide

private lemma prime_523 : Nat.Prime 523 := by
  apply lucas_from_prime_list 523 (2 : ZMod 523) [2,3,3,29]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_29
  · decide +kernel
  · change (2 : ZMod 523) ^ 522 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 523) ^ 261 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 523) ^ 174 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 523) ^ 174 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 523) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_541 : Nat.Prime 541 := by
  apply lucas_from_prime_list 541 (2 : ZMod 541) [2,2,3,3,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (2 : ZMod 541) ^ 540 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 541) ^ 270 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 541) ^ 270 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 541) ^ 180 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 541) ^ 180 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 541) ^ 180 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 541) ^ 108 ≠ 1
      reduce_mod_char
      decide

private lemma prime_557 : Nat.Prime 557 := by
  apply lucas_from_prime_list 557 (2 : ZMod 557) [2,2,139]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_139
  · decide +kernel
  · change (2 : ZMod 557) ^ 556 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 557) ^ 278 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 557) ^ 278 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 557) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_811 : Nat.Prime 811 := by
  apply lucas_from_prime_list 811 (3 : ZMod 811) [2,3,3,3,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (3 : ZMod 811) ^ 810 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 811) ^ 405 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 811) ^ 270 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 811) ^ 270 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 811) ^ 270 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 811) ^ 270 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 811) ^ 162 ≠ 1
      reduce_mod_char
      decide

private lemma prime_827 : Nat.Prime 827 := by
  apply lucas_from_prime_list 827 (2 : ZMod 827) [2,7,59]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_59
  · decide +kernel
  · change (2 : ZMod 827) ^ 826 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 827) ^ 413 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 827) ^ 118 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 827) ^ 14 ≠ 1
      reduce_mod_char
      decide

private lemma prime_9491 : Nat.Prime 9491 := by
  apply lucas_from_prime_list 9491 (2 : ZMod 9491) [2,5,13,73]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
    · exact prime_73
  · decide +kernel
  · change (2 : ZMod 9491) ^ 9490 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9491) ^ 4745 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 9491) ^ 1898 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 9491) ^ 730 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 9491) ^ 130 ≠ 1
      reduce_mod_char
      decide

private lemma prime_41809 : Nat.Prime 41809 := by
  apply lucas_from_prime_list 41809 (21 : ZMod 41809) [2,2,2,2,3,13,67]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_67
  · decide +kernel
  · change (21 : ZMod 41809) ^ 41808 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 41809) ^ 20904 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 41809) ^ 20904 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 41809) ^ 20904 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 41809) ^ 20904 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 41809) ^ 13936 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 41809) ^ 3216 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 41809) ^ 624 ≠ 1
      reduce_mod_char
      decide

private lemma prime_919799 : Nat.Prime 919799 := by
  apply lucas_from_prime_list 919799 (11 : ZMod 919799) [2,11,41809]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_41809
  · decide +kernel
  · change (11 : ZMod 919799) ^ 919798 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (11 : ZMod 919799) ^ 459899 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 919799) ^ 83618 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 919799) ^ 22 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999998381 : Nat.Prime 399999999998381 := by
  apply lucas_from_prime_list 399999999998381 (3 : ZMod 399999999998381) [2,2,5,29,79,9491,919799]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_79
    · exact prime_9491
    · exact prime_919799
  · decide +kernel
  · change (3 : ZMod 399999999998381) ^ 399999999998380 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 399999999998381) ^ 199999999999190 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999998381) ^ 199999999999190 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999998381) ^ 79999999999676 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999998381) ^ 13793103448220 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999998381) ^ 5063291139220 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999998381) ^ 42145190180 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999998381) ^ 434877620 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1451 : Nat.Prime 1451 := by
  apply lucas_from_prime_list 1451 (2 : ZMod 1451) [2,5,5,29]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_29
  · decide +kernel
  · change (2 : ZMod 1451) ^ 1450 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1451) ^ 725 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1451) ^ 290 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1451) ^ 290 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1451) ^ 50 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2903 : Nat.Prime 2903 := by
  apply lucas_from_prime_list 2903 (5 : ZMod 2903) [2,1451]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_1451
  · decide +kernel
  · change (5 : ZMod 2903) ^ 2902 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 2903) ^ 1451 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 2903) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_75479 : Nat.Prime 75479 := by
  apply lucas_from_prime_list 75479 (19 : ZMod 75479) [2,13,2903]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_2903
  · decide +kernel
  · change (19 : ZMod 75479) ^ 75478 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (19 : ZMod 75479) ^ 37739 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 75479) ^ 5806 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 75479) ^ 26 ≠ 1
      reduce_mod_char
      decide

private lemma prime_13567 : Nat.Prime 13567 := by
  apply lucas_from_prime_list 13567 (3 : ZMod 13567) [2,3,7,17,19]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_17
    · exact prime_19
  · decide +kernel
  · change (3 : ZMod 13567) ^ 13566 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13567) ^ 6783 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 13567) ^ 4522 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 13567) ^ 1938 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 13567) ^ 798 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 13567) ^ 714 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2048047187 : Nat.Prime 2048047187 := by
  apply lucas_from_prime_list 2048047187 (2 : ZMod 2048047187) [2,13567,75479]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13567
    · exact prime_75479
  · decide +kernel
  · change (2 : ZMod 2048047187) ^ 2048047186 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 2048047187) ^ 1024023593 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2048047187) ^ 150958 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2048047187) ^ 27134 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999998597 : Nat.Prime 399999999998597 := by
  apply lucas_from_prime_list 399999999998597 (2 : ZMod 399999999998597) [2,2,157,311,2048047187]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_157
    · exact prime_311
    · exact prime_2048047187
  · decide +kernel
  · change (2 : ZMod 399999999998597) ^ 399999999998596 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 399999999998597) ^ 199999999999298 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999998597) ^ 199999999999298 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999998597) ^ 2547770700628 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999998597) ^ 1286173633436 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999998597) ^ 195308 ≠ 1
      reduce_mod_char
      decide

private lemma prime_58601 : Nat.Prime 58601 := by
  apply lucas_from_prime_list 58601 (3 : ZMod 58601) [2,2,2,5,5,293]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_293
  · decide +kernel
  · change (3 : ZMod 58601) ^ 58600 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 58601) ^ 29300 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 58601) ^ 29300 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 58601) ^ 29300 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 58601) ^ 11720 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 58601) ^ 11720 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 58601) ^ 200 ≠ 1
      reduce_mod_char
      decide

private lemma prime_184944757 : Nat.Prime 184944757 := by
  apply lucas_from_prime_list 184944757 (2 : ZMod 184944757) [2,2,3,263,58601]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_263
    · exact prime_58601
  · decide +kernel
  · change (2 : ZMod 184944757) ^ 184944756 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 184944757) ^ 92472378 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 184944757) ^ 92472378 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 184944757) ^ 61648252 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 184944757) ^ 703212 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 184944757) ^ 3156 ≠ 1
      reduce_mod_char
      decide

private lemma prime_358422939067 : Nat.Prime 358422939067 := by
  apply lucas_from_prime_list 358422939067 (5 : ZMod 358422939067) [2,3,17,19,184944757]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_19
    · exact prime_184944757
  · decide +kernel
  · change (5 : ZMod 358422939067) ^ 358422939066 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 358422939067) ^ 179211469533 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 358422939067) ^ 119474313022 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 358422939067) ^ 21083702298 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 358422939067) ^ 18864365214 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 358422939067) ^ 1938 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999998773 : Nat.Prime 399999999998773 := by
  apply lucas_from_prime_list 399999999998773 (5 : ZMod 399999999998773) [2,2,3,3,31,358422939067]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_31
    · exact prime_358422939067
  · decide +kernel
  · change (5 : ZMod 399999999998773) ^ 399999999998772 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 399999999998773) ^ 199999999999386 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999998773) ^ 199999999999386 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999998773) ^ 133333333332924 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999998773) ^ 133333333332924 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999998773) ^ 12903225806412 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999998773) ^ 1116 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1511 : Nat.Prime 1511 := by
  apply lucas_from_prime_list 1511 (11 : ZMod 1511) [2,5,151]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_151
  · decide +kernel
  · change (11 : ZMod 1511) ^ 1510 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (11 : ZMod 1511) ^ 755 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 1511) ^ 302 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 1511) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_9067 : Nat.Prime 9067 := by
  apply lucas_from_prime_list 9067 (3 : ZMod 9067) [2,3,1511]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_1511
  · decide +kernel
  · change (3 : ZMod 9067) ^ 9066 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 9067) ^ 4533 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 9067) ^ 3022 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 9067) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_677 : Nat.Prime 677 := by
  apply lucas_from_prime_list 677 (2 : ZMod 677) [2,2,13,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_13
    · exact prime_13
  · decide +kernel
  · change (2 : ZMod 677) ^ 676 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 677) ^ 338 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 677) ^ 338 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 677) ^ 52 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 677) ^ 52 ≠ 1
      reduce_mod_char
      decide

private lemma prime_9479 : Nat.Prime 9479 := by
  apply lucas_from_prime_list 9479 (7 : ZMod 9479) [2,7,677]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_677
  · decide +kernel
  · change (7 : ZMod 9479) ^ 9478 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 9479) ^ 4739 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 9479) ^ 1354 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 9479) ^ 14 ≠ 1
      reduce_mod_char
      decide

private lemma prime_57442741 : Nat.Prime 57442741 := by
  apply lucas_from_prime_list 57442741 (2 : ZMod 57442741) [2,2,3,5,101,9479]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_101
    · exact prime_9479
  · decide +kernel
  · change (2 : ZMod 57442741) ^ 57442740 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57442741) ^ 28721370 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 57442741) ^ 28721370 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 57442741) ^ 19147580 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 57442741) ^ 11488548 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 57442741) ^ 568740 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 57442741) ^ 6060 ≠ 1
      reduce_mod_char
      decide

private lemma prime_919083857 : Nat.Prime 919083857 := by
  apply lucas_from_prime_list 919083857 (3 : ZMod 919083857) [2,2,2,2,57442741]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_57442741
  · decide +kernel
  · change (3 : ZMod 919083857) ^ 919083856 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 919083857) ^ 459541928 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 919083857) ^ 459541928 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 919083857) ^ 459541928 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 919083857) ^ 459541928 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 919083857) ^ 16 ≠ 1
      reduce_mod_char
      decide

private lemma prime_5514503143 : Nat.Prime 5514503143 := by
  apply lucas_from_prime_list 5514503143 (3 : ZMod 5514503143) [2,3,919083857]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_919083857
  · decide +kernel
  · change (3 : ZMod 5514503143) ^ 5514503142 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 5514503143) ^ 2757251571 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5514503143) ^ 1838167714 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5514503143) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_22058012573 : Nat.Prime 22058012573 := by
  apply lucas_from_prime_list 22058012573 (2 : ZMod 22058012573) [2,2,5514503143]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5514503143
  · decide +kernel
  · change (2 : ZMod 22058012573) ^ 22058012572 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 22058012573) ^ 11029006286 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 22058012573) ^ 11029006286 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 22058012573) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999998783 : Nat.Prime 399999999998783 := by
  apply lucas_from_prime_list 399999999998783 (5 : ZMod 399999999998783) [2,9067,22058012573]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_9067
    · exact prime_22058012573
  · decide +kernel
  · change (5 : ZMod 399999999998783) ^ 399999999998782 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (5 : ZMod 399999999998783) ^ 199999999999391 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999998783) ^ 44116025146 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999998783) ^ 18134 ≠ 1
      reduce_mod_char
      decide

private lemma prime_21481 : Nat.Prime 21481 := by
  apply lucas_from_prime_list 21481 (13 : ZMod 21481) [2,2,2,3,5,179]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_179
  · decide +kernel
  · change (13 : ZMod 21481) ^ 21480 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 21481) ^ 10740 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 21481) ^ 10740 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 21481) ^ 10740 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 21481) ^ 7160 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 21481) ^ 4296 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 21481) ^ 120 ≠ 1
      reduce_mod_char
      decide

private lemma prime_232982927 : Nat.Prime 232982927 := by
  apply lucas_from_prime_list 232982927 (5 : ZMod 232982927) [2,11,17,29,21481]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_17
    · exact prime_29
    · exact prime_21481
  · decide +kernel
  · change (5 : ZMod 232982927) ^ 232982926 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 232982927) ^ 116491463 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 232982927) ^ 21180266 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 232982927) ^ 13704878 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 232982927) ^ 8033894 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 232982927) ^ 10846 ≠ 1
      reduce_mod_char
      decide

private lemma prime_22366360993 : Nat.Prime 22366360993 := by
  apply lucas_from_prime_list 22366360993 (10 : ZMod 22366360993) [2,2,2,2,2,3,232982927]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_232982927
  · decide +kernel
  · change (10 : ZMod 22366360993) ^ 22366360992 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 22366360993) ^ 11183180496 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 22366360993) ^ 11183180496 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 22366360993) ^ 11183180496 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 22366360993) ^ 11183180496 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 22366360993) ^ 11183180496 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 22366360993) ^ 7455453664 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 22366360993) ^ 96 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999998813 : Nat.Prime 399999999998813 := by
  apply lucas_from_prime_list 399999999998813 (2 : ZMod 399999999998813) [2,2,17,263,22366360993]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_17
    · exact prime_263
    · exact prime_22366360993
  · decide +kernel
  · change (2 : ZMod 399999999998813) ^ 399999999998812 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 399999999998813) ^ 199999999999406 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999998813) ^ 199999999999406 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999998813) ^ 23529411764636 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999998813) ^ 1520912547524 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999998813) ^ 17884 ≠ 1
      reduce_mod_char
      decide

private lemma prime_853 : Nat.Prime 853 := by
  apply lucas_from_prime_list 853 (2 : ZMod 853) [2,2,3,71]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_71
  · decide +kernel
  · change (2 : ZMod 853) ^ 852 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 853) ^ 426 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 853) ^ 426 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 853) ^ 284 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 853) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_733 : Nat.Prime 733 := by
  apply lucas_from_prime_list 733 (6 : ZMod 733) [2,2,3,61]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_61
  · decide +kernel
  · change (6 : ZMod 733) ^ 732 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 733) ^ 366 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 733) ^ 366 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 733) ^ 244 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 733) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_60107 : Nat.Prime 60107 := by
  apply lucas_from_prime_list 60107 (2 : ZMod 60107) [2,41,733]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_733
  · decide +kernel
  · change (2 : ZMod 60107) ^ 60106 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 60107) ^ 30053 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 60107) ^ 1466 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 60107) ^ 82 ≠ 1
      reduce_mod_char
      decide

private lemma prime_304502063 : Nat.Prime 304502063 := by
  apply lucas_from_prime_list 304502063 (5 : ZMod 304502063) [2,17,149,60107]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_149
    · exact prime_60107
  · decide +kernel
  · change (5 : ZMod 304502063) ^ 304502062 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 304502063) ^ 152251031 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 304502063) ^ 17911886 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 304502063) ^ 2043638 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 304502063) ^ 5066 ≠ 1
      reduce_mod_char
      decide

private lemma prime_519480519479 : Nat.Prime 519480519479 := by
  apply lucas_from_prime_list 519480519479 (11 : ZMod 519480519479) [2,853,304502063]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_853
    · exact prime_304502063
  · decide +kernel
  · change (11 : ZMod 519480519479) ^ 519480519478 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (11 : ZMod 519480519479) ^ 259740259739 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 519480519479) ^ 609004126 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 519480519479) ^ 1706 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999998831 : Nat.Prime 399999999998831 := by
  apply lucas_from_prime_list 399999999998831 (11 : ZMod 399999999998831) [2,5,7,11,519480519479]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_519480519479
  · decide +kernel
  · change (11 : ZMod 399999999998831) ^ 399999999998830 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 399999999998831) ^ 199999999999415 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 399999999998831) ^ 79999999999766 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 399999999998831) ^ 57142857142690 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 399999999998831) ^ 36363636363530 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 399999999998831) ^ 770 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3720361 : Nat.Prime 3720361 := by
  apply lucas_from_prime_list 3720361 (23 : ZMod 3720361) [2,2,2,3,5,7,43,103]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_43
    · exact prime_103
  · decide +kernel
  · change (23 : ZMod 3720361) ^ 3720360 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 3720361) ^ 1860180 ≠ 1
      reduce_mod_char
      decide
    · change (23 : ZMod 3720361) ^ 1860180 ≠ 1
      reduce_mod_char
      decide
    · change (23 : ZMod 3720361) ^ 1860180 ≠ 1
      reduce_mod_char
      decide
    · change (23 : ZMod 3720361) ^ 1240120 ≠ 1
      reduce_mod_char
      decide
    · change (23 : ZMod 3720361) ^ 744072 ≠ 1
      reduce_mod_char
      decide
    · change (23 : ZMod 3720361) ^ 531480 ≠ 1
      reduce_mod_char
      decide
    · change (23 : ZMod 3720361) ^ 86520 ≠ 1
      reduce_mod_char
      decide
    · change (23 : ZMod 3720361) ^ 36120 ≠ 1
      reduce_mod_char
      decide

private lemma prime_354609929077 : Nat.Prime 354609929077 := by
  apply lucas_from_prime_list 354609929077 (2 : ZMod 354609929077) [2,2,3,13,13,47,3720361]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_13
    · exact prime_13
    · exact prime_47
    · exact prime_3720361
  · decide +kernel
  · change (2 : ZMod 354609929077) ^ 354609929076 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 354609929077) ^ 177304964538 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 354609929077) ^ 177304964538 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 354609929077) ^ 118203309692 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 354609929077) ^ 27277686852 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 354609929077) ^ 27277686852 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 354609929077) ^ 7544892108 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 354609929077) ^ 95316 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999998857 : Nat.Prime 399999999998857 := by
  apply lucas_from_prime_list 399999999998857 (5 : ZMod 399999999998857) [2,2,2,3,47,354609929077]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_47
    · exact prime_354609929077
  · decide +kernel
  · change (5 : ZMod 399999999998857) ^ 399999999998856 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 399999999998857) ^ 199999999999428 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999998857) ^ 199999999999428 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999998857) ^ 199999999999428 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999998857) ^ 133333333332952 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999998857) ^ 8510638297848 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999998857) ^ 1128 ≠ 1
      reduce_mod_char
      decide

private lemma prime_487 : Nat.Prime 487 := by
  apply lucas_from_prime_list 487 (3 : ZMod 487) [2,3,3,3,3,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
  · decide +kernel
  · change (3 : ZMod 487) ^ 486 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 487) ^ 243 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 487) ^ 162 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 487) ^ 162 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 487) ^ 162 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 487) ^ 162 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 487) ^ 162 ≠ 1
      reduce_mod_char
      decide

private lemma prime_256163 : Nat.Prime 256163 := by
  apply lucas_from_prime_list 256163 (2 : ZMod 256163) [2,263,487]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_263
    · exact prime_487
  · decide +kernel
  · change (2 : ZMod 256163) ^ 256162 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 256163) ^ 128081 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 256163) ^ 974 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 256163) ^ 526 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999998881 : Nat.Prime 399999999998881 := by
  apply lucas_from_prime_list 399999999998881 (22 : ZMod 399999999998881) [2,2,2,2,2,3,3,5,17,227,281,256163]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_227
    · exact prime_281
    · exact prime_256163
  · decide +kernel
  · change (22 : ZMod 399999999998881) ^ 399999999998880 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 399999999998881) ^ 199999999999440 ≠ 1
      reduce_mod_char
      decide
    · change (22 : ZMod 399999999998881) ^ 199999999999440 ≠ 1
      reduce_mod_char
      decide
    · change (22 : ZMod 399999999998881) ^ 199999999999440 ≠ 1
      reduce_mod_char
      decide
    · change (22 : ZMod 399999999998881) ^ 199999999999440 ≠ 1
      reduce_mod_char
      decide
    · change (22 : ZMod 399999999998881) ^ 199999999999440 ≠ 1
      reduce_mod_char
      decide
    · change (22 : ZMod 399999999998881) ^ 133333333332960 ≠ 1
      reduce_mod_char
      decide
    · change (22 : ZMod 399999999998881) ^ 133333333332960 ≠ 1
      reduce_mod_char
      decide
    · change (22 : ZMod 399999999998881) ^ 79999999999776 ≠ 1
      reduce_mod_char
      decide
    · change (22 : ZMod 399999999998881) ^ 23529411764640 ≠ 1
      reduce_mod_char
      decide
    · change (22 : ZMod 399999999998881) ^ 1762114537440 ≠ 1
      reduce_mod_char
      decide
    · change (22 : ZMod 399999999998881) ^ 1423487544480 ≠ 1
      reduce_mod_char
      decide
    · change (22 : ZMod 399999999998881) ^ 1561505760 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1381 : Nat.Prime 1381 := by
  apply lucas_from_prime_list 1381 (2 : ZMod 1381) [2,2,3,5,23]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_23
  · decide +kernel
  · change (2 : ZMod 1381) ^ 1380 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1381) ^ 690 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1381) ^ 690 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1381) ^ 460 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1381) ^ 276 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1381) ^ 60 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4021 : Nat.Prime 4021 := by
  apply lucas_from_prime_list 4021 (2 : ZMod 4021) [2,2,3,5,67]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_67
  · decide +kernel
  · change (2 : ZMod 4021) ^ 4020 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4021) ^ 2010 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4021) ^ 2010 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4021) ^ 1340 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4021) ^ 804 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4021) ^ 60 ≠ 1
      reduce_mod_char
      decide

private lemma prime_55530011 : Nat.Prime 55530011 := by
  apply lucas_from_prime_list 55530011 (2 : ZMod 55530011) [2,5,1381,4021]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_1381
    · exact prime_4021
  · decide +kernel
  · change (2 : ZMod 55530011) ^ 55530010 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55530011) ^ 27765005 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 55530011) ^ 11106002 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 55530011) ^ 40210 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 55530011) ^ 13810 ≠ 1
      reduce_mod_char
      decide

private lemma prime_111060023 : Nat.Prime 111060023 := by
  apply lucas_from_prime_list 111060023 (5 : ZMod 111060023) [2,55530011]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_55530011
  · decide +kernel
  · change (5 : ZMod 111060023) ^ 111060022 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 111060023) ^ 55530011 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 111060023) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_222120047 : Nat.Prime 222120047 := by
  apply lucas_from_prime_list 222120047 (5 : ZMod 222120047) [2,111060023]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_111060023
  · decide +kernel
  · change (5 : ZMod 222120047) ^ 222120046 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 222120047) ^ 111060023 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 222120047) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_397 : Nat.Prime 397 := by
  apply lucas_from_prime_list 397 (5 : ZMod 397) [2,2,3,3,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_11
  · decide +kernel
  · change (5 : ZMod 397) ^ 396 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 397) ^ 198 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 397) ^ 198 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 397) ^ 132 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 397) ^ 132 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 397) ^ 36 ≠ 1
      reduce_mod_char
      decide

private lemma prime_50023 : Nat.Prime 50023 := by
  apply lucas_from_prime_list 50023 (3 : ZMod 50023) [2,3,3,7,397]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_7
    · exact prime_397
  · decide +kernel
  · change (3 : ZMod 50023) ^ 50022 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 50023) ^ 25011 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 50023) ^ 16674 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 50023) ^ 16674 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 50023) ^ 7146 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 50023) ^ 126 ≠ 1
      reduce_mod_char
      decide

private lemma prime_66666666666487 : Nat.Prime 66666666666487 := by
  apply lucas_from_prime_list 66666666666487 (5 : ZMod 66666666666487) [2,3,50023,222120047]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_50023
    · exact prime_222120047
  · decide +kernel
  · change (5 : ZMod 66666666666487) ^ 66666666666486 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66666666666487) ^ 33333333333243 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 66666666666487) ^ 22222222222162 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 66666666666487) ^ 1332720282 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 66666666666487) ^ 300138 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999998923 : Nat.Prime 399999999998923 := by
  apply lucas_from_prime_list 399999999998923 (2 : ZMod 399999999998923) [2,3,66666666666487]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_66666666666487
  · decide +kernel
  · change (2 : ZMod 399999999998923) ^ 399999999998922 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 399999999998923) ^ 199999999999461 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999998923) ^ 133333333332974 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999998923) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2539 : Nat.Prime 2539 := by
  apply lucas_from_prime_list 2539 (2 : ZMod 2539) [2,3,3,3,47]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_47
  · decide +kernel
  · change (2 : ZMod 2539) ^ 2538 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2539) ^ 1269 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2539) ^ 846 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2539) ^ 846 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2539) ^ 846 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2539) ^ 54 ≠ 1
      reduce_mod_char
      decide

private lemma prime_25391 : Nat.Prime 25391 := by
  apply lucas_from_prime_list 25391 (7 : ZMod 25391) [2,5,2539]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_2539
  · decide +kernel
  · change (7 : ZMod 25391) ^ 25390 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 25391) ^ 12695 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 25391) ^ 5078 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 25391) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_761731 : Nat.Prime 761731 := by
  apply lucas_from_prime_list 761731 (2 : ZMod 761731) [2,3,5,25391]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_25391
  · decide +kernel
  · change (2 : ZMod 761731) ^ 761730 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 761731) ^ 380865 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 761731) ^ 253910 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 761731) ^ 152346 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 761731) ^ 30 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4235224361 : Nat.Prime 4235224361 := by
  apply lucas_from_prime_list 4235224361 (3 : ZMod 4235224361) [2,2,2,5,139,761731]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_139
    · exact prime_761731
  · decide +kernel
  · change (3 : ZMod 4235224361) ^ 4235224360 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4235224361) ^ 2117612180 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4235224361) ^ 2117612180 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4235224361) ^ 2117612180 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4235224361) ^ 847044872 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4235224361) ^ 30469240 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4235224361) ^ 5560 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999007 : Nat.Prime 399999999999007 := by
  apply lucas_from_prime_list 399999999999007 (7 : ZMod 399999999999007) [2,3,3,3,3,11,53,4235224361]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_11
    · exact prime_53
    · exact prime_4235224361
  · decide +kernel
  · change (7 : ZMod 399999999999007) ^ 399999999999006 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 399999999999007) ^ 199999999999503 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 399999999999007) ^ 133333333333002 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 399999999999007) ^ 133333333333002 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 399999999999007) ^ 133333333333002 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 399999999999007) ^ 133333333333002 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 399999999999007) ^ 36363636363546 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 399999999999007) ^ 7547169811302 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 399999999999007) ^ 94446 ≠ 1
      reduce_mod_char
      decide

private lemma prime_32983 : Nat.Prime 32983 := by
  apply lucas_from_prime_list 32983 (3 : ZMod 32983) [2,3,23,239]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_239
  · decide +kernel
  · change (3 : ZMod 32983) ^ 32982 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32983) ^ 16491 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 32983) ^ 10994 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 32983) ^ 1434 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 32983) ^ 138 ≠ 1
      reduce_mod_char
      decide

private lemma prime_50463991 : Nat.Prime 50463991 := by
  apply lucas_from_prime_list 50463991 (15 : ZMod 50463991) [2,3,3,5,17,32983]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_17
    · exact prime_32983
  · decide +kernel
  · change (15 : ZMod 50463991) ^ 50463990 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 50463991) ^ 25231995 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 50463991) ^ 16821330 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 50463991) ^ 16821330 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 50463991) ^ 10092798 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 50463991) ^ 2968470 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 50463991) ^ 1530 ≠ 1
      reduce_mod_char
      decide

private lemma prime_302783947 : Nat.Prime 302783947 := by
  apply lucas_from_prime_list 302783947 (2 : ZMod 302783947) [2,3,50463991]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_50463991
  · decide +kernel
  · change (2 : ZMod 302783947) ^ 302783946 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 302783947) ^ 151391973 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 302783947) ^ 100927982 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 302783947) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3191 : Nat.Prime 3191 := by
  apply lucas_from_prime_list 3191 (11 : ZMod 3191) [2,5,11,29]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_29
  · decide +kernel
  · change (11 : ZMod 3191) ^ 3190 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3191) ^ 1595 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 3191) ^ 638 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 3191) ^ 290 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 3191) ^ 110 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999079 : Nat.Prime 399999999999079 := by
  apply lucas_from_prime_list 399999999999079 (3 : ZMod 399999999999079) [2,3,3,23,3191,302783947]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_23
    · exact prime_3191
    · exact prime_302783947
  · decide +kernel
  · change (3 : ZMod 399999999999079) ^ 399999999999078 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 399999999999079) ^ 199999999999539 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999079) ^ 133333333333026 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999079) ^ 133333333333026 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999079) ^ 17391304347786 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999079) ^ 125352554058 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999079) ^ 1321074 ≠ 1
      reduce_mod_char
      decide

private lemma prime_11399 : Nat.Prime 11399 := by
  apply lucas_from_prime_list 11399 (11 : ZMod 11399) [2,41,139]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_139
  · decide +kernel
  · change (11 : ZMod 11399) ^ 11398 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (11 : ZMod 11399) ^ 5699 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 11399) ^ 278 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 11399) ^ 82 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3282913 : Nat.Prime 3282913 := by
  apply lucas_from_prime_list 3282913 (5 : ZMod 3282913) [2,2,2,2,2,3,3,11399]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_11399
  · decide +kernel
  · change (5 : ZMod 3282913) ^ 3282912 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3282913) ^ 1641456 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3282913) ^ 1641456 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3282913) ^ 1641456 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3282913) ^ 1641456 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3282913) ^ 1641456 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3282913) ^ 1094304 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3282913) ^ 1094304 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3282913) ^ 288 ≠ 1
      reduce_mod_char
      decide

private lemma prime_78789913 : Nat.Prime 78789913 := by
  apply lucas_from_prime_list 78789913 (5 : ZMod 78789913) [2,2,2,3,3282913]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3282913
  · decide +kernel
  · change (5 : ZMod 78789913) ^ 78789912 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 78789913) ^ 39394956 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 78789913) ^ 39394956 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 78789913) ^ 39394956 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 78789913) ^ 26263304 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 78789913) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_719 : Nat.Prime 719 := by
  apply lucas_from_prime_list 719 (11 : ZMod 719) [2,359]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_359
  · decide +kernel
  · change (11 : ZMod 719) ^ 718 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (11 : ZMod 719) ^ 359 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 719) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1439 : Nat.Prime 1439 := by
  apply lucas_from_prime_list 1439 (7 : ZMod 1439) [2,719]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_719
  · decide +kernel
  · change (7 : ZMod 1439) ^ 1438 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (7 : ZMod 1439) ^ 719 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 1439) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999097 : Nat.Prime 399999999999097 := by
  apply lucas_from_prime_list 399999999999097 (15 : ZMod 399999999999097) [2,2,2,3,3,7,7,1439,78789913]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_7
    · exact prime_7
    · exact prime_1439
    · exact prime_78789913
  · decide +kernel
  · change (15 : ZMod 399999999999097) ^ 399999999999096 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 399999999999097) ^ 199999999999548 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 399999999999097) ^ 199999999999548 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 399999999999097) ^ 199999999999548 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 399999999999097) ^ 133333333333032 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 399999999999097) ^ 133333333333032 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 399999999999097) ^ 57142857142728 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 399999999999097) ^ 57142857142728 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 399999999999097) ^ 277970813064 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 399999999999097) ^ 5076792 ≠ 1
      reduce_mod_char
      decide

private lemma prime_449 : Nat.Prime 449 := by
  apply lucas_from_prime_list 449 (3 : ZMod 449) [2,2,2,2,2,2,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_7
  · decide +kernel
  · change (3 : ZMod 449) ^ 448 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 449) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 449) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 449) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 449) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 449) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 449) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 449) ^ 64 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1213 : Nat.Prime 1213 := by
  apply lucas_from_prime_list 1213 (2 : ZMod 1213) [2,2,3,101]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_101
  · decide +kernel
  · change (2 : ZMod 1213) ^ 1212 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1213) ^ 606 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1213) ^ 606 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1213) ^ 404 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1213) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_41243 : Nat.Prime 41243 := by
  apply lucas_from_prime_list 41243 (2 : ZMod 41243) [2,17,1213]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_1213
  · decide +kernel
  · change (2 : ZMod 41243) ^ 41242 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 41243) ^ 20621 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 41243) ^ 2426 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 41243) ^ 34 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4091 : Nat.Prime 4091 := by
  apply lucas_from_prime_list 4091 (2 : ZMod 4091) [2,5,409]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_409
  · decide +kernel
  · change (2 : ZMod 4091) ^ 4090 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 4091) ^ 2045 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4091) ^ 818 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 4091) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3711952487 : Nat.Prime 3711952487 := by
  apply lucas_from_prime_list 3711952487 (10 : ZMod 3711952487) [2,11,4091,41243]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_4091
    · exact prime_41243
  · decide +kernel
  · change (10 : ZMod 3711952487) ^ 3711952486 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (10 : ZMod 3711952487) ^ 1855976243 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 3711952487) ^ 337450226 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 3711952487) ^ 907346 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 3711952487) ^ 90002 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999121 : Nat.Prime 399999999999121 := by
  apply lucas_from_prime_list 399999999999121 (17 : ZMod 399999999999121) [2,2,2,2,3,5,449,3711952487]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_449
    · exact prime_3711952487
  · decide +kernel
  · change (17 : ZMod 399999999999121) ^ 399999999999120 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 399999999999121) ^ 199999999999560 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 399999999999121) ^ 199999999999560 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 399999999999121) ^ 199999999999560 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 399999999999121) ^ 199999999999560 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 399999999999121) ^ 133333333333040 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 399999999999121) ^ 79999999999824 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 399999999999121) ^ 890868596880 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 399999999999121) ^ 107760 ≠ 1
      reduce_mod_char
      decide

private lemma prime_379 : Nat.Prime 379 := by
  apply lucas_from_prime_list 379 (2 : ZMod 379) [2,3,3,3,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_7
  · decide +kernel
  · change (2 : ZMod 379) ^ 378 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 379) ^ 189 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 379) ^ 126 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 379) ^ 126 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 379) ^ 126 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 379) ^ 54 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1670633 : Nat.Prime 1670633 := by
  apply lucas_from_prime_list 1670633 (3 : ZMod 1670633) [2,2,2,19,29,379]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_19
    · exact prime_29
    · exact prime_379
  · decide +kernel
  · change (3 : ZMod 1670633) ^ 1670632 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1670633) ^ 835316 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1670633) ^ 835316 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1670633) ^ 835316 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1670633) ^ 87928 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1670633) ^ 57608 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1670633) ^ 4408 ≠ 1
      reduce_mod_char
      decide

private lemma prime_937 : Nat.Prime 937 := by
  apply lucas_from_prime_list 937 (5 : ZMod 937) [2,2,2,3,3,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_13
  · decide +kernel
  · change (5 : ZMod 937) ^ 936 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 937) ^ 468 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 937) ^ 468 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 937) ^ 468 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 937) ^ 312 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 937) ^ 312 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 937) ^ 72 ≠ 1
      reduce_mod_char
      decide

private lemma prime_511603 : Nat.Prime 511603 := by
  apply lucas_from_prime_list 511603 (2 : ZMod 511603) [2,3,7,13,937]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_13
    · exact prime_937
  · decide +kernel
  · change (2 : ZMod 511603) ^ 511602 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 511603) ^ 255801 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 511603) ^ 170534 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 511603) ^ 73086 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 511603) ^ 39354 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 511603) ^ 546 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999133 : Nat.Prime 399999999999133 := by
  apply lucas_from_prime_list 399999999999133 (2 : ZMod 399999999999133) [2,2,3,3,13,511603,1670633]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_13
    · exact prime_511603
    · exact prime_1670633
  · decide +kernel
  · change (2 : ZMod 399999999999133) ^ 399999999999132 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 399999999999133) ^ 199999999999566 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999133) ^ 199999999999566 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999133) ^ 133333333333044 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999133) ^ 133333333333044 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999133) ^ 30769230769164 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999133) ^ 781856244 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999133) ^ 239430204 ≠ 1
      reduce_mod_char
      decide

private lemma prime_5441 : Nat.Prime 5441 := by
  apply lucas_from_prime_list 5441 (3 : ZMod 5441) [2,2,2,2,2,2,5,17]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_17
  · decide +kernel
  · change (3 : ZMod 5441) ^ 5440 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5441) ^ 2720 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5441) ^ 2720 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5441) ^ 2720 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5441) ^ 2720 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5441) ^ 2720 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5441) ^ 2720 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5441) ^ 1088 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 5441) ^ 320 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3569297 : Nat.Prime 3569297 := by
  apply lucas_from_prime_list 3569297 (3 : ZMod 3569297) [2,2,2,2,41,5441]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_41
    · exact prime_5441
  · decide +kernel
  · change (3 : ZMod 3569297) ^ 3569296 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3569297) ^ 1784648 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3569297) ^ 1784648 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3569297) ^ 1784648 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3569297) ^ 1784648 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3569297) ^ 87056 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3569297) ^ 656 ≠ 1
      reduce_mod_char
      decide

private lemma prime_5839 : Nat.Prime 5839 := by
  apply lucas_from_prime_list 5839 (6 : ZMod 5839) [2,3,7,139]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_139
  · decide +kernel
  · change (6 : ZMod 5839) ^ 5838 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5839) ^ 2919 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 5839) ^ 1946 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 5839) ^ 834 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 5839) ^ 42 ≠ 1
      reduce_mod_char
      decide

private lemma prime_23357 : Nat.Prime 23357 := by
  apply lucas_from_prime_list 23357 (2 : ZMod 23357) [2,2,5839]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5839
  · decide +kernel
  · change (2 : ZMod 23357) ^ 23356 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 23357) ^ 11678 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 23357) ^ 11678 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 23357) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2399 : Nat.Prime 2399 := by
  apply lucas_from_prime_list 2399 (11 : ZMod 2399) [2,11,109]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_109
  · decide +kernel
  · change (11 : ZMod 2399) ^ 2398 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (11 : ZMod 2399) ^ 1199 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 2399) ^ 218 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 2399) ^ 22 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999143 : Nat.Prime 399999999999143 := by
  apply lucas_from_prime_list 399999999999143 (5 : ZMod 399999999999143) [2,2399,23357,3569297]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2399
    · exact prime_23357
    · exact prime_3569297
  · decide +kernel
  · change (5 : ZMod 399999999999143) ^ 399999999999142 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 399999999999143) ^ 199999999999571 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999999143) ^ 166736140058 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999999143) ^ 17125487006 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999999143) ^ 112066886 ≠ 1
      reduce_mod_char
      decide

private lemma prime_7841 : Nat.Prime 7841 := by
  apply lucas_from_prime_list 7841 (12 : ZMod 7841) [2,2,2,2,2,5,7,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_7
    · exact prime_7
  · decide +kernel
  · change (12 : ZMod 7841) ^ 7840 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 7841) ^ 3920 ≠ 1
      reduce_mod_char
      decide
    · change (12 : ZMod 7841) ^ 3920 ≠ 1
      reduce_mod_char
      decide
    · change (12 : ZMod 7841) ^ 3920 ≠ 1
      reduce_mod_char
      decide
    · change (12 : ZMod 7841) ^ 3920 ≠ 1
      reduce_mod_char
      decide
    · change (12 : ZMod 7841) ^ 3920 ≠ 1
      reduce_mod_char
      decide
    · change (12 : ZMod 7841) ^ 1568 ≠ 1
      reduce_mod_char
      decide
    · change (12 : ZMod 7841) ^ 1120 ≠ 1
      reduce_mod_char
      decide
    · change (12 : ZMod 7841) ^ 1120 ≠ 1
      reduce_mod_char
      decide

private lemma prime_23561 : Nat.Prime 23561 := by
  apply lucas_from_prime_list 23561 (3 : ZMod 23561) [2,2,2,5,19,31]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_19
    · exact prime_31
  · decide +kernel
  · change (3 : ZMod 23561) ^ 23560 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23561) ^ 11780 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 23561) ^ 11780 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 23561) ^ 11780 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 23561) ^ 4712 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 23561) ^ 1240 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 23561) ^ 760 ≠ 1
      reduce_mod_char
      decide

private lemma prime_50609029 : Nat.Prime 50609029 := by
  apply lucas_from_prime_list 50609029 (2 : ZMod 50609029) [2,2,3,179,23561]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_179
    · exact prime_23561
  · decide +kernel
  · change (2 : ZMod 50609029) ^ 50609028 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50609029) ^ 25304514 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 50609029) ^ 25304514 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 50609029) ^ 16869676 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 50609029) ^ 282732 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 50609029) ^ 2148 ≠ 1
      reduce_mod_char
      decide

private lemma prime_910962523 : Nat.Prime 910962523 := by
  apply lucas_from_prime_list 910962523 (2 : ZMod 910962523) [2,3,3,50609029]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_50609029
  · decide +kernel
  · change (2 : ZMod 910962523) ^ 910962522 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 910962523) ^ 455481261 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 910962523) ^ 303654174 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 910962523) ^ 303654174 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 910962523) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999209 : Nat.Prime 399999999999209 := by
  apply lucas_from_prime_list 399999999999209 (3 : ZMod 399999999999209) [2,2,2,7,7841,910962523]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_7841
    · exact prime_910962523
  · decide +kernel
  · change (3 : ZMod 399999999999209) ^ 399999999999208 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 399999999999209) ^ 199999999999604 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999209) ^ 199999999999604 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999209) ^ 199999999999604 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999209) ^ 57142857142744 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999209) ^ 51013901288 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999209) ^ 439096 ≠ 1
      reduce_mod_char
      decide

private lemma prime_387721 : Nat.Prime 387721 := by
  apply lucas_from_prime_list 387721 (37 : ZMod 387721) [2,2,2,3,3,3,5,359]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_359
  · decide +kernel
  · change (37 : ZMod 387721) ^ 387720 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 387721) ^ 193860 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 387721) ^ 193860 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 387721) ^ 193860 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 387721) ^ 129240 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 387721) ^ 129240 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 387721) ^ 129240 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 387721) ^ 77544 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 387721) ^ 1080 ≠ 1
      reduce_mod_char
      decide

private lemma prime_599 : Nat.Prime 599 := by
  apply lucas_from_prime_list 599 (7 : ZMod 599) [2,13,23]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_23
  · decide +kernel
  · change (7 : ZMod 599) ^ 598 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 599) ^ 299 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 599) ^ 46 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 599) ^ 26 ≠ 1
      reduce_mod_char
      decide

private lemma prime_21529 : Nat.Prime 21529 := by
  apply lucas_from_prime_list 21529 (11 : ZMod 21529) [2,2,2,3,3,13,23]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_13
    · exact prime_23
  · decide +kernel
  · change (11 : ZMod 21529) ^ 21528 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 21529) ^ 10764 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 21529) ^ 10764 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 21529) ^ 10764 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 21529) ^ 7176 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 21529) ^ 7176 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 21529) ^ 1656 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 21529) ^ 936 ≠ 1
      reduce_mod_char
      decide

private lemma prime_99999999999821 : Nat.Prime 99999999999821 := by
  apply lucas_from_prime_list 99999999999821 (3 : ZMod 99999999999821) [2,2,5,599,21529,387721]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_599
    · exact prime_21529
    · exact prime_387721
  · decide +kernel
  · change (3 : ZMod 99999999999821) ^ 99999999999820 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 99999999999821) ^ 49999999999910 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 99999999999821) ^ 49999999999910 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 99999999999821) ^ 19999999999964 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 99999999999821) ^ 166944908180 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 99999999999821) ^ 4644897580 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 99999999999821) ^ 257917420 ≠ 1
      reduce_mod_char
      decide

private lemma prime_199999999999643 : Nat.Prime 199999999999643 := by
  apply lucas_from_prime_list 199999999999643 (2 : ZMod 199999999999643) [2,99999999999821]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_99999999999821
  · decide +kernel
  · change (2 : ZMod 199999999999643) ^ 199999999999642 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 199999999999643) ^ 99999999999821 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 199999999999643) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999287 : Nat.Prime 399999999999287 := by
  apply lucas_from_prime_list 399999999999287 (5 : ZMod 399999999999287) [2,199999999999643]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_199999999999643
  · decide +kernel
  · change (5 : ZMod 399999999999287) ^ 399999999999286 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (5 : ZMod 399999999999287) ^ 199999999999643 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999999287) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3229 : Nat.Prime 3229 := by
  apply lucas_from_prime_list 3229 (6 : ZMod 3229) [2,2,3,269]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_269
  · decide +kernel
  · change (6 : ZMod 3229) ^ 3228 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3229) ^ 1614 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3229) ^ 1614 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3229) ^ 1076 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 3229) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4519 : Nat.Prime 4519 := by
  apply lucas_from_prime_list 4519 (3 : ZMod 4519) [2,3,3,251]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_251
  · decide +kernel
  · change (3 : ZMod 4519) ^ 4518 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4519) ^ 2259 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4519) ^ 1506 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4519) ^ 1506 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4519) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_49157683 : Nat.Prime 49157683 := by
  apply lucas_from_prime_list 49157683 (3 : ZMod 49157683) [2,3,7,7,37,4519]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_7
    · exact prime_37
    · exact prime_4519
  · decide +kernel
  · change (3 : ZMod 49157683) ^ 49157682 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49157683) ^ 24578841 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 49157683) ^ 16385894 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 49157683) ^ 7022526 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 49157683) ^ 7022526 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 49157683) ^ 1328586 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 49157683) ^ 10878 ≠ 1
      reduce_mod_char
      decide

private lemma prime_491576831 : Nat.Prime 491576831 := by
  apply lucas_from_prime_list 491576831 (7 : ZMod 491576831) [2,5,49157683]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_49157683
  · decide +kernel
  · change (7 : ZMod 491576831) ^ 491576830 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 491576831) ^ 245788415 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 491576831) ^ 98315366 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 491576831) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999349 : Nat.Prime 399999999999349 := by
  apply lucas_from_prime_list 399999999999349 (2 : ZMod 399999999999349) [2,2,3,3,7,3229,491576831]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_7
    · exact prime_3229
    · exact prime_491576831
  · decide +kernel
  · change (2 : ZMod 399999999999349) ^ 399999999999348 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 399999999999349) ^ 199999999999674 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999349) ^ 199999999999674 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999349) ^ 133333333333116 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999349) ^ 133333333333116 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999349) ^ 57142857142764 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999349) ^ 123877361412 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999349) ^ 813708 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1033 : Nat.Prime 1033 := by
  apply lucas_from_prime_list 1033 (5 : ZMod 1033) [2,2,2,3,43]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_43
  · decide +kernel
  · change (5 : ZMod 1033) ^ 1032 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1033) ^ 516 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 1033) ^ 516 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 1033) ^ 516 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 1033) ^ 344 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 1033) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_34673 : Nat.Prime 34673 := by
  apply lucas_from_prime_list 34673 (3 : ZMod 34673) [2,2,2,2,11,197]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_11
    · exact prime_197
  · decide +kernel
  · change (3 : ZMod 34673) ^ 34672 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34673) ^ 17336 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 34673) ^ 17336 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 34673) ^ 17336 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 34673) ^ 17336 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 34673) ^ 3152 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 34673) ^ 176 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1575957197 : Nat.Prime 1575957197 := by
  apply lucas_from_prime_list 1575957197 (2 : ZMod 1575957197) [2,2,11,1033,34673]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_11
    · exact prime_1033
    · exact prime_34673
  · decide +kernel
  · change (2 : ZMod 1575957197) ^ 1575957196 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1575957197) ^ 787978598 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1575957197) ^ 787978598 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1575957197) ^ 143268836 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1575957197) ^ 1525612 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1575957197) ^ 45452 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999359 : Nat.Prime 399999999999359 := by
  apply lucas_from_prime_list 399999999999359 (7 : ZMod 399999999999359) [2,11,83,139,1575957197]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_11
    · exact prime_83
    · exact prime_139
    · exact prime_1575957197
  · decide +kernel
  · change (7 : ZMod 399999999999359) ^ 399999999999358 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 399999999999359) ^ 199999999999679 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 399999999999359) ^ 36363636363578 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 399999999999359) ^ 4819277108426 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 399999999999359) ^ 2877697841722 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 399999999999359) ^ 253814 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3329 : Nat.Prime 3329 := by
  apply lucas_from_prime_list 3329 (3 : ZMod 3329) [2,2,2,2,2,2,2,2,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_13
  · decide +kernel
  · change (3 : ZMod 3329) ^ 3328 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3329) ^ 1664 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3329) ^ 1664 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3329) ^ 1664 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3329) ^ 1664 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3329) ^ 1664 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3329) ^ 1664 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3329) ^ 1664 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3329) ^ 1664 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 3329) ^ 256 ≠ 1
      reduce_mod_char
      decide

private lemma prime_6659 : Nat.Prime 6659 := by
  apply lucas_from_prime_list 6659 (2 : ZMod 6659) [2,3329]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_3329
  · decide +kernel
  · change (2 : ZMod 6659) ^ 6658 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 6659) ^ 3329 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 6659) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3181 : Nat.Prime 3181 := by
  apply lucas_from_prime_list 3181 (7 : ZMod 3181) [2,2,3,5,53]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_53
  · decide +kernel
  · change (7 : ZMod 3181) ^ 3180 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3181) ^ 1590 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3181) ^ 1590 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3181) ^ 1060 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3181) ^ 636 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 3181) ^ 60 ≠ 1
      reduce_mod_char
      decide

private lemma prime_19087 : Nat.Prime 19087 := by
  apply lucas_from_prime_list 19087 (19 : ZMod 19087) [2,3,3181]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3181
  · decide +kernel
  · change (19 : ZMod 19087) ^ 19086 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (19 : ZMod 19087) ^ 9543 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 19087) ^ 6362 ≠ 1
      reduce_mod_char
      decide
    · change (19 : ZMod 19087) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_47281323877 : Nat.Prime 47281323877 := by
  apply lucas_from_prime_list 47281323877 (2 : ZMod 47281323877) [2,2,3,31,6659,19087]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_31
    · exact prime_6659
    · exact prime_19087
  · decide +kernel
  · change (2 : ZMod 47281323877) ^ 47281323876 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47281323877) ^ 23640661938 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 47281323877) ^ 23640661938 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 47281323877) ^ 15760441292 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 47281323877) ^ 1525203996 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 47281323877) ^ 7100364 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 47281323877) ^ 2477148 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999421 : Nat.Prime 399999999999421 := by
  apply lucas_from_prime_list 399999999999421 (2 : ZMod 399999999999421) [2,2,3,3,5,47,47281323877]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_47
    · exact prime_47281323877
  · decide +kernel
  · change (2 : ZMod 399999999999421) ^ 399999999999420 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 399999999999421) ^ 199999999999710 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999421) ^ 199999999999710 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999421) ^ 133333333333140 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999421) ^ 133333333333140 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999421) ^ 79999999999884 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999421) ^ 8510638297860 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999421) ^ 8460 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1447 : Nat.Prime 1447 := by
  apply lucas_from_prime_list 1447 (3 : ZMod 1447) [2,3,241]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_241
  · decide +kernel
  · change (3 : ZMod 1447) ^ 1446 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 1447) ^ 723 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1447) ^ 482 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1447) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3383087 : Nat.Prime 3383087 := by
  apply lucas_from_prime_list 3383087 (5 : ZMod 3383087) [2,7,167,1447]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_167
    · exact prime_1447
  · decide +kernel
  · change (5 : ZMod 3383087) ^ 3383086 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3383087) ^ 1691543 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3383087) ^ 483298 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3383087) ^ 20258 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 3383087) ^ 2338 ≠ 1
      reduce_mod_char
      decide

private lemma prime_87960263 : Nat.Prime 87960263 := by
  apply lucas_from_prime_list 87960263 (5 : ZMod 87960263) [2,13,3383087]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_13
    · exact prime_3383087
  · decide +kernel
  · change (5 : ZMod 87960263) ^ 87960262 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (5 : ZMod 87960263) ^ 43980131 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 87960263) ^ 6766174 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 87960263) ^ 26 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1231443683 : Nat.Prime 1231443683 := by
  apply lucas_from_prime_list 1231443683 (2 : ZMod 1231443683) [2,7,87960263]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_87960263
  · decide +kernel
  · change (2 : ZMod 1231443683) ^ 1231443682 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 1231443683) ^ 615721841 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1231443683) ^ 175920526 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1231443683) ^ 14 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1259 : Nat.Prime 1259 := by
  apply lucas_from_prime_list 1259 (2 : ZMod 1259) [2,17,37]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_37
  · decide +kernel
  · change (2 : ZMod 1259) ^ 1258 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 1259) ^ 629 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1259) ^ 74 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1259) ^ 34 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999427 : Nat.Prime 399999999999427 := by
  apply lucas_from_prime_list 399999999999427 (2 : ZMod 399999999999427) [2,3,43,1259,1231443683]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_43
    · exact prime_1259
    · exact prime_1231443683
  · decide +kernel
  · change (2 : ZMod 399999999999427) ^ 399999999999426 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 399999999999427) ^ 199999999999713 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999427) ^ 133333333333142 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999427) ^ 9302325581382 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999427) ^ 317712470214 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999427) ^ 324822 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2377 : Nat.Prime 2377 := by
  apply lucas_from_prime_list 2377 (5 : ZMod 2377) [2,2,2,3,3,3,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_11
  · decide +kernel
  · change (5 : ZMod 2377) ^ 2376 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2377) ^ 1188 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 2377) ^ 1188 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 2377) ^ 1188 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 2377) ^ 792 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 2377) ^ 792 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 2377) ^ 792 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 2377) ^ 216 ≠ 1
      reduce_mod_char
      decide

private lemma prime_5548773721 : Nat.Prime 5548773721 := by
  apply lucas_from_prime_list 5548773721 (11 : ZMod 5548773721) [2,2,2,3,5,7,7,397,2377]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_7
    · exact prime_397
    · exact prime_2377
  · decide +kernel
  · change (11 : ZMod 5548773721) ^ 5548773720 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5548773721) ^ 2774386860 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 5548773721) ^ 2774386860 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 5548773721) ^ 2774386860 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 5548773721) ^ 1849591240 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 5548773721) ^ 1109754744 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 5548773721) ^ 792681960 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 5548773721) ^ 792681960 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 5548773721) ^ 13976760 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 5548773721) ^ 2334360 ≠ 1
      reduce_mod_char
      decide

private lemma prime_9011 : Nat.Prime 9011 := by
  apply lucas_from_prime_list 9011 (2 : ZMod 9011) [2,5,17,53]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_17
    · exact prime_53
  · decide +kernel
  · change (2 : ZMod 9011) ^ 9010 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9011) ^ 4505 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 9011) ^ 1802 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 9011) ^ 530 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 9011) ^ 170 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999449 : Nat.Prime 399999999999449 := by
  apply lucas_from_prime_list 399999999999449 (3 : ZMod 399999999999449) [2,2,2,9011,5548773721]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_9011
    · exact prime_5548773721
  · decide +kernel
  · change (3 : ZMod 399999999999449) ^ 399999999999448 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 399999999999449) ^ 199999999999724 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999449) ^ 199999999999724 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999449) ^ 199999999999724 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999449) ^ 44390189768 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999449) ^ 72088 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1683433 : Nat.Prime 1683433 := by
  apply lucas_from_prime_list 1683433 (7 : ZMod 1683433) [2,2,2,3,3,103,227]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_103
    · exact prime_227
  · decide +kernel
  · change (7 : ZMod 1683433) ^ 1683432 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1683433) ^ 841716 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 1683433) ^ 841716 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 1683433) ^ 841716 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 1683433) ^ 561144 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 1683433) ^ 561144 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 1683433) ^ 16344 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 1683433) ^ 7416 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1423 : Nat.Prime 1423 := by
  apply lucas_from_prime_list 1423 (3 : ZMod 1423) [2,3,3,79]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_79
  · decide +kernel
  · change (3 : ZMod 1423) ^ 1422 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1423) ^ 711 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1423) ^ 474 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1423) ^ 474 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1423) ^ 18 ≠ 1
      reduce_mod_char
      decide

private lemma prime_11927 : Nat.Prime 11927 := by
  apply lucas_from_prime_list 11927 (5 : ZMod 11927) [2,67,89]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_67
    · exact prime_89
  · decide +kernel
  · change (5 : ZMod 11927) ^ 11926 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (5 : ZMod 11927) ^ 5963 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 11927) ^ 178 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 11927) ^ 134 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999503 : Nat.Prime 399999999999503 := by
  apply lucas_from_prime_list 399999999999503 (5 : ZMod 399999999999503) [2,7,1423,11927,1683433]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_1423
    · exact prime_11927
    · exact prime_1683433
  · decide +kernel
  · change (5 : ZMod 399999999999503) ^ 399999999999502 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 399999999999503) ^ 199999999999751 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999999503) ^ 57142857142786 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999999503) ^ 281096275474 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999999503) ^ 33537352226 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 399999999999503) ^ 237609694 ≠ 1
      reduce_mod_char
      decide

private lemma prime_15361 : Nat.Prime 15361 := by
  apply lucas_from_prime_list 15361 (7 : ZMod 15361) [2,2,2,2,2,2,2,2,2,2,3,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · decide +kernel
  · change (7 : ZMod 15361) ^ 15360 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15361) ^ 7680 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 15361) ^ 7680 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 15361) ^ 7680 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 15361) ^ 7680 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 15361) ^ 7680 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 15361) ^ 7680 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 15361) ^ 7680 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 15361) ^ 7680 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 15361) ^ 7680 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 15361) ^ 7680 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 15361) ^ 5120 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 15361) ^ 3072 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1601 : Nat.Prime 1601 := by
  apply lucas_from_prime_list 1601 (3 : ZMod 1601) [2,2,2,2,2,2,5,5]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_5
  · decide +kernel
  · change (3 : ZMod 1601) ^ 1600 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1601) ^ 800 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1601) ^ 800 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1601) ^ 800 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1601) ^ 800 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1601) ^ 800 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1601) ^ 800 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1601) ^ 320 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1601) ^ 320 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3203 : Nat.Prime 3203 := by
  apply lucas_from_prime_list 3203 (2 : ZMod 3203) [2,1601]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_1601
  · decide +kernel
  · change (2 : ZMod 3203) ^ 3202 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 3203) ^ 1601 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3203) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_44843 : Nat.Prime 44843 := by
  apply lucas_from_prime_list 44843 (5 : ZMod 44843) [2,7,3203]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_3203
  · decide +kernel
  · change (5 : ZMod 44843) ^ 44842 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (5 : ZMod 44843) ^ 22421 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 44843) ^ 6406 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 44843) ^ 14 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999517 : Nat.Prime 399999999999517 := by
  apply lucas_from_prime_list 399999999999517 (6 : ZMod 399999999999517) [2,2,3,7,31,223,15361,44843]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_31
    · exact prime_223
    · exact prime_15361
    · exact prime_44843
  · decide +kernel
  · change (6 : ZMod 399999999999517) ^ 399999999999516 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 399999999999517) ^ 199999999999758 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999517) ^ 199999999999758 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999517) ^ 133333333333172 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999517) ^ 57142857142788 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999517) ^ 12903225806436 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999517) ^ 1793721973092 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999517) ^ 26039971356 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999517) ^ 8920009812 ≠ 1
      reduce_mod_char
      decide

private lemma prime_797 : Nat.Prime 797 := by
  apply lucas_from_prime_list 797 (2 : ZMod 797) [2,2,199]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_199
  · decide +kernel
  · change (2 : ZMod 797) ^ 796 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 797) ^ 398 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 797) ^ 398 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 797) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_63761 : Nat.Prime 63761 := by
  apply lucas_from_prime_list 63761 (3 : ZMod 63761) [2,2,2,2,5,797]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_797
  · decide +kernel
  · change (3 : ZMod 63761) ^ 63760 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 63761) ^ 31880 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 63761) ^ 31880 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 63761) ^ 31880 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 63761) ^ 31880 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 63761) ^ 12752 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 63761) ^ 80 ≠ 1
      reduce_mod_char
      decide

private lemma prime_616313827 : Nat.Prime 616313827 := by
  apply lucas_from_prime_list 616313827 (3 : ZMod 616313827) [2,3,3,3,179,63761]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_179
    · exact prime_63761
  · decide +kernel
  · change (3 : ZMod 616313827) ^ 616313826 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 616313827) ^ 308156913 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 616313827) ^ 205437942 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 616313827) ^ 205437942 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 616313827) ^ 205437942 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 616313827) ^ 3443094 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 616313827) ^ 9666 ≠ 1
      reduce_mod_char
      decide

private lemma prime_373 : Nat.Prime 373 := by
  apply lucas_from_prime_list 373 (2 : ZMod 373) [2,2,3,31]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_31
  · decide +kernel
  · change (2 : ZMod 373) ^ 372 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 373) ^ 186 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 373) ^ 186 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 373) ^ 124 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 373) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999541 : Nat.Prime 399999999999541 := by
  apply lucas_from_prime_list 399999999999541 (2 : ZMod 399999999999541) [2,2,3,5,29,373,616313827]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_29
    · exact prime_373
    · exact prime_616313827
  · decide +kernel
  · change (2 : ZMod 399999999999541) ^ 399999999999540 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 399999999999541) ^ 199999999999770 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999541) ^ 199999999999770 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999541) ^ 133333333333180 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999541) ^ 79999999999908 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999541) ^ 13793103448260 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999541) ^ 1072386058980 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999541) ^ 649020 ≠ 1
      reduce_mod_char
      decide

private lemma prime_673 : Nat.Prime 673 := by
  apply lucas_from_prime_list 673 (5 : ZMod 673) [2,2,2,2,2,3,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel
  · change (5 : ZMod 673) ^ 672 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 673) ^ 336 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 673) ^ 336 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 673) ^ 336 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 673) ^ 336 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 673) ^ 336 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 673) ^ 224 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 673) ^ 96 ≠ 1
      reduce_mod_char
      decide

private lemma prime_26921 : Nat.Prime 26921 := by
  apply lucas_from_prime_list 26921 (13 : ZMod 26921) [2,2,2,5,673]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_673
  · decide +kernel
  · change (13 : ZMod 26921) ^ 26920 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 26921) ^ 13460 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 26921) ^ 13460 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 26921) ^ 13460 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 26921) ^ 5384 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 26921) ^ 40 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1301 : Nat.Prime 1301 := by
  apply lucas_from_prime_list 1301 (2 : ZMod 1301) [2,2,5,5,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_13
  · decide +kernel
  · change (2 : ZMod 1301) ^ 1300 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1301) ^ 650 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1301) ^ 650 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1301) ^ 260 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1301) ^ 260 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1301) ^ 100 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1499 : Nat.Prime 1499 := by
  apply lucas_from_prime_list 1499 (2 : ZMod 1499) [2,7,107]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_107
  · decide +kernel
  · change (2 : ZMod 1499) ^ 1498 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 1499) ^ 749 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1499) ^ 214 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1499) ^ 14 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2999 : Nat.Prime 2999 := by
  apply lucas_from_prime_list 2999 (17 : ZMod 2999) [2,1499]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_1499
  · decide +kernel
  · change (17 : ZMod 2999) ^ 2998 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (17 : ZMod 2999) ^ 1499 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 2999) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_23993 : Nat.Prime 23993 := by
  apply lucas_from_prime_list 23993 (3 : ZMod 23993) [2,2,2,2999]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2999
  · decide +kernel
  · change (3 : ZMod 23993) ^ 23992 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 23993) ^ 11996 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 23993) ^ 11996 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 23993) ^ 11996 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 23993) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999629 : Nat.Prime 399999999999629 := by
  apply lucas_from_prime_list 399999999999629 (2 : ZMod 399999999999629) [2,2,7,17,1301,23993,26921]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_17
    · exact prime_1301
    · exact prime_23993
    · exact prime_26921
  · decide +kernel
  · change (2 : ZMod 399999999999629) ^ 399999999999628 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 399999999999629) ^ 199999999999814 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999629) ^ 199999999999814 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999629) ^ 57142857142804 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999629) ^ 23529411764684 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999629) ^ 307455803228 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999629) ^ 16671529196 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999629) ^ 14858289068 ≠ 1
      reduce_mod_char
      decide

private lemma prime_461 : Nat.Prime 461 := by
  apply lucas_from_prime_list 461 (2 : ZMod 461) [2,2,5,23]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_23
  · decide +kernel
  · change (2 : ZMod 461) ^ 460 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 461) ^ 230 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 461) ^ 230 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 461) ^ 92 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 461) ^ 20 ≠ 1
      reduce_mod_char
      decide

private lemma prime_25065493 : Nat.Prime 25065493 := by
  apply lucas_from_prime_list 25065493 (2 : ZMod 25065493) [2,2,3,23,197,461]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_23
    · exact prime_197
    · exact prime_461
  · decide +kernel
  · change (2 : ZMod 25065493) ^ 25065492 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25065493) ^ 12532746 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 25065493) ^ 12532746 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 25065493) ^ 8355164 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 25065493) ^ 1089804 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 25065493) ^ 127236 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 25065493) ^ 54372 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999643 : Nat.Prime 399999999999643 := by
  apply lucas_from_prime_list 399999999999643 (3 : ZMod 399999999999643) [2,3,7,53,67,107,25065493]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_53
    · exact prime_67
    · exact prime_107
    · exact prime_25065493
  · decide +kernel
  · change (3 : ZMod 399999999999643) ^ 399999999999642 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 399999999999643) ^ 199999999999821 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999643) ^ 133333333333214 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999643) ^ 57142857142806 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999643) ^ 7547169811314 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999643) ^ 5970149253726 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999643) ^ 3738317757006 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999643) ^ 15958194 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1913 : Nat.Prime 1913 := by
  apply lucas_from_prime_list 1913 (3 : ZMod 1913) [2,2,2,239]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_239
  · decide +kernel
  · change (3 : ZMod 1913) ^ 1912 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1913) ^ 956 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1913) ^ 956 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1913) ^ 956 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1913) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4441 : Nat.Prime 4441 := by
  apply lucas_from_prime_list 4441 (21 : ZMod 4441) [2,2,2,3,5,37]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_37
  · decide +kernel
  · change (21 : ZMod 4441) ^ 4440 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 4441) ^ 2220 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 4441) ^ 2220 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 4441) ^ 2220 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 4441) ^ 1480 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 4441) ^ 888 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 4441) ^ 120 ≠ 1
      reduce_mod_char
      decide

private lemma prime_10729457 : Nat.Prime 10729457 := by
  apply lucas_from_prime_list 10729457 (3 : ZMod 10729457) [2,2,2,2,151,4441]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_151
    · exact prime_4441
  · decide +kernel
  · change (3 : ZMod 10729457) ^ 10729456 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10729457) ^ 5364728 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 10729457) ^ 5364728 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 10729457) ^ 5364728 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 10729457) ^ 5364728 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 10729457) ^ 71056 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 10729457) ^ 2416 ≠ 1
      reduce_mod_char
      decide

private lemma prime_64376743 : Nat.Prime 64376743 := by
  apply lucas_from_prime_list 64376743 (5 : ZMod 64376743) [2,3,10729457]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_10729457
  · decide +kernel
  · change (5 : ZMod 64376743) ^ 64376742 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (5 : ZMod 64376743) ^ 32188371 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 64376743) ^ 21458914 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 64376743) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_246305418719 : Nat.Prime 246305418719 := by
  apply lucas_from_prime_list 246305418719 (17 : ZMod 246305418719) [2,1913,64376743]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1913
    · exact prime_64376743
  · decide +kernel
  · change (17 : ZMod 246305418719) ^ 246305418718 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (17 : ZMod 246305418719) ^ 123152709359 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 246305418719) ^ 128753486 ≠ 1
      reduce_mod_char
      decide
    · change (17 : ZMod 246305418719) ^ 3826 ≠ 1
      reduce_mod_char
      decide

private lemma prime_199999999999829 : Nat.Prime 199999999999829 := by
  apply lucas_from_prime_list 199999999999829 (2 : ZMod 199999999999829) [2,2,7,29,246305418719]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_29
    · exact prime_246305418719
  · decide +kernel
  · change (2 : ZMod 199999999999829) ^ 199999999999828 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 199999999999829) ^ 99999999999914 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 199999999999829) ^ 99999999999914 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 199999999999829) ^ 28571428571404 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 199999999999829) ^ 6896551724132 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 199999999999829) ^ 812 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999659 : Nat.Prime 399999999999659 := by
  apply lucas_from_prime_list 399999999999659 (2 : ZMod 399999999999659) [2,199999999999829]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact prime_2
    · exact prime_199999999999829
  · decide +kernel
  · change (2 : ZMod 399999999999659) ^ 399999999999658 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change (2 : ZMod 399999999999659) ^ 199999999999829 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999659) ^ 2 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3851 : Nat.Prime 3851 := by
  apply lucas_from_prime_list 3851 (2 : ZMod 3851) [2,5,5,7,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_5
    · exact prime_7
    · exact prime_11
  · decide +kernel
  · change (2 : ZMod 3851) ^ 3850 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3851) ^ 1925 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3851) ^ 770 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3851) ^ 770 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3851) ^ 550 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3851) ^ 350 ≠ 1
      reduce_mod_char
      decide

private lemma prime_22805623 : Nat.Prime 22805623 := by
  apply lucas_from_prime_list 22805623 (5 : ZMod 22805623) [2,3,3,7,47,3851]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_7
    · exact prime_47
    · exact prime_3851
  · decide +kernel
  · change (5 : ZMod 22805623) ^ 22805622 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22805623) ^ 11402811 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 22805623) ^ 7601874 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 22805623) ^ 7601874 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 22805623) ^ 3257946 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 22805623) ^ 485226 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 22805623) ^ 5922 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2777 : Nat.Prime 2777 := by
  apply lucas_from_prime_list 2777 (3 : ZMod 2777) [2,2,2,347]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_347
  · decide +kernel
  · change (3 : ZMod 2777) ^ 2776 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2777) ^ 1388 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2777) ^ 1388 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2777) ^ 1388 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 2777) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1579 : Nat.Prime 1579 := by
  apply lucas_from_prime_list 1579 (3 : ZMod 1579) [2,3,263]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_263
  · decide +kernel
  · change (3 : ZMod 1579) ^ 1578 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 1579) ^ 789 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1579) ^ 526 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 1579) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_8769767 : Nat.Prime 8769767 := by
  apply lucas_from_prime_list 8769767 (5 : ZMod 8769767) [2,1579,2777]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_1579
    · exact prime_2777
  · decide +kernel
  · change (5 : ZMod 8769767) ^ 8769766 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (5 : ZMod 8769767) ^ 4384883 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 8769767) ^ 5554 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 8769767) ^ 3158 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999683 : Nat.Prime 399999999999683 := by
  apply lucas_from_prime_list 399999999999683 (2 : ZMod 399999999999683) [2,8769767,22805623]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_8769767
    · exact prime_22805623
  · decide +kernel
  · change (2 : ZMod 399999999999683) ^ 399999999999682 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 399999999999683) ^ 199999999999841 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999683) ^ 45611246 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999683) ^ 17539534 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2411 : Nat.Prime 2411 := by
  apply lucas_from_prime_list 2411 (6 : ZMod 2411) [2,5,241]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_241
  · decide +kernel
  · change (6 : ZMod 2411) ^ 2410 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (6 : ZMod 2411) ^ 1205 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 2411) ^ 482 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 2411) ^ 10 ≠ 1
      reduce_mod_char
      decide

private lemma prime_8629 : Nat.Prime 8629 := by
  apply lucas_from_prime_list 8629 (6 : ZMod 8629) [2,2,3,719]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_719
  · decide +kernel
  · change (6 : ZMod 8629) ^ 8628 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (6 : ZMod 8629) ^ 4314 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 8629) ^ 4314 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 8629) ^ 2876 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 8629) ^ 12 ≠ 1
      reduce_mod_char
      decide

private lemma prime_291263267 : Nat.Prime 291263267 := by
  apply lucas_from_prime_list 291263267 (2 : ZMod 291263267) [2,7,2411,8629]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_7
    · exact prime_2411
    · exact prime_8629
  · decide +kernel
  · change (2 : ZMod 291263267) ^ 291263266 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (2 : ZMod 291263267) ^ 145631633 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 291263267) ^ 41609038 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 291263267) ^ 120806 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 291263267) ^ 33754 ≠ 1
      reduce_mod_char
      decide

private lemma prime_6990318409 : Nat.Prime 6990318409 := by
  apply lucas_from_prime_list 6990318409 (11 : ZMod 6990318409) [2,2,2,3,291263267]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_291263267
  · decide +kernel
  · change (11 : ZMod 6990318409) ^ 6990318408 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6990318409) ^ 3495159204 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 6990318409) ^ 3495159204 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 6990318409) ^ 3495159204 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 6990318409) ^ 2330106136 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 6990318409) ^ 24 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999799 : Nat.Prime 399999999999799 := by
  apply lucas_from_prime_list 399999999999799 (21 : ZMod 399999999999799) [2,3,3,11,17,17,6990318409]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_11
    · exact prime_17
    · exact prime_17
    · exact prime_6990318409
  · decide +kernel
  · change (21 : ZMod 399999999999799) ^ 399999999999798 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 399999999999799) ^ 199999999999899 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 399999999999799) ^ 133333333333266 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 399999999999799) ^ 133333333333266 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 399999999999799) ^ 36363636363618 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 399999999999799) ^ 23529411764694 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 399999999999799) ^ 23529411764694 ≠ 1
      reduce_mod_char
      decide
    · change (21 : ZMod 399999999999799) ^ 57222 ≠ 1
      reduce_mod_char
      decide

private lemma prime_647 : Nat.Prime 647 := by
  apply lucas_from_prime_list 647 (5 : ZMod 647) [2,17,19]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_17
    · exact prime_19
  · decide +kernel
  · change (5 : ZMod 647) ^ 646 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (5 : ZMod 647) ^ 323 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 647) ^ 38 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 647) ^ 34 ≠ 1
      reduce_mod_char
      decide

private lemma prime_28409 : Nat.Prime 28409 := by
  apply lucas_from_prime_list 28409 (3 : ZMod 28409) [2,2,2,53,67]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_53
    · exact prime_67
  · decide +kernel
  · change (3 : ZMod 28409) ^ 28408 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28409) ^ 14204 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 28409) ^ 14204 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 28409) ^ 14204 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 28409) ^ 536 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 28409) ^ 424 ≠ 1
      reduce_mod_char
      decide

private lemma prime_98814229249 : Nat.Prime 98814229249 := by
  apply lucas_from_prime_list 98814229249 (29 : ZMod 98814229249) [2,2,2,2,2,2,2,2,3,7,647,28409]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_7
    · exact prime_647
    · exact prime_28409
  · decide +kernel
  · change (29 : ZMod 98814229249) ^ 98814229248 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 98814229249) ^ 49407114624 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 98814229249) ^ 49407114624 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 98814229249) ^ 49407114624 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 98814229249) ^ 49407114624 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 98814229249) ^ 49407114624 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 98814229249) ^ 49407114624 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 98814229249) ^ 49407114624 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 98814229249) ^ 49407114624 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 98814229249) ^ 32938076416 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 98814229249) ^ 14116318464 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 98814229249) ^ 152726784 ≠ 1
      reduce_mod_char
      decide
    · change (29 : ZMod 98814229249) ^ 3478272 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999953 : Nat.Prime 399999999999953 := by
  apply lucas_from_prime_list 399999999999953 (6 : ZMod 399999999999953) [2,2,2,2,11,23,98814229249]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_11
    · exact prime_23
    · exact prime_98814229249
  · decide +kernel
  · change (6 : ZMod 399999999999953) ^ 399999999999952 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 399999999999953) ^ 199999999999976 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999953) ^ 199999999999976 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999953) ^ 199999999999976 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999953) ^ 199999999999976 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999953) ^ 36363636363632 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999953) ^ 17391304347824 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 399999999999953) ^ 4048 ≠ 1
      reduce_mod_char
      decide

private lemma prime_769 : Nat.Prime 769 := by
  apply lucas_from_prime_list 769 (11 : ZMod 769) [2,2,2,2,2,2,2,2,3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
  · decide +kernel
  · change (11 : ZMod 769) ^ 768 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 769) ^ 384 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 769) ^ 384 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 769) ^ 384 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 769) ^ 384 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 769) ^ 384 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 769) ^ 384 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 769) ^ 384 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 769) ^ 384 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 769) ^ 256 ≠ 1
      reduce_mod_char
      decide

private lemma prime_2861 : Nat.Prime 2861 := by
  apply lucas_from_prime_list 2861 (2 : ZMod 2861) [2,2,5,11,13]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
  · decide +kernel
  · change (2 : ZMod 2861) ^ 2860 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2861) ^ 1430 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2861) ^ 1430 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2861) ^ 572 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2861) ^ 260 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 2861) ^ 220 ≠ 1
      reduce_mod_char
      decide

private lemma prime_353 : Nat.Prime 353 := by
  apply lucas_from_prime_list 353 (3 : ZMod 353) [2,2,2,2,2,11]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_11
  · decide +kernel
  · change (3 : ZMod 353) ^ 352 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 353) ^ 176 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 353) ^ 176 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 353) ^ 176 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 353) ^ 176 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 353) ^ 176 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 353) ^ 32 ≠ 1
      reduce_mod_char
      decide

private lemma prime_3787691 : Nat.Prime 3787691 := by
  apply lucas_from_prime_list 3787691 (2 : ZMod 3787691) [2,5,29,37,353]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_29
    · exact prime_37
    · exact prime_353
  · decide +kernel
  · change (2 : ZMod 3787691) ^ 3787690 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3787691) ^ 1893845 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3787691) ^ 757538 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3787691) ^ 130610 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3787691) ^ 102370 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 3787691) ^ 10730 ≠ 1
      reduce_mod_char
      decide

private lemma prime_30301529 : Nat.Prime 30301529 := by
  apply lucas_from_prime_list 30301529 (3 : ZMod 30301529) [2,2,2,3787691]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3787691
  · decide +kernel
  · change (3 : ZMod 30301529) ^ 30301528 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30301529) ^ 15150764 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 30301529) ^ 15150764 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 30301529) ^ 15150764 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 30301529) ^ 8 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999967 : Nat.Prime 399999999999967 := by
  apply lucas_from_prime_list 399999999999967 (3 : ZMod 399999999999967) [2,3,769,2861,30301529]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_769
    · exact prime_2861
    · exact prime_30301529
  · decide +kernel
  · change (3 : ZMod 399999999999967) ^ 399999999999966 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 399999999999967) ^ 199999999999983 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999967) ^ 133333333333322 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999967) ^ 520156046814 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999967) ^ 139811254806 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 399999999999967) ^ 13200654 ≠ 1
      reduce_mod_char
      decide

private lemma prime_499 : Nat.Prime 499 := by
  apply lucas_from_prime_list 499 (7 : ZMod 499) [2,3,83]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_83
  · decide +kernel
  · change (7 : ZMod 499) ^ 498 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (7 : ZMod 499) ^ 249 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 499) ^ 166 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 499) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_1997 : Nat.Prime 1997 := by
  apply lucas_from_prime_list 1997 (2 : ZMod 1997) [2,2,499]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_499
  · decide +kernel
  · change (2 : ZMod 1997) ^ 1996 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (2 : ZMod 1997) ^ 998 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1997) ^ 998 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 1997) ^ 4 ≠ 1
      reduce_mod_char
      decide

private lemma prime_337 : Nat.Prime 337 := by
  apply lucas_from_prime_list 337 (10 : ZMod 337) [2,2,2,2,3,7]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_7
  · decide +kernel
  · change (10 : ZMod 337) ^ 336 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 337) ^ 168 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 337) ^ 168 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 337) ^ 168 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 337) ^ 168 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 337) ^ 112 ≠ 1
      reduce_mod_char
      decide
    · change (10 : ZMod 337) ^ 48 ≠ 1
      reduce_mod_char
      decide

private lemma prime_18199 : Nat.Prime 18199 := by
  apply lucas_from_prime_list 18199 (11 : ZMod 18199) [2,3,3,3,337]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_337
  · decide +kernel
  · change (11 : ZMod 18199) ^ 18198 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 18199) ^ 9099 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 18199) ^ 6066 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 18199) ^ 6066 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 18199) ^ 6066 ≠ 1
      reduce_mod_char
      decide
    · change (11 : ZMod 18199) ^ 54 ≠ 1
      reduce_mod_char
      decide

private lemma prime_607 : Nat.Prime 607 := by
  apply lucas_from_prime_list 607 (3 : ZMod 607) [2,3,101]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_101
  · decide +kernel
  · change (3 : ZMod 607) ^ 606 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change (3 : ZMod 607) ^ 303 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 607) ^ 202 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 607) ^ 6 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999973 : Nat.Prime 399999999999973 := by
  apply lucas_from_prime_list 399999999999973 (2 : ZMod 399999999999973) [2,2,3,607,1511,1997,18199]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_607
    · exact prime_1511
    · exact prime_1997
    · exact prime_18199
  · decide +kernel
  · change (2 : ZMod 399999999999973) ^ 399999999999972 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 399999999999973) ^ 199999999999986 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999973) ^ 199999999999986 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999973) ^ 133333333333324 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999973) ^ 658978583196 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999973) ^ 264725347452 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999973) ^ 200300450676 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999973) ^ 21979229628 ≠ 1
      reduce_mod_char
      decide

private lemma prime_909091 : Nat.Prime 909091 := by
  apply lucas_from_prime_list 909091 (7 : ZMod 909091) [2,3,3,3,5,7,13,37]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_7
    · exact prime_13
    · exact prime_37
  · decide +kernel
  · change (7 : ZMod 909091) ^ 909090 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 909091) ^ 454545 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 909091) ^ 303030 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 909091) ^ 303030 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 909091) ^ 303030 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 909091) ^ 181818 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 909091) ^ 129870 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 909091) ^ 69930 ≠ 1
      reduce_mod_char
      decide
    · change (7 : ZMod 909091) ^ 24570 ≠ 1
      reduce_mod_char
      decide

private lemma prime_4649 : Nat.Prime 4649 := by
  apply lucas_from_prime_list 4649 (3 : ZMod 4649) [2,2,2,7,83]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_83
  · decide +kernel
  · change (3 : ZMod 4649) ^ 4648 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4649) ^ 2324 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4649) ^ 2324 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4649) ^ 2324 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4649) ^ 664 ≠ 1
      reduce_mod_char
      decide
    · change (3 : ZMod 4649) ^ 56 ≠ 1
      reduce_mod_char
      decide

private lemma prime_399999999999997 : Nat.Prime 399999999999997 := by
  apply lucas_from_prime_list 399999999999997 (2 : ZMod 399999999999997) [2,2,3,3,11,239,4649,909091]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_11
    · exact prime_239
    · exact prime_4649
    · exact prime_909091
  · decide +kernel
  · change (2 : ZMod 399999999999997) ^ 399999999999996 = 1
    reduce_mod_char
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 399999999999997) ^ 199999999999998 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999997) ^ 199999999999998 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999997) ^ 133333333333332 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999997) ^ 133333333333332 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999997) ^ 36363636363636 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999997) ^ 1673640167364 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999997) ^ 86040008604 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 399999999999997) ^ 439999956 ≠ 1
      reduce_mod_char
      decide

end GoldbachLucasSegmentPrimes

namespace GoldbachLucasBitmapData399999999999000_400000000000000
open GoldbachCertificate GoldbachBitmapCertificate

private def primes : PrimeTree := (.node 269 (.node 109 (.node 47 (.node 19 (.node 11 (.node 5 (.node 3 .empty .empty) (.node 7 .empty .empty)) (.node 17 (.node 13 .empty .empty) .empty)) (.node 37 (.node 29 (.node 23 .empty .empty) (.node 31 .empty .empty)) (.node 43 (.node 41 .empty .empty) .empty))) (.node 79 (.node 67 (.node 59 (.node 53 .empty .empty) (.node 61 .empty .empty)) (.node 73 (.node 71 .empty .empty) .empty)) (.node 101 (.node 89 (.node 83 .empty .empty) (.node 97 .empty .empty)) (.node 107 (.node 103 .empty .empty) .empty)))) (.node 191 (.node 151 (.node 137 (.node 127 (.node 113 .empty .empty) (.node 131 .empty .empty)) (.node 149 (.node 139 .empty .empty) .empty)) (.node 173 (.node 163 (.node 157 .empty .empty) (.node 167 .empty .empty)) (.node 181 (.node 179 .empty .empty) .empty))) (.node 229 (.node 211 (.node 197 (.node 193 .empty .empty) (.node 199 .empty .empty)) (.node 227 (.node 223 .empty .empty) .empty)) (.node 251 (.node 239 (.node 233 .empty .empty) (.node 241 .empty .empty)) (.node 263 (.node 257 .empty .empty) .empty))))) (.node 399999999998881 (.node 503 (.node 311 (.node 283 (.node 277 (.node 271 .empty .empty) (.node 281 .empty .empty)) (.node 307 (.node 293 .empty .empty) .empty)) (.node 359 (.node 347 (.node 317 .empty .empty) (.node 349 .empty .empty)) (.node 409 (.node 401 .empty .empty) .empty))) (.node 399999999998381 (.node 557 (.node 523 (.node 521 .empty .empty) (.node 541 .empty .empty)) (.node 827 (.node 811 .empty .empty) .empty)) (.node 399999999998813 (.node 399999999998773 (.node 399999999998597 .empty .empty) (.node 399999999998783 .empty .empty)) (.node 399999999998857 (.node 399999999998831 .empty .empty) .empty)))) (.node 399999999999449 (.node 399999999999143 (.node 399999999999097 (.node 399999999999007 (.node 399999999998923 .empty .empty) (.node 399999999999079 .empty .empty)) (.node 399999999999133 (.node 399999999999121 .empty .empty) .empty)) (.node 399999999999359 (.node 399999999999287 (.node 399999999999209 .empty .empty) (.node 399999999999349 .empty .empty)) (.node 399999999999427 (.node 399999999999421 .empty .empty) .empty))) (.node 399999999999683 (.node 399999999999629 (.node 399999999999517 (.node 399999999999503 .empty .empty) (.node 399999999999541 .empty .empty)) (.node 399999999999659 (.node 399999999999643 .empty .empty) .empty)) (.node 399999999999967 (.node 399999999999953 (.node 399999999999799 .empty .empty) .empty) (.node 399999999999997 (.node 399999999999973 .empty .empty) .empty))))))
private def left : List ℕ := [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,317,347,349,359,401,409,503,521,523,541,557,811,827]

private lemma primes_valid : primes.check = true := by
  simp [primes, PrimeTree.check, GoldbachCertificate.primeCheck_spec, GoldbachLucasSegmentPrimes.prime_3, GoldbachLucasSegmentPrimes.prime_5, GoldbachLucasSegmentPrimes.prime_7, GoldbachLucasSegmentPrimes.prime_11, GoldbachLucasSegmentPrimes.prime_13, GoldbachLucasSegmentPrimes.prime_17, GoldbachLucasSegmentPrimes.prime_19, GoldbachLucasSegmentPrimes.prime_23, GoldbachLucasSegmentPrimes.prime_29, GoldbachLucasSegmentPrimes.prime_31, GoldbachLucasSegmentPrimes.prime_37, GoldbachLucasSegmentPrimes.prime_41, GoldbachLucasSegmentPrimes.prime_43, GoldbachLucasSegmentPrimes.prime_47, GoldbachLucasSegmentPrimes.prime_53, GoldbachLucasSegmentPrimes.prime_59, GoldbachLucasSegmentPrimes.prime_61, GoldbachLucasSegmentPrimes.prime_67, GoldbachLucasSegmentPrimes.prime_71, GoldbachLucasSegmentPrimes.prime_73, GoldbachLucasSegmentPrimes.prime_79, GoldbachLucasSegmentPrimes.prime_83, GoldbachLucasSegmentPrimes.prime_89, GoldbachLucasSegmentPrimes.prime_97, GoldbachLucasSegmentPrimes.prime_101, GoldbachLucasSegmentPrimes.prime_103, GoldbachLucasSegmentPrimes.prime_107, GoldbachLucasSegmentPrimes.prime_109, GoldbachLucasSegmentPrimes.prime_113, GoldbachLucasSegmentPrimes.prime_127, GoldbachLucasSegmentPrimes.prime_131, GoldbachLucasSegmentPrimes.prime_137, GoldbachLucasSegmentPrimes.prime_139, GoldbachLucasSegmentPrimes.prime_149, GoldbachLucasSegmentPrimes.prime_151, GoldbachLucasSegmentPrimes.prime_157, GoldbachLucasSegmentPrimes.prime_163, GoldbachLucasSegmentPrimes.prime_167, GoldbachLucasSegmentPrimes.prime_173, GoldbachLucasSegmentPrimes.prime_179, GoldbachLucasSegmentPrimes.prime_181, GoldbachLucasSegmentPrimes.prime_191, GoldbachLucasSegmentPrimes.prime_193, GoldbachLucasSegmentPrimes.prime_197, GoldbachLucasSegmentPrimes.prime_199, GoldbachLucasSegmentPrimes.prime_211, GoldbachLucasSegmentPrimes.prime_223, GoldbachLucasSegmentPrimes.prime_227, GoldbachLucasSegmentPrimes.prime_229, GoldbachLucasSegmentPrimes.prime_233, GoldbachLucasSegmentPrimes.prime_239, GoldbachLucasSegmentPrimes.prime_241, GoldbachLucasSegmentPrimes.prime_251, GoldbachLucasSegmentPrimes.prime_257, GoldbachLucasSegmentPrimes.prime_263, GoldbachLucasSegmentPrimes.prime_269, GoldbachLucasSegmentPrimes.prime_271, GoldbachLucasSegmentPrimes.prime_277, GoldbachLucasSegmentPrimes.prime_281, GoldbachLucasSegmentPrimes.prime_283, GoldbachLucasSegmentPrimes.prime_293, GoldbachLucasSegmentPrimes.prime_307, GoldbachLucasSegmentPrimes.prime_311, GoldbachLucasSegmentPrimes.prime_317, GoldbachLucasSegmentPrimes.prime_347, GoldbachLucasSegmentPrimes.prime_349, GoldbachLucasSegmentPrimes.prime_359, GoldbachLucasSegmentPrimes.prime_401, GoldbachLucasSegmentPrimes.prime_409, GoldbachLucasSegmentPrimes.prime_503, GoldbachLucasSegmentPrimes.prime_521, GoldbachLucasSegmentPrimes.prime_523, GoldbachLucasSegmentPrimes.prime_541, GoldbachLucasSegmentPrimes.prime_557, GoldbachLucasSegmentPrimes.prime_811, GoldbachLucasSegmentPrimes.prime_827, GoldbachLucasSegmentPrimes.prime_399999999998381, GoldbachLucasSegmentPrimes.prime_399999999998597, GoldbachLucasSegmentPrimes.prime_399999999998773, GoldbachLucasSegmentPrimes.prime_399999999998783, GoldbachLucasSegmentPrimes.prime_399999999998813, GoldbachLucasSegmentPrimes.prime_399999999998831, GoldbachLucasSegmentPrimes.prime_399999999998857, GoldbachLucasSegmentPrimes.prime_399999999998881, GoldbachLucasSegmentPrimes.prime_399999999998923, GoldbachLucasSegmentPrimes.prime_399999999999007, GoldbachLucasSegmentPrimes.prime_399999999999079, GoldbachLucasSegmentPrimes.prime_399999999999097, GoldbachLucasSegmentPrimes.prime_399999999999121, GoldbachLucasSegmentPrimes.prime_399999999999133, GoldbachLucasSegmentPrimes.prime_399999999999143, GoldbachLucasSegmentPrimes.prime_399999999999209, GoldbachLucasSegmentPrimes.prime_399999999999287, GoldbachLucasSegmentPrimes.prime_399999999999349, GoldbachLucasSegmentPrimes.prime_399999999999359, GoldbachLucasSegmentPrimes.prime_399999999999421, GoldbachLucasSegmentPrimes.prime_399999999999427, GoldbachLucasSegmentPrimes.prime_399999999999449, GoldbachLucasSegmentPrimes.prime_399999999999503, GoldbachLucasSegmentPrimes.prime_399999999999517, GoldbachLucasSegmentPrimes.prime_399999999999541, GoldbachLucasSegmentPrimes.prime_399999999999629, GoldbachLucasSegmentPrimes.prime_399999999999643, GoldbachLucasSegmentPrimes.prime_399999999999659, GoldbachLucasSegmentPrimes.prime_399999999999683, GoldbachLucasSegmentPrimes.prime_399999999999799, GoldbachLucasSegmentPrimes.prime_399999999999953, GoldbachLucasSegmentPrimes.prime_399999999999967, GoldbachLucasSegmentPrimes.prime_399999999999973, GoldbachLucasSegmentPrimes.prime_399999999999997]

private lemma left_valid : leftCheck 5569 primes left = true := by decide +kernel
private lemma coverage_valid : covers 199999999996715 2785 501 primes left = true := by decide +kernel

end GoldbachLucasBitmapData399999999999000_400000000000000

theorem solution (n : ℕ) (hlo : 399999999999000 ≤ n) (hhi : n ≤ 400000000000000) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ 5569 ∧ n = p + q := by
  exact GoldbachBitmapCertificate.block_sound 199999999996715 2785 501 5569
    GoldbachLucasBitmapData399999999999000_400000000000000.primes GoldbachLucasBitmapData399999999999000_400000000000000.left GoldbachLucasBitmapData399999999999000_400000000000000.primes_valid
    GoldbachLucasBitmapData399999999999000_400000000000000.left_valid GoldbachLucasBitmapData399999999999000_400000000000000.coverage_valid n (by omega) (by omega) he

#print axioms solution
