-- Prove2me | solution 1 for GoldbachBitmapCertificate.block_sound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T01:02:28.108145+00:00
-- url     : https://prove2.me/submissions/5cf76d3b-d51d-4396-9958-1bedb69cef18

import Definitions.Def_GoldbachBitmapCertificate
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

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

theorem solution (base first count smallBound : ℕ) (tree : GoldbachCertificate.PrimeTree)
    (left : List ℕ) (ht : tree.check = true)
    (hl : GoldbachBitmapCertificate.leftCheck smallBound tree left = true)
    (hc : GoldbachBitmapCertificate.covers base first count tree left = true)
    (n : ℕ) (hlo : 2 * (base + first) ≤ n)
    (hhi : n < 2 * (base + first + count)) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ smallBound ∧ n = p + q := by
  exact GoldbachBitmapCertificate.block_sound base first count smallBound tree left ht hl hc n hlo hhi he

#print axioms solution
