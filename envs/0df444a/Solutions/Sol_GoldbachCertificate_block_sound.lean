-- Prove2me | solution 1 for GoldbachCertificate.block_sound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T00:33:42.490727+00:00
-- url     : https://prove2.me/submissions/c0b78346-f46d-45f0-b06b-345055d01c8f

import Definitions.Def_GoldbachCertificate
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false

namespace GoldbachCertificate

lemma primeCheck_spec (p : ℕ) : primeCheck p = true ↔ Nat.Prime p := by
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

lemma PrimeTree.contains_prime (tree : PrimeTree) (n : ℕ)
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

lemma rows_sound (rows : List (ℕ × ℕ)) (tree : PrimeTree)
    (ht : tree.check = true) :
    ∀ first smallBound : ℕ, checkRows first smallBound tree rows = true →
      ∀ n : ℕ, 2 * first ≤ n → n < 2 * (first + rows.length) → Even n →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ smallBound ∧ n = p + q := by
  induction rows with
  | nil =>
    intro first smallBound h n hlo hhi he
    simp only [List.length_nil, Nat.add_zero] at hhi
    omega
  | cons row rows ih =>
    rcases row with ⟨p, q⟩
    intro first smallBound h n hlo hhi he
    simp only [checkRows, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hn : n = 2 * first
    · exact ⟨p, q, tree.contains_prime p ht h.1.1.1.1,
        tree.contains_prime q ht h.1.1.1.2, h.1.1.2, hn.trans h.1.2.symm⟩
    · rcases he with ⟨k, hk⟩
      have hlo' : 2 * (first + 1) ≤ n := by omega
      have hhi' : n < 2 * (first + 1 + rows.length) := by
        simp only [List.length_cons] at hhi
        omega
      exact ih (first + 1) smallBound h.2 n hlo' hhi' ⟨k, hk⟩

end GoldbachCertificate

theorem solution (first smallBound : ℕ) (tree : GoldbachCertificate.PrimeTree)
    (rows : List (ℕ × ℕ)) (ht : tree.check = true)
    (hr : GoldbachCertificate.checkRows first smallBound tree rows = true)
    (n : ℕ) (hlo : 2 * first ≤ n) (hhi : n < 2 * (first + rows.length))
    (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ smallBound ∧ n = p + q := by
  exact GoldbachCertificate.rows_sound rows tree ht first smallBound hr n hlo hhi he

#print axioms solution
