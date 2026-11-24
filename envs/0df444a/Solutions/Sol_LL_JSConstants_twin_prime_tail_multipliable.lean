-- Prove2me | solution 1 for LL_JSConstants.twin_prime_tail_multipliable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T23:33:30.090265+00:00
-- url     : https://prove2.me/submissions/d7d1a132-8618-4b6d-b2af-e92ad46b1922

import Mathlib

theorem solution :
    Multipliable (fun x : ((((Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p) :
        Finset {p : ℕ // p.Prime ∧ 2 < p}) : Set {p : ℕ // p.Prime ∧ 2 < p})ᶜ :
        Set {p : ℕ // p.Prime ∧ 2 < p}) =>
      (1 - 1 / ((((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) : ℝ) - 1) ^ 2)) := by
  let f : ((((Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p) :
      Finset {p : ℕ // p.Prime ∧ 2 < p}) : Set {p : ℕ // p.Prime ∧ 2 < p})ᶜ :
      Set {p : ℕ // p.Prime ∧ 2 < p}) → ℝ :=
    fun x => -(1 / ((((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) : ℝ) - 1) ^ 2)
  have hinj : Function.Injective (fun x :
      ((((Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p) :
        Finset {p : ℕ // p.Prime ∧ 2 < p}) : Set {p : ℕ // p.Prime ∧ 2 < p})ᶜ :
        Set {p : ℕ // p.Prime ∧ 2 < p}) =>
      (((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) - 1)) := by
    intro x y hxy
    dsimp only at hxy
    have hx2 : 2 < ((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) := x.1.2.2
    have hy2 : 2 < ((y : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) := y.1.2.2
    have hval : ((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) =
        ((y : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) := by omega
    exact Subtype.ext (Subtype.ext hval)
  have hsum_nat : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
    simp [one_div]
  have hsum_comp : Summable (fun x :
      ((((Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p) :
        Finset {p : ℕ // p.Prime ∧ 2 < p}) : Set {p : ℕ // p.Prime ∧ 2 < p})ᶜ :
        Set {p : ℕ // p.Prime ∧ 2 < p}) =>
      1 / ((((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) - 1 : ℕ) : ℝ) ^ 2) :=
    hsum_nat.comp_injective hinj
  have hsum_pos : Summable (fun x => -f x) := by
    refine hsum_comp.congr fun x => ?_
    have hx1 : 1 ≤ ((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) := by
      have := x.1.2.2; omega
    simp [f, Nat.cast_sub hx1]
  have hf : Summable f := by
    simpa using hsum_pos.neg
  simpa [f, sub_eq_add_neg] using Real.multipliable_one_add_of_summable hf
