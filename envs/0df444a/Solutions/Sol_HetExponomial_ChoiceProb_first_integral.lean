-- Prove2me | solution 1 for HetExponomial.ChoiceProb.first_integral
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:34:39.749976+00:00
-- url     : https://prove2.me/submissions/5b5a1149-cca4-46ae-bf32-1ecbe3c33524

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

open MeasureTheory

open HetExponomial.ChoiceProb in
theorem solution {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i : Fin n) :
    lam i * tailInt u lam i (u i) 0 = G u lam i := by
  have hL : 0 < Lsum u lam i :=
    Finset.sum_pos (fun j _ => hlam j) ⟨i, by simp [better, betterThan]⟩
  have hsum : ∀ z : ℝ, ∑ j ∈ betterThan u (u i), lam j * (u j - u i + z) =
      ∑ j ∈ better u i, lam j * (u j - u i) + Lsum u lam i * z := by
    intro z
    unfold Lsum better
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hint : ∀ z : ℝ, Real.exp (-(∑ j ∈ betterThan u (u i), lam j * (u j - u i + z))) =
      Real.exp (-(∑ j ∈ better u i, lam j * (u j - u i))) * Real.exp ((-Lsum u lam i) * z) := by
    intro z
    rw [hsum z, ← Real.exp_add]
    congr 1
    ring
  unfold tailInt G
  simp_rw [hint]
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hL) 0, mul_zero,
    Real.exp_zero, neg_div_neg_eq]
  ring
