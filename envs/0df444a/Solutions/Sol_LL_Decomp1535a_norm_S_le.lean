-- Prove2me | solution 1 for LL_Decomp1535a.norm_S_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:04:57.599129+00:00
-- url     : https://prove2.me/submissions/a3adcd15-88e9-41d5-8a55-60828a8c4e36

import Mathlib
import Definitions.Def_LL_Decomp1535a_S
import Definitions.Def_LL_Decomp1535a_theta

open MeasureTheory

noncomputable def GbAAux.thetaA (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p

theorem GbAAux.norm_S_le (N : ℕ) (α : ℝ) : ‖LL_Decomp1535a.S N α‖ ≤ GbAAux.thetaA N := by
  unfold LL_Decomp1535a.S GbAAux.thetaA
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg p),
    Complex.norm_exp]
  simp

theorem solution (N : ℕ) (α : ℝ) :
    ‖LL_Decomp1535a.S N α‖ ≤ LL_Decomp1535a.theta N :=
  GbAAux.norm_S_le N α
