-- Prove2me | solution 1 for HlawkaGaussian.gaussAbsConst_pos
-- status  : ACCEPTED   (prove)
-- author  : @sorry_not_sorry
-- created : 2026-10-08T06:40:49.795625+00:00
-- url     : https://prove2.me/submissions/bd9cad36-c96c-4824-a6ee-c265a2f41487

import Mathlib

open MeasureTheory ProbabilityTheory

/-- Positivity of the Gaussian absolute first moment:
`C = ∫ |t| ∂(gaussianReal 0 1) > 0`.
If `C = 0`, then `|·| = 0` a.e.-`N(0,1)` (by `integral_eq_zero_iff_of_nonneg_ae`),
so the identity is `0` a.e. and the variance — written as an integral via
`variance_eq_integral` with mean `0` — vanishes. But `variance_id_gaussianReal`
says the variance is `1`, a contradiction. -/
theorem solution : 0 < ∫ t, |t| ∂(gaussianReal 0 1) := by
  by_contra h
  push_neg at h
  have hint : Integrable (fun t : ℝ => |t|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal 1).integrable (by simp)).abs
  have h0 : ∫ t, |t| ∂(gaussianReal 0 1) = 0 :=
    le_antisymm h (integral_nonneg fun _ => abs_nonneg _)
  have hae : (fun t : ℝ => |t|) =ᵐ[gaussianReal 0 1] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ => abs_nonneg _) hint).mp h0
  have hae0 : ∀ᵐ t ∂(gaussianReal 0 1), t = 0 :=
    hae.mono fun t ht => abs_eq_zero.mp ht
  have hvar : Var[id; gaussianReal 0 1] = 0 := by
    rw [variance_eq_integral (by fun_prop)]
    simp only [id_eq, integral_id_gaussianReal]
    apply integral_eq_zero_of_ae
    filter_upwards [hae0] with t ht
    simp [ht]
  rw [variance_id_gaussianReal] at hvar
  simpa using hvar
