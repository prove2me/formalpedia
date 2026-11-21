-- Prove2me | solution 1 for MasulloRH.strip_jet_rank_one_traceNorm_sq_integral
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:22:59.519172+00:00
-- url     : https://prove2.me/submissions/71fef4f3-8167-4f03-b919-e033fdf3ce8c

import Theorems.Thm_MasulloRH_lifted_rank_one_schatten_norms
import Definitions.Def_MasulloRH_WeightedStripJetSpace

open MeasureTheory MasulloRH MasulloGRH InnerProductSpace

theorem solution (b p : ℝ) (z : ℂ) (m : ℕ)
    (A : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (v η : Lp ℂ 2 (volume : Measure ℝ))
    (hη : (η : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
      (rationalStripWeight b p x : ℂ) * (x : ℂ) ^ m * Complex.exp ((z - 1/2) * x)) :
    traceNorm (rankOne ℂ (A v) η) ^ 2 =
      ‖A v‖ ^ 2 * ∫ x : ℝ,
        (|rationalStripWeight b p x| * |x| ^ m * Real.exp ((z.re - 1/2) * x)) ^ 2 := by
  rw [(lifted_rank_one_schatten_norms (A v) η).1, mul_pow]
  congr 1
  calc
    ‖η‖ ^ 2 = inner ℝ η η := (real_inner_self_eq_norm_sq η).symm
    _ = ∫ x : ℝ, inner ℝ (η x) (η x) := L2.inner_def _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hη] with x hx
      rw [real_inner_self_eq_norm_sq, hx]
      simp [Complex.norm_exp, Complex.mul_re, Complex.sub_re, Real.norm_eq_abs]
