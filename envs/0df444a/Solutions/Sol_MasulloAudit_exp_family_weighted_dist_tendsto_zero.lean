-- Prove2me | solution 1 for MasulloAudit.exp_family_weighted_dist_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:32:27.35992+00:00
-- url     : https://prove2.me/submissions/026c771c-6da6-4f11-bdd5-342b02b7a9b1

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic

open Filter Topology MeasureTheory

/-- For an integrable nonnegative weight `w`, the weighted squared distance
`∫ ‖e^{itu} - e^{isu}‖² w(u) du` tends to `0` as `s → t`. -/
theorem solution (w : ℝ → ℝ) (hw : Integrable w) (hw0 : ∀ u, 0 ≤ w u) (t : ℝ) :
    Tendsto (fun s : ℝ => ∫ u : ℝ,
        ‖Complex.exp (Complex.I * t * u) - Complex.exp (Complex.I * s * u)‖ ^ 2 * w u)
      (𝓝 t) (𝓝 0) := by
  set F : ℝ → ℝ → ℝ := fun s u =>
    ‖Complex.exp (Complex.I * t * u) - Complex.exp (Complex.I * s * u)‖ ^ 2 * w u with hF
  have hcont : ∀ s, Continuous (fun u : ℝ =>
      ‖Complex.exp (Complex.I * t * u) - Complex.exp (Complex.I * s * u)‖ ^ 2) := by
    intro s; fun_prop
  have hlim : (0 : ℝ) = ∫ u : ℝ, F t u := by simp [hF]
  rw [hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun u => 4 * w u) ?_ ?_
    (hw.const_mul 4) ?_
  · exact Eventually.of_forall fun s =>
      ((hcont s).aestronglyMeasurable).mul hw.aestronglyMeasurable
  · refine Eventually.of_forall fun s => Eventually.of_forall fun u => ?_
    have hnorm : ‖Complex.exp (Complex.I * t * u) - Complex.exp (Complex.I * s * u)‖ ≤ 2 := by
      calc _ ≤ ‖Complex.exp (Complex.I * t * u)‖ + ‖Complex.exp (Complex.I * s * u)‖ :=
            norm_sub_le _ _
        _ = 2 := by
          rw [show Complex.I * t * u = ((t * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
            show Complex.I * s * u = ((s * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]; norm_num
    have hsq : ‖Complex.exp (Complex.I * t * u) - Complex.exp (Complex.I * s * u)‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg (Complex.exp (Complex.I * t * u) - Complex.exp (Complex.I * s * u))]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hw0 u))]
    exact mul_le_mul_of_nonneg_right hsq (hw0 u)
  · refine Eventually.of_forall fun u => ?_
    have : Continuous (fun s : ℝ => F s u) := by simp only [hF]; fun_prop
    exact this.tendsto t

