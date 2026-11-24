-- Prove2me | solution 1 for Kyprianou.Ch02.complexLaplaceAffineIntegralDifferentiableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:00:24.028971+00:00
-- url     : https://prove2.me/submissions/c928352b-929d-4aeb-a30b-2ec3b1448523

import Theorems.Thm_Kyprianou_Ch02_complexLaplaceAffineKernelDerivativeV1
import Theorems.Thm_Kyprianou_Ch02_complexLaplaceAffineKernelDerivativeBoundV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution
    (μ : Measure ℝ) (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|) μ)
    (a b : ℂ)
    (hi : ∀ z : ℂ, 0 < z.re →
      Integrable (fun x : ℝ => a + b * Complex.exp (-z * (x : ℂ))) μ) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ x, a + b * Complex.exp (-z * (x : ℂ)) ∂μ)
      {z : ℂ | 0 < z.re} := by
  intro z hz
  change 0 < z.re at hz
  let r : ℝ := z.re / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let U : Set ℂ := {w | r < w.re}
  have hU : U ∈ nhds z := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by change r < z.re; dsimp [r]; linarith)
  let F (w : ℂ) (x : ℝ) := a + b * Complex.exp (-w * (x : ℂ))
  let F' (w : ℂ) (x : ℝ) := b * (-(x : ℂ)) * Complex.exp (-w * (x : ℂ))
  have hbound : ∀ᵐ x ∂μ, ∀ w ∈ U, ‖F' w x‖ ≤
      (‖b‖ * max 1 (1/r)) * min 1 |x| :=
    hpos.mono fun x hx w hw =>
      Kyprianou.Ch02.complexLaplaceAffineKernelDerivativeBoundV1 b r hr w
        (le_of_lt hw) x hx
  have hdiff : ∀ᵐ x ∂μ, ∀ w ∈ U, HasDerivAt (F · x) (F' w x) w :=
    Eventually.of_forall fun x w _ => Kyprianou.Ch02.complexLaplaceAffineKernelDerivativeV1 a b w x
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU
    (Eventually.of_forall fun w => (show Continuous (F w) by dsimp [F]; fun_prop).aestronglyMeasurable)
    (hi z hz) ((show Continuous (F' z) by dsimp [F']; fun_prop).aestronglyMeasurable)
    hbound (hint.const_mul _) hdiff).2.differentiableAt.differentiableWithinAt
