-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegativeLawLaplaceContinuousClosedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:00:48.638491+00:00
-- url     : https://prove2.me/submissions/80b38a62-5493-4784-8c70-bc91bd93d635

import Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelNormLeOneV1
import Theorems.Thm_Kyprianou_Ch02_complexLaplaceDerivativeUniformBoundV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q (Set.Iio (0 : ℝ)) = 0) :
    ContinuousOn (fun z : ℂ => ∫ x, Complex.exp (-z * (x : ℂ)) ∂Q) {z : ℂ | 0 ≤ z.re} := by
  have hpos : ∀ᵐ x ∂Q, 0 ≤ x := by
    rw [ae_iff]
    have he : {x : ℝ | ¬ 0 ≤ x} = Set.Iio 0 := by ext x; simp [not_le]
    rw [he, hQ]
  let F (z : ℂ) (x : ℝ) : ℂ := Complex.exp (-z * (x : ℂ))
  let F' (z : ℂ) (x : ℝ) : ℂ := -(x : ℂ) * F z x
  have hmeas (z : ℂ) : AEStronglyMeasurable (F z) Q :=
    (show Continuous (F z) by dsimp [F]; fun_prop).aestronglyMeasurable
  have hnorm (z : ℂ) (hz : 0 ≤ z.re) : ∀ᵐ x ∂Q, ‖F z x‖ ≤ 1 :=
    hpos.mono fun x hx => Kyprianou.Ch02.complexLaplaceKernelNormLeOneV1 z hz x hx
  apply continuousOn_of_dominated (bound := fun _ : ℝ => 1)
  · exact fun z _ => hmeas z
  · exact fun z hz => hnorm z hz
  · exact integrable_const _
  · exact Eventually.of_forall fun x =>
      (show Continuous (fun w => F w x) by dsimp [F]; fun_prop).continuousOn
