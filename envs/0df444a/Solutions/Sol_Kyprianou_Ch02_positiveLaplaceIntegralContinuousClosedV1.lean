-- Prove2me | solution 1 for Kyprianou.Ch02.positiveLaplaceIntegralContinuousClosedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:57:03.613455+00:00
-- url     : https://prove2.me/submissions/32a135c6-d3d6-4380-ac77-c804ca82e45c

import Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelUniformBoundV1
import Theorems.Thm_Kyprianou_Ch02_complexLaplaceDerivativeUniformBoundV1
import Theorems.Thm_Kyprianou_Ch02_positiveComplexLaplaceKernelIntegrableV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) :
    ContinuousOn (fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ),
      (1 - Complex.exp (-z * (x : ℂ))) ∂ν) {z : ℂ | 0 ≤ z.re} := by
  let μ := ν.restrict (Set.Ioi (0 : ℝ))
  let F (z : ℂ) (x : ℝ) : ℂ := 1 - Complex.exp (-z * (x : ℂ))
  let F' (z : ℂ) (x : ℝ) : ℂ := (x : ℂ) * Complex.exp (-z * (x : ℂ))
  have hmeas (z : ℂ) : AEStronglyMeasurable (F z) μ :=
    (show Continuous (F z) by dsimp [F]; fun_prop).aestronglyMeasurable
  have hmeas' (z : ℂ) : AEStronglyMeasurable (F' z) μ :=
    (show Continuous (F' z) by dsimp [F']; fun_prop).aestronglyMeasurable
  intro z hz
  apply continuousWithinAt_of_dominated
    (bound := fun x : ℝ => 2 * max 1 (‖z‖ + 1) * min 1 |x|)
  · exact Eventually.of_forall hmeas
  · have hnear : ∀ᶠ w in nhdsWithin z {w : ℂ | 0 ≤ w.re}, ‖w‖ < ‖z‖ + 1 :=
      nhdsWithin_le_nhds (continuous_norm.continuousAt.eventually
        (Iio_mem_nhds (by linarith : ‖z‖ < ‖z‖ + 1)))
    filter_upwards [self_mem_nhdsWithin, hnear] with w hw hn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hb := Kyprianou.Ch02.complexLaplaceKernelUniformBoundV1 w hw x hx.le
    have hm : max 1 ‖w‖ ≤ max 1 (‖z‖+1) := max_le_max le_rfl hn.le
    exact hb.trans (by gcongr)
  · exact hint.const_mul _
  · exact Eventually.of_forall fun x =>
      (show Continuous (fun w => F w x) by dsimp [F]; fun_prop).continuousWithinAt
