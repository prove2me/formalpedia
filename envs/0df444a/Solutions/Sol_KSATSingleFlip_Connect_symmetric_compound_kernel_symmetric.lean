-- Prove2me | solution 1 for KSATSingleFlip.Connect.symmetric_compound_kernel_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:00:27.424241+00:00
-- url     : https://prove2.me/submissions/1cab99a6-c50e-4b6f-b5c9-6a5131f94180

import Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_probability
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measure.map (fun z : ℝ => -z) (compoundPoisson μ ∗ Measure.map (fun z : ℝ => -z) (compoundPoisson μ)) =
      compoundPoisson μ ∗ Measure.map (fun z : ℝ => -z) (compoundPoisson μ) := by
  let P := compoundPoisson μ
  letI : IsProbabilityMeasure P := ⟨compound_poisson_probability μ⟩
  let Q := Measure.map (fun z : ℝ => -z) P
  letI : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (by fun_prop)
  let L : ℝ →+ ℝ := { toFun := fun z => -z, map_zero' := by simp, map_add' := by intros; simp [neg_add, add_comm] }
  have hdouble : Measure.map (fun z : ℝ => -z) Q = P := by
    dsimp [Q]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simpa [Function.comp_def] using (Measure.map_id' : Measure.map (fun z : ℝ => z) P = P)
  change Measure.map L (P ∗ Q) = P ∗ Q
  rw [Measure.map_conv_addMonoidHom L (by dsimp [L]; fun_prop)]
  change Q ∗ Measure.map (fun z : ℝ => -z) Q = P ∗ Q
  rw [hdouble, Measure.conv_comm]
