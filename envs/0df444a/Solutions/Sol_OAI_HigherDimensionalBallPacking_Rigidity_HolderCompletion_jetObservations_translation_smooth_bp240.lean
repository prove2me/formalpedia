-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObservations_translation_smooth_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:54:57.018586+00:00
-- url     : https://prove2.me/submissions/73ff9c0b-78af-404a-aa3e-4834b5162c00

import Mathlib
import Definitions.Def_OAIQ240Bp021

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 theorem compact_test_translation_smooth {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) {v : ℂ → E} (hv : LocallyIntegrable v) :
    ContDiff ℝ ∞ (fun t : ℂ => ∫ z : ℂ, g z • v (z+t)) := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  have hs : ContDiff ℝ ∞ (fun z : ℂ => g (-z)) := hg.comp contDiff_neg
  have hc : HasCompactSupport (fun z : ℂ => g (-z)) := hgc.comp_homeomorph (Homeomorph.neg ℂ)
  have hh := hc.contDiff_convolution_left (𝕜 := ℝ) (μ := (volume : Measure ℂ)) L hs hv
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  rw [convolution_def,←integral_neg_eq_self]
  congr 1
  funext z
  change g (-z) • v (-z+t)=g (-z) • v (t-z)
  rw [neg_add_eq_sub]


end
section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter MeasureTheory
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.testInst1
local instance testInst2_r3d3d3d_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
lemma jetTest_translation_smooth (g : PlaneTest) (u : COne ℂ E) :
    ContDiff ℝ ∞ (fun t => jetTestCLM g (jetTranslate t u)) := by
  simp only [jetTest_value,jetTranslate_value]
  exact compact_test_translation_smooth g.property.1 g.property.2 (cValue u).continuous.locallyIntegrable

lemma jetTest_translation_difference_smooth (g : PlaneTest) (u : COne ℂ E) :
    ContDiff ℝ ∞ (fun t => jetTestCLM g (jetTranslate t u-u)) := by
  simp_rw [map_sub]
  exact (jetTest_translation_smooth g u).sub contDiff_const

end HolderCompletion

end
section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter
namespace HolderCompletion
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst2
omit [FiniteDimensional ℝ E] in
lemma jetObservations_translation_smooth_bp240_oai [FiniteDimensional ℝ E] (s : Finset PlaneTest) (u : COne ℂ E) :
    ContDiff ℝ ∞ (fun t => jetObservations s (jetTranslate t u-u)) :=
  contDiff_pi.mpr (fun g => jetTest_translation_difference_smooth g.val u)

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObservations_translation_smooth_bp240_oai.{u_1} := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObservations_translation_smooth_bp240_oai.{u_1}
