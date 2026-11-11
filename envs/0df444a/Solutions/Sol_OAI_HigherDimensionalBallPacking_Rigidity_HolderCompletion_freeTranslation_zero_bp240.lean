-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTranslation_zero_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:54:53.443729+00:00
-- url     : https://prove2.me/submissions/54c032ab-3592-44e3-acba-0748b872cd6d

import Mathlib
import Definitions.Def_OAIQ240Bp020

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTransInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTransInst2
local instance freeTransInst3_r593253_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeTransInst4_r593253_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma translationVariation_zero [CompleteSpace E] (a : E) (u : COne ℂ E) : translationVariation a u 0=0 := by
  apply cValue_ext
  intro z
  simp only [translationVariation_value,zero_smul,zero_add,add_zero,sub_self]
  rfl

variable {R S : ℝ} (hRS : R+1 ≤ S) (a : E)
  (u : freeModel (E := E) (Metric.closedBall (0:ℂ) R))

local instance freeTransInst5_r593253_1 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance freeTransInst6_r593253_1 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
lemma freeTranslation_near : ∀ᶠ t in 𝓝 (0:ℂ), (freeTranslation hRS a u t).val=translationVariation a u.val t := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (show (0:ℝ)<1 by norm_num)] with t ht
  have ht' : ‖t‖≤1 := (show ‖t‖<1 by simpa only [Metric.mem_ball,dist_zero_right] using ht).le
  simp only [freeTranslation,dite_eq_left ht']

@[simp] lemma freeTranslation_zero_bp240_oai : freeTranslation hRS a u 0=0 := by
  apply Subtype.ext
  exact freeTranslation_near hRS a u |>.self_of_nhds |>.trans (translationVariation_zero a u.val)

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTranslation_zero_bp240_oai.{u_1} := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTranslation_zero_bp240_oai.{u_1}
