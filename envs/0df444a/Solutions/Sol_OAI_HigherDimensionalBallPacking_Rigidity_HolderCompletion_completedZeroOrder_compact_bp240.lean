-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder_compact_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:53:51.708743+00:00
-- url     : https://prove2.me/submissions/ae686542-8bc2-4cbc-a59a-6a41f3a7b85f

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp018
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_compact_subset_bump_inner_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_jetZeroOrder_isCompact_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_supportedHolder_closed_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FiniteExtensions
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [completeSpaceE : CompleteSpace E]

variable {K : Set ℂ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroOrderInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroOrderInst2
local instance zeroOrderInst3_r0e58ad_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance zeroOrderInst4_r0e58ad_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance zeroOrderInst5_r0e58ad_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance zeroOrderInst6_r0e58ad_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance zeroOrderInst7_r0e58ad_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance zeroOrderInst8_r0e58ad_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance zeroOrderInst9_r0e58ad_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance zeroOrderInst10_r0e58ad_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
lemma markedZeroOrder_isCompact [ProperSpace E] (C : HMap ℂ (E →L[ℝ] E))
    (hC : ∀ z ∉ K, valueCLM _ C z = 0) (b : ContDiffBump (0:ℂ))
    (hCb : ∀ z ∉ Metric.closedBall (0:ℂ) b.rIn, valueCLM _ C z = 0) :
    IsCompactOperator (markedZeroOrder C hC) := by
  have hc := (jetZeroOrder_isCompact_bp240 C b hCb).comp_clm (markedModel (E := E) K).subtypeL
  exact hc.codRestrict (fun u => by
    apply (mem_supportedHolder _ K).mpr
    intro z hz
    change valueCLM _ C z (cValue u.val z) = 0
    rw [hC z hz,zero_apply]) (supportedHolder_closed_bp240 K)

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_CompactFredholmAlternative
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma markedZeroOrder_isCompact_of_compact [ProperSpace E] {K : Set ℂ} (hK : IsCompact K)
    (C : HMap ℂ (E →L[ℝ] E)) (hC : ∀ z ∉ K, valueCLM _ C z = 0) :
    IsCompactOperator (markedZeroOrder C hC) := by
  obtain ⟨b,hb⟩ := compact_subset_bump_inner_bp240 hK
  exact markedZeroOrder_isCompact C hC b (fun z hz => hC z (fun hzK => hz (hb hzK)))

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_PointwiseMarkedCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst5
local instance compLinInst6_r0e58ad_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst7
local instance compLinInst8_r0e58ad_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance compLinInst9_r0e58ad_1 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance compLinInst10_r0e58ad_1 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))

variable {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)

variable (b : ContDiffBump (0:ℂ)) (hb : K ⊆ Metric.closedBall (0:ℂ) b.rIn)

local instance compLinInst11_r0e58ad_1 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance compLinInst12_r0e58ad_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance compLinInst13_r0e58ad_1 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance compLinInst14_r0e58ad_1 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
include hK in
lemma completedZeroOrder_compact_bp240_oai : IsCompactOperator (completedZeroOrder hJ hstd p q u he) :=
  markedZeroOrder_isCompact_of_compact (E := Phase n) hK _ _


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder_compact_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedZeroOrder_compact_bp240_oai
