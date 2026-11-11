-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_fredholm_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:54:49.576607+00:00
-- url     : https://prove2.me/submissions/d44e42d0-adc9-4712-ae04-4395304375f6

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020
import Definitions.Def_OAIQ240Bp021
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualMarkedChart_derivative_eq_linearized_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_compact_subset_bump_inner_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedPrincipal_add_compact_fredholm_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedZeroOrder_compact_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FrameFredholm
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markFiniteInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markFiniteInst2
local instance markFiniteInst3_r1cb68e_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markFiniteInst4_r1cb68e_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markFiniteInst5_r1cb68e_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markFiniteInst6_r1cb68e_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markFiniteInst7_r1cb68e_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markFiniteInst8_r1cb68e_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markFiniteInst9_r1cb68e_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markFiniteInst10_r1cb68e_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
omit [CompleteSpace E] in
lemma markedFiniteCorrection_isCompact [CompleteSpace E] [FiniteDimensional ℝ E]
    (B : HMap ℂ (E →L[ℝ] E)) (hB : ∀ z ∉ K, valueCLM _ B z = 0) :
    IsCompactOperator (markedFiniteCorrection B hB) := by
  have hc : IsCompactOperator (ContinuousLinearMap.id ℝ E) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)).mpr inferInstance
  exact (hc.clm_comp (supportedFieldAction B hB)).comp_clm (markedEval (E := E) (K := K) 1)


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



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
local instance compLinInst6_r1cb68e_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst7
local instance compLinInst8_r1cb68e_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance compLinInst9_r1cb68e_1 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance compLinInst10_r1cb68e_1 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))

variable {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)

variable (b : ContDiffBump (0:ℂ)) (hb : K ⊆ Metric.closedBall (0:ℂ) b.rIn)

local instance compLinInst11_r1cb68e_1 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance compLinInst12_r1cb68e_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance compLinInst13_r1cb68e_1 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance compLinInst14_r1cb68e_1 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
lemma completedMarkCorrection_compact : IsCompactOperator (completedMarkCorrection hJ hstd p q u he b hb) :=
  markedFiniteCorrection_isCompact (E := Phase n) _ _

include hc hK in
lemma completedLinearized_fredholm : (completedLinearized hJ hstd p q u he b hb).IsFredholm ∧
    Module.finrank ℝ (completedLinearized hJ hstd p q u he b hb).ker =
      Module.finrank ℝ (supportedHolder (E := Phase n) K ⧸ (completedLinearized hJ hstd p q u he b hb).range) := by
  let C : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
    -completedZeroOrder hJ hstd p q u he + completedMarkCorrection hJ hstd p q u he b hb
  have hC : IsCompactOperator C :=
    (completedZeroOrder_compact_bp240 hJ hstd p q u hK he).neg.add
      (completedMarkCorrection_compact hJ hstd p q u he b hb)
  have hh := completedPrincipal_add_compact_fredholm_bp240 hJ hc hstd p q u hK he C hC
  exact hh


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst14
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst15
variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ᶠ h in 𝓝 (0 : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u.val h.val z‖)

include hc he in
lemma actualMarkedChart_derivative_fredholm_bp240_oai :
    IsIndexZeroFredholm (actualMarkedDerivative hJ hstd b p q u) := by
  obtain ⟨b₁,hb₁⟩ := compact_subset_bump_inner_bp240 (K := Metric.closedBall (0:ℂ) b.rOut)
    (isCompact_closedBall (0:ℂ) b.rOut)
  have hd : actualMarkedDerivative hJ hstd b p q u =
      completedLinearized hJ hstd p q u.val (marked_escape_base b p q u he) b₁ hb₁ :=
    actualMarkedChart_derivative_eq_linearized_bp240 hJ hstd b p q u he b₁ hb₁
  have hf : IsIndexZeroFredholm
      (completedLinearized hJ hstd p q u.val (marked_escape_base b p q u he) b₁ hb₁) :=
    completedLinearized_fredholm hJ hc hstd p q u.val (isCompact_closedBall (0:ℂ) b.rOut)
      (marked_escape_base b p q u he) b₁ hb₁
  exact hd ▸ hf

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_fredholm_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_fredholm_bp240_oai
