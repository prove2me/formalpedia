-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_add_compact_fredholm_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T02:20:46.841353+00:00
-- url     : https://prove2.me/submissions/2c07df79-7103-4a2c-95ca-0ecfab7d8b33

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp015
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_compact_subset_bump_inner_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_compatibleFrame_intertwine_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_compatibleFrame_inverse_left_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_jetZeroOrder_isCompact_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_supportedHolder_closed_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_framed_compact_perturbation_fredholm_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_BanachSpace
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped BoundedContinuousFunction Topology ContDiff
open Set Filter
section

variable (X E : Type*) [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma graph_closed (α : ℝ) : IsClosed (graph X E α : Set (Ambient X E)) := by
  change IsClosed {u : Ambient X E | ∀ p : Pairs X, _}
  simp only [← Set.iInter_ofPred]
  apply isClosed_iInter
  intro p
  exact isClosed_eq
    ((BoundedContinuousFunction.evalCLM ℝ p).continuous.comp continuous_snd)
    ((((BoundedContinuousFunction.evalCLM ℝ p.val.1).continuous.comp continuous_fst).sub
      ((BoundedContinuousFunction.evalCLM ℝ p.val.2).continuous.comp continuous_fst)).const_smul _)

instance instCompleteSpaceSubtypeAmbientMemSubmoduleRealHolder (α : ℝ) [CompleteSpace E] : CompleteSpace (Holder X E α) :=
  (graph_closed X E α).completeSpace_coe

variable {X E}

variable {α : ℝ}

variable (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma jetGraph_closed (α : ℝ) : IsClosed (jetGraph (E := E) D α : Set (JetAmbient (E := E) D α)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu huv x
  have hv0 : Tendsto (fun n => valueCLM α (u n).1) atTop (𝓝 (valueCLM α v.1)) :=
    ((valueCLM α).continuous.comp continuous_fst).tendsto v |>.comp huv
  have hv1 : Tendsto (fun n => valueCLM α (u n).2) atTop (𝓝 (valueCLM α v.2)) :=
    ((valueCLM α).continuous.comp continuous_snd).tendsto v |>.comp huv
  have huni := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hv1
  exact hasFDerivAt_of_tendstoUniformly huni (fun n => hu n)
    (fun y => (BoundedContinuousFunction.evalCLM ℝ y).continuous.tendsto _ |>.comp hv0) x

instance instCompleteSpaceSubtypeJetAmbientMemSubmoduleRealCOneHolder (α : ℝ) [CompleteSpace E] : CompleteSpace (COneHolder (E := E) D α) :=
  (jetGraph_closed (E := E) D α).completeSpace_coe

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_NonlinearCR
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
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne_2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_2
local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_r803621_1 : NormedAddCommGroup (COne D E →L[ℝ] COne D F) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_r803621_1 : NormedSpace ℝ (COne D E →L[ℝ] COne D F) := ContinuousLinearMap.toNormedSpace
instance instCompleteSpaceSubtypeAmbientMemSubmoduleRealHMapSupportedHolder (K : Set D) [CompleteSpace E] : CompleteSpace (supportedHolder (E := E) K) :=
  (supportedHolder_closed_bp240 K).completeSpace_coe

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
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

local instance markedAffineInst1_r803621_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_r803621_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_r803621_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_r803621_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma markedModel_closed (K : Set ℂ) : IsClosed (markedModel (E := E) K : Set (COne ℂ E)) :=
  (jetEval (E := E) 0).isClosed_ker.inter ((supportedHolder_closed_bp240 K).preimage standardJetCR.continuous)

instance instCompleteSpaceSubtypeJetAmbientComplexHDivRealOfNatMemSubmoduleCOneMarkedModel (K : Set ℂ) : CompleteSpace (markedModel (E := E) K) :=
  (markedModel_closed K).completeSpace_coe



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

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
local instance zeroOrderInst3_r803621_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance zeroOrderInst4_r803621_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance zeroOrderInst5_r803621_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance zeroOrderInst6_r803621_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance zeroOrderInst7_r803621_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance zeroOrderInst8_r803621_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance zeroOrderInst9_r803621_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance zeroOrderInst10_r803621_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
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

variable {K : Set ℂ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst3
local instance linCRInst4_r803621_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst5
local instance linCRInst6_r803621_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance linCRInst7_r803621_1 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst8_r803621_1 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst9_r803621_1 : NormedAddCommGroup (COne ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst10_r803621_1 : NormedSpace ℝ (COne ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst11_r803621_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance linCRInst12_r803621_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance linCRInst13_r803621_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance linCRInst14_r803621_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
lemma coefficientAction_standardCR (M : COne ℂ (E →L[ℝ] E)) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (standardJetCR (coefficientAction M u)) z =
      cValue M z (cDeriv u z Complex.I) - Complex.I • cValue M z (cDeriv u z 1) +
      valueCLM _ (frameCRCoefficient M) z (cValue u z) := by
  rw [standardJetCR_value,coefficientAction_deriv M u z,frameCRCoefficient_value M z]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,smul_add]
  abel

lemma frame_principal_pointwise (M : COne ℂ (E →L[ℝ] E)) (A : HMap ℂ (E →L[ℝ] E))
    (u : COne ℂ E) (z : ℂ)
    (hmj : cValue M z (valueCLM _ A z (cDeriv u z 1)) = Complex.I • cValue M z (cDeriv u z 1)) :
    cValue M z (cDeriv u z Complex.I - valueCLM _ A z (cDeriv u z 1)) =
      valueCLM _ (standardJetCR (coefficientAction M u)) z -
        valueCLM _ (frameCRCoefficient M) z (cValue u z) := by
  rw [coefficientAction_standardCR M u z]
  calc
    _ = cValue M z (cDeriv u z Complex.I) - cValue M z (valueCLM _ A z (cDeriv u z 1)) :=
      map_sub (cValue M z) _ _
    _ = cValue M z (cDeriv u z Complex.I) - Complex.I • cValue M z (cDeriv u z 1) :=
      congrArg (fun w : E => cValue M z (cDeriv u z Complex.I) - w) hmj
    _ = _ := (add_sub_cancel_right _ _).symm

lemma frame_conjugates_principal (hK : IsClosed K) (M : COne ℂ (E →L[ℝ] E)) (c : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E)
    (A : HMap ℂ (E →L[ℝ] E)) (hA : ∀ z ∉ K, valueCLM _ A z = complexI)
    (hmj : ∀ z v, cValue M z (valueCLM _ A z v) = Complex.I • (cValue M z v)) :
    (supportedCoefficientAction (jetValueCLM _ M)).comp (markedPrincipal A hA) =
      (markedCR (E := E) (K := K)).comp (markedCoefficientAction hK M c hM) -
      markedZeroOrder (frameCRCoefficient M) (frameCRCoefficient_zero_outside hK M c hM) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply value_ext
  intro z
  change cValue M z (cDeriv u.val z Complex.I - valueCLM _ A z (cDeriv u.val z 1)) =
    valueCLM _ (standardJetCR (coefficientAction M u.val)) z -
      valueCLM _ (frameCRCoefficient M) z (cValue u.val z)
  exact frame_principal_pointwise M A u.val z (hmj z (cDeriv u.val z 1))

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [ProperSpace E]
variable {K : Set ℂ} (hK : IsCompact K)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst14
include hK in
lemma framedJetPrincipal_add_compact_fredholm
    (M N : COne ℂ (E →L[ℝ] E)) (m r : ℝ)
    (hM : ∀ z ∉ K, cValue M z = m • ContinuousLinearMap.id ℝ E)
    (hN : ∀ z ∉ K, cValue N z = r • ContinuousLinearMap.id ℝ E)
    (hNM : ∀ z v, cValue N z (cValue M z v) = v)
    (hMN : ∀ z v, cValue M z (cValue N z v) = v)
    (A : HMap ℂ (E →L[ℝ] E))
    (hA : ∀ z ∉ K, valueCLM _ A z = (ContinuousLinearMap.lsmul ℝ ℂ (E := E)) Complex.I)
    (hi : ∀ z v, cValue M z (valueCLM _ A z v) = Complex.I • cValue M z v)
    (C : markedModel (E := E) K →L[ℝ] supportedHolder (E := E) K)
    (hC : IsCompactOperator C) :
    (markedPrincipal A hA+C).IsFredholm ∧
      Module.finrank ℝ (markedPrincipal A hA+C).ker =
        Module.finrank ℝ (supportedHolder (E := E) K ⧸ (markedPrincipal A hA+C).range) := by
  let Z : markedModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
    markedZeroOrder (frameCRCoefficient M) (frameCRCoefficient_zero_outside hK.isClosed M m hM)
  let d : markedModel (E := E) K ≃L[ℝ] supportedHolder (E := E) K :=
    (markedCoefficientEquiv hK.isClosed M N m r hM hN hNM hMN).trans (markedCREquiv hK)
  let e : supportedHolder (E := E) K ≃L[ℝ] supportedHolder (E := E) K :=
    supportedCoefficientEquiv (jetValueCLM _ M) (jetValueCLM _ N) hNM hMN
  have hz : IsCompactOperator Z := markedZeroOrder_isCompact_of_compact hK _ _
  have he : e.toContinuousLinearMap.comp (markedPrincipal A hA) = d.toContinuousLinearMap-Z :=
    frame_conjugates_principal hK.isClosed M m hM A hA hi
  have hh := framed_compact_perturbation_fredholm_bp240 (E := markedModel (E := E) K)
    (F := supportedHolder (E := E) K) (markedPrincipal A hA) Z C d e he hz hC
  exact hh


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst3
local instance ccFrameInst4_r803621_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccFrameInst5
local instance ccFrameInst6_r803621_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance ccFrameInst7_r803621_1 : NormedAddCommGroup (COne ℂ (End n)) := inferInstance
local instance ccFrameInst8_r803621_1 : NormedSpace ℝ (COne ℂ (End n)) := inferInstance
local instance ccFrameInst9_r803621_1 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance ccFrameInst10_r803621_1 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))

variable {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)

local instance ccFrameInst11_r803621_1 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance ccFrameInst12_r803621_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance ccFrameInst13_r803621_1 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance ccFrameInst14_r803621_1 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
include hc hK in
lemma completedPrincipal_add_compact_fredholm_bp240_oai
    (C : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K)
    (hC : IsCompactOperator C) :
    (completedPrincipal hJ hstd p q u he+C).IsFredholm ∧
      Module.finrank ℝ (completedPrincipal hJ hstd p q u he+C).ker =
        Module.finrank ℝ (supportedHolder (E := Phase n) K ⧸ (completedPrincipal hJ hstd p q u he+C).range) := by
  have hh := framedJetPrincipal_add_compact_fredholm (E := Phase n) hK
    (completedFrameJet hJ hstd p q u) (completedInverseJet hJ hc hstd p q u) 2 (1/2)
    (fun z hz => (congrArg compatibleFrame (hstd _ (he z hz))).trans compatibleFrame_standard)
    (fun z hz => (congrArg (fun A : End n => (compatibleFrame A).inverse)
      (hstd _ (he z hz))).trans compatibleFrame_inverse_standard)
    (fun z v => compatibleFrame_inverse_left_bp240 (hc _) v)
    (fun z v => compatibleFrame_inverse_right (hc _) v)
    (jetValueCLM _ (completedStructureJet hJ hstd p q u)) (fun z hz => hstd _ (he z hz))
    (fun z v => compatibleFrame_intertwine_bp240 (hc _) v) C hC
  exact hh


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_add_compact_fredholm_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_add_compact_fredholm_bp240_oai
