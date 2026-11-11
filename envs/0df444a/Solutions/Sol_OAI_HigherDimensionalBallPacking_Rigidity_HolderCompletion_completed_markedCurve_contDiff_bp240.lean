-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completed_markedCurve_contDiff_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:56:01.786775+00:00
-- url     : https://prove2.me/submissions/0e20fc3f-3e40-41e6-a4d1-986008eb65f1

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp022
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_regularityTranslation_near_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_regularityTranslation_smooth_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_BanachSpace
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

variable {X E}

variable {α : ℝ}

variable (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]

variable {D}

lemma jet_norm_value_le (u : COneHolder (E := E) D α) (x : D) :
    ‖valueCLM α (jetValueCLM α u) x‖ ≤ ‖u‖ :=
  (norm_value_le _ _).trans (jetValue_norm_le u)

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

lemma c_value_bound (u : COne D E) (x : D) : ‖cValue u x‖ ≤ ‖u‖ := jet_norm_value_le u x
end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.bumpHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.constHolderCLM_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCoordinate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCurveJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffSlope_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameCRCoefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freePrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetDirectional_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.localizedJetValue_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivativeVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFiniteCorrection_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ofBoundedLipschitz_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.principalCR_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.realConstantJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.restrictedValue_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.sourceCutoff_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedFieldAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedSourceCutoff_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncateShift_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncatedCoefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst8
lemma affineCurve_fderiv (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) :
    fderiv ℝ (affineCurve p a u) z = a+cDeriv u z :=
  (affineCurve_hasFDerivAt p a u z).fderiv

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst2
variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J)

@[simp] lemma crSection_value (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (crSection hJ p a u) z =
      fderiv ℝ (affineCurve p a u) z Complex.I -
        J (affineCurve p a u z) (fderiv ℝ (affineCurve p a u) z 1) := by
  rw [affineCurve_fderiv]
  rfl

@[simp] lemma crSectionDeriv_value (p : E) (a : ℂ →L[ℝ] E)
    (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (crSectionDeriv hJ p a u h) z =
      fderiv ℝ (cValue h) z Complex.I - J (affineCurve p a u z) (fderiv ℝ (cValue h) z 1) -
      (fderiv ℝ J (affineCurve p a u z) (cValue h z))
        (fderiv ℝ (affineCurve p a u) z 1) := by
  rw [affineCurve_fderiv, c_fderiv]
  rfl


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J) (b : ContDiffBump (0:ℂ)) (p a : E)
variable (u : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=complexI (E := E))
  (hesc : ∀ᶠ v in 𝓝 (0 : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z, b.rIn≤‖z‖ → B<‖affineCurve p (complexSlope a) (u.val+v.val) z‖)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.teInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.teInst2
local instance teInst3_rca48c4_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance teInst4_rca48c4_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.teInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.teInst6
omit hJ hstd hesc in
lemma source_smooth_of_translation
    (V : ℂ → freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (hv : ∀ᶠ t in 𝓝 (0:ℂ), (V t).val=translationVariation a u.val t)
    (hs : ContDiffAt ℝ ∞ V 0) : ContDiff ℝ ∞ (affineCurve p (complexSlope a) u.val) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  let L : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut) →L[ℝ] E :=
    (jetEval z).comp (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL
  have ho : ContDiffAt ℝ ∞ (fun t => affineCurve p (complexSlope a) u.val z+L (V t)) 0 :=
    contDiffAt_const.add (L.contDiff.contDiffAt.comp 0 hs)
  have heq : (fun t => affineCurve p (complexSlope a) u.val (z+t)) =ᶠ[𝓝 0]
      (fun t => affineCurve p (complexSlope a) u.val z+L (V t)) := by
    filter_upwards [hv] with t ht
    change affineCurve p (complexSlope a) u.val (z+t) =
      affineCurve p (complexSlope a) u.val z+cValue (V t).val z
    rw [ht,translationVariation_value]
    change p+(z+t) • a+cValue u.val (z+t) =
      (p+z • a+cValue u.val z)+(t • a+cValue u.val (z+t)-cValue u.val z)
    rw [add_smul]
    abel
  have hf := ho.congr_of_eventuallyEq heq
  have hsub : ContDiffAt ℝ ∞ (fun t : ℂ => t-z) z := contDiffAt_id.sub contDiffAt_const
  have hf' : ContDiffAt ℝ ∞ (fun t => affineCurve p (complexSlope a) u.val (z+t)) (z-z) := by
    simpa only [sub_self] using hf
  have hcomp := hf'.comp (f := fun t : ℂ => t-z) z hsub
  convert! hcomp using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  congr 1
  simp only
  abel

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.feInst1
local instance feInst2_rca48c4_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance feInst3_rca48c4_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance feInst4_rca48c4_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma affine_free_norm_lower [CompleteSpace E] (p a : E) (u v : COne ℂ E) (z : ℂ) :
    ‖z‖*‖a‖-‖p‖-‖u‖-‖v‖ ≤ ‖affineCurve p (complexSlope a) (u+v) z‖ := by
  have h : ‖z • a‖ ≤ ‖affineCurve p (complexSlope a) (u+v) z‖+‖p‖+‖cValue u z‖+‖cValue v z‖ := by
    calc
      _ = ‖((affineCurve p (complexSlope a) (u+v) z-p)-cValue u z)-cValue v z‖ := by
        congr 1
        change z • a=((p+z • a+(cValue u z+cValue v z)-p)-cValue u z)-cValue v z
        abel
      _ ≤ ‖(affineCurve p (complexSlope a) (u+v) z-p)-cValue u z‖+‖cValue v z‖ := norm_sub_le _ _
      _ ≤ (‖affineCurve p (complexSlope a) (u+v) z-p‖+‖cValue u z‖)+‖cValue v z‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := by linarith [norm_sub_le (affineCurve p (complexSlope a) (u+v) z) p]
  rw [norm_smul] at h
  linarith [c_value_bound u z,c_value_bound v z]

lemma exists_free_escape_radius (p a : E) (u : COne ℂ E) (ha : a≠0) (B : ℝ) :
    ∃ R : ℝ, 0<R ∧ ∀ v : COne ℂ E, ‖v‖<1 → ∀ z : ℂ, R≤‖z‖ →
      B<‖affineCurve p (complexSlope a) (u+v) z‖ := by
  let R := (max B 0+‖p‖+‖u‖+2)/‖a‖
  have ha' : 0<‖a‖ := norm_pos_iff.mpr ha
  have hR : 0<R := div_pos (by have := le_max_right B 0; positivity) ha'
  refine ⟨R,hR,?_⟩
  intro v hv z hz
  have hn : max B 0+‖p‖+‖u‖+2 ≤ ‖z‖*‖a‖ := by
    have hm := mul_le_mul_of_nonneg_right hz ha'.le
    dsimp only [R] at hm
    rwa [div_mul_cancel₀ _ ha'.ne'] at hm
  exact (show B<‖z‖*‖a‖-‖p‖-‖u‖-‖v‖ by linarith [le_max_left B 0]).trans_le
    (affine_free_norm_lower p a u v z)

omit [CompleteSpace E] in
lemma freeModel_mono [CompleteSpace E] {K L : Set ℂ} (h : K⊆L) : freeModel (E := E) K ≤ freeModel (E := E) L := by
  intro u hu
  apply (mem_supportedHolder _ _).mpr
  intro z hz
  exact (mem_supportedHolder _ _).mp hu z (fun hK => hz (h hK))

omit [CompleteSpace E] in
lemma freeModel_of_elliptic [CompleteSpace E] {J : E → E →L[ℝ] E} {B R : ℝ}
    (hstd : ∀ x, B<‖x‖ → J x=complexI (E := E))
    (p a : E) (u : COne ℂ E)
    (hcr : ∀ z, fderiv ℝ (affineCurve p (complexSlope a) u) z Complex.I =
      J (affineCurve p (complexSlope a) u z) (fderiv ℝ (affineCurve p (complexSlope a) u) z 1))
    (he : ∀ z, R≤‖z‖ → B<‖affineCurve p (complexSlope a) u z‖) :
    u∈freeModel (E := E) (Metric.closedBall (0:ℂ) R) := by
  apply (mem_supportedHolder _ _).mpr
  intro z hz
  have hz' : R≤‖z‖ := (show R<‖z‖ by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz).le
  have hh := hcr z
  rw [hstd _ (he z hz'),affineCurve_fderiv] at hh
  change Complex.I • a+cDeriv u z Complex.I=Complex.I • ((1:ℂ) • a+cDeriv u z 1) at hh
  rw [one_smul,smul_add] at hh
  have hd := add_left_cancel hh
  change valueCLM _ (standardJetCR u) z=0
  rw [standardJetCR_value]
  exact sub_eq_zero.mpr hd

variable (b : ContDiffBump (0:ℂ))

local instance feInst5_rca48c4_1 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance feInst6_rca48c4_1 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
omit [CompleteSpace E] in
lemma freeEscape_of_radius [CompleteSpace E] (p a : E) (u : COne ℂ E) (B : ℝ)
    (he : ∀ v : COne ℂ E, ‖v‖<1 → ∀ z : ℂ, b.rIn≤‖z‖ →
      B<‖affineCurve p (complexSlope a) (u+v) z‖) : FreeEscapeNeighborhood b p a u B := by
  filter_upwards [Metric.ball_mem_nhds (0 : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) (show (0:ℝ)<1 by norm_num)] with v hv
  have hv' : ‖v.val‖<1 := by simpa only [Metric.mem_ball,dist_zero_right,Submodule.norm_coe] using hv
  exact he v.val hv'

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst11
variable (w : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) {R : ℝ}
  (hRS : R+1≤b.rOut) (hsupp : w.val ∈ freeModel (E := Phase n) (Metric.closedBall (0:ℂ) R))
  (hesc : FreeEscapeNeighborhood b p (markedSlope p q w.val) w.val B)
  (hcr : ∀ z, fderiv ℝ (markedCurve p q w.val) z Complex.I =
    J (markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst9
include hJ hstd hc hesc hcr hRS hsupp in
lemma completed_free_source_contDiff : ContDiff ℝ ∞ (markedCurve p q w.val) := by
  have hs := regularityTranslation_smooth_bp240 hJ hc hstd b p q w hRS hsupp hesc hcr
  have hh := source_smooth_of_translation b p (markedSlope p q w.val) w
    (regularityTranslation b p q w hRS hsupp) (regularityTranslation_near_bp240 b p q w hRS hsupp) hs
  exact hh

end
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.azInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.azInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.azInst3
local instance azInst4_rca48c4_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance azInst5_rca48c4_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance azInst6_rca48c4_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=standardJ n) (p q : Phase n)

include hJ hc hstd in
lemma completed_markedCurve_contDiff_bp240_oai (u : COne ℂ (Phase n)) (ha : markedSlope p q u ≠ 0)
    (hcr : ∀ z, fderiv ℝ (markedCurve p q u) z Complex.I =
      J (markedCurve p q u z) (fderiv ℝ (markedCurve p q u) z 1)) :
    ContDiff ℝ ∞ (markedCurve p q u) := by
  obtain ⟨R,hR,he⟩ := exists_free_escape_radius p (markedSlope p q u) u ha B
  have he0 : ∀ z, R≤‖z‖ → B<‖affineCurve p (complexSlope (markedSlope p q u)) u z‖ := by
    intro z hz
    simpa only [add_zero] using he 0 (by simp) z hz
  have huR : u∈freeModel (E := Phase n) (Metric.closedBall (0:ℂ) R) :=
    freeModel_of_elliptic hstd p (markedSlope p q u) u hcr he0
  let b : ContDiffBump (0:ℂ) := ⟨R,R+2,hR,by linarith⟩
  have hRS : R+1≤b.rOut := by change R+1≤R+2; linarith
  have huS : u∈freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) :=
    freeModel_mono (Metric.closedBall_subset_closedBall (by change R≤R+2; linarith)) huR
  let w : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) := ⟨u,huS⟩
  have hesc : FreeEscapeNeighborhood b p (markedSlope p q w.val) w.val B :=
    freeEscape_of_radius b p (markedSlope p q u) u B he
  exact completed_free_source_contDiff hJ hc hstd b p q w hRS huR hesc hcr

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completed_markedCurve_contDiff_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completed_markedCurve_contDiff_bp240_oai
