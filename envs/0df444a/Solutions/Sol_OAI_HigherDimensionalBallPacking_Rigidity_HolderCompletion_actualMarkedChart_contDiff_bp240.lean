-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_contDiff_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:54:22.179051+00:00
-- url     : https://prove2.me/submissions/4ee19cb1-52a4-49ba-ab4e-6998c0ef233f

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_BanachSpace
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.coefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ofBoundedCThree_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ofBoundedCThree_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.structureAlongDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.structureAlong_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.superposeDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.superpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncatedCoefficient_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma taylor_remainder_quadratic {f : E → F} (hf : Differentiable ℝ f)
    {M : ℝ} (hM : 0 ≤ M)
    (hdf : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ M * ‖x-y‖) (x h : E) :
    ‖f (x+h) - f x - fderiv ℝ f x h‖ ≤ M * ‖h‖ ^ 2 := by
  have hball : x + h ∈ Metric.closedBall x ‖h‖ := by
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, le_refl]
  have hb (z : E) (hz : z ∈ Metric.closedBall x ‖h‖) :
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ M * ‖h‖ := by
    apply (hdf z x).trans
    apply mul_le_mul_of_nonneg_left _ hM
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have he := (convex_closedBall x ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hf z).hasFDerivAt.hasFDerivWithinAt) hb
    (Metric.mem_closedBall_self (norm_nonneg h)) hball
  simpa only [add_sub_cancel_left, pow_two, mul_assoc] using he

lemma hasFDerivAt_of_quadratic_remainder {g : E → F} (L : E →L[ℝ] F) (x : E)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h, ‖g (x+h)-g x-L h‖ ≤ C*‖h‖^2) : HasFDerivAt g L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hδ : 0 < c / (C+1) := div_pos hc (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  have hn : ‖h‖ < c / (C+1) := by simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hsmall : C*‖h‖ ≤ c := by
    have ht := (lt_div_iff₀ (show 0 < C+1 by positivity)).mp hn
    nlinarith [norm_nonneg h]
  exact (hb h).trans (by nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg h)])

namespace BoundedCThree
variable {f : E → F}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealContinuousLinearMapId_solutions
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealContinuousLinearMapId_solutions_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupContinuousLinearMapRealId_solutions_2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealContinuousLinearMapId_solutions_2
lemma norm_fderiv₃_le (hf : BoundedCThree f) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ ≤ hf.bound :=
  (Classical.choose_spec hf.bounded).2.2.2.2 x

lemma fderiv₂_smooth (hf : BoundedCThree f) : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
  hf.fderiv_smooth.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

lemma norm_fderiv_sub_le (hf : BoundedCThree f) (x y : E) :
    ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ hf.bound * ‖x-y‖ :=
  norm_sub_le_of_deriv_bound (hf.fderiv_smooth.differentiable (by simp)) hf.norm_fderiv₂_le x y

lemma norm_fderiv₂_sub_le (hf : BoundedCThree f) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ hf.bound * ‖x-y‖ :=
  norm_sub_le_of_deriv_bound (hf.fderiv₂_smooth.differentiable (by simp)) hf.norm_fderiv₃_le x y

lemma remainder_bound (hf : BoundedCThree f) (x h : E) :
    ‖f (x+h) - f x - fderiv ℝ f x h‖ ≤ hf.bound * ‖h‖^2 :=
  taylor_remainder_quadratic (hf.smooth.differentiable (by simp)) hf.bound_nonneg
    hf.norm_fderiv_sub_le x h

lemma fderiv_remainder_bound (hf : BoundedCThree f) (x h : E) :
    ‖fderiv ℝ f (x+h) - fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) x h‖ ≤ hf.bound * ‖h‖^2 :=
  taylor_remainder_quadratic (hf.fderiv_smooth.differentiable (by simp)) hf.bound_nonneg
    hf.norm_fderiv₂_sub_le x h

end BoundedCThree

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {f : E → F} (hf : BoundedCThree f) {t h : D → E} {x : D}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealContinuousLinearMapId_solutions
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealContinuousLinearMapId_solutions_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupContinuousLinearMapRealId_solutions_2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealContinuousLinearMapId_solutions_2
include hf in
lemma fderiv_composed_remainder (ht : DifferentiableAt ℝ t x) (hh : DifferentiableAt ℝ h x) (v : D) :
    fderiv ℝ (fun z => f (t z + h z) - f (t z) - fderiv ℝ f (t z) (h z)) x v =
      (fderiv ℝ f (t x + h x) - fderiv ℝ f (t x) - fderiv ℝ (fderiv ℝ f) (t x) (h x))
        (fderiv ℝ t x v) +
      (fderiv ℝ f (t x + h x) - fderiv ℝ f (t x)) (fderiv ℝ h x v) := by
  have hc := (((hf.smooth.differentiable (by simp) (t x+h x)).hasFDerivAt.comp x
    (ht.hasFDerivAt.add hh.hasFDerivAt)).sub
      ((hf.smooth.differentiable (by simp) (t x)).hasFDerivAt.comp x ht.hasFDerivAt)).sub
    (((hf.fderiv_smooth.differentiable (by simp) (t x)).hasFDerivAt.comp x ht.hasFDerivAt).clm_apply
      hh.hasFDerivAt)
  have hc' : HasFDerivAt
      (fun z => f (t z+h z)-f (t z)-fderiv ℝ f (t z) (h z))
      ((fderiv ℝ f (t x+h x)).comp (fderiv ℝ t x + fderiv ℝ h x) -
        (fderiv ℝ f (t x)).comp (fderiv ℝ t x) -
        ((fderiv ℝ f (t x)).comp (fderiv ℝ h x) +
          ((fderiv ℝ (fderiv ℝ f) (t x)).comp (fderiv ℝ t x)).flip (h x))) x := by
    convert! hc using 1
    all_goals try with_reducible_and_instances rfl
  rw [hc'.fderiv]
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    map_add]
  rw [(hf.smooth.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)).eq
    (fderiv ℝ t x v) (h x)]
  abel

lemma norm_fderiv_composed_remainder (ht : DifferentiableAt ℝ t x)
    (hh : DifferentiableAt ℝ h x) :
    ‖fderiv ℝ (fun z => f (t z+h z)-f (t z)-fderiv ℝ f (t z) (h z)) x‖ ≤
      hf.bound * ‖h x‖^2 * ‖fderiv ℝ t x‖ + hf.bound * ‖h x‖ * ‖fderiv ℝ h x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [hf.bound_nonneg])
  intro v
  rw [fderiv_composed_remainder hf ht hh]
  calc
    _ ≤ ‖(fderiv ℝ f (t x+h x)-fderiv ℝ f (t x)-fderiv ℝ (fderiv ℝ f) (t x) (h x))
          (fderiv ℝ t x v)‖ +
        ‖(fderiv ℝ f (t x+h x)-fderiv ℝ f (t x)) (fderiv ℝ h x v)‖ := norm_add_le _ _
    _ ≤ (hf.bound * ‖h x‖^2) * (‖fderiv ℝ t x‖ * ‖v‖) +
        (hf.bound * ‖h x‖) * (‖fderiv ℝ h x‖ * ‖v‖) := by
      apply add_le_add
      · exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hf.fderiv_remainder_bound (t x) (h x))
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) (by positivity [hf.bound_nonneg]))
      · have hd := hf.norm_fderiv_sub_le (t x+h x) (t x)
        simp only [add_sub_cancel_left] at hd
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul hd (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
            (mul_nonneg hf.bound_nonneg (norm_nonneg _)))
    _ = _ := by ring

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_NonlinearCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.bumpHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.constHolderCLM_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.constJet_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.constJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCoordinate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCurveJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffSlope_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.derivativeAssembly_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameCRCoefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freePrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetDirection_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetDirectional_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetEval_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.localizedJetValue_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivativeVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFiniteCorrection_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ofBoundedLipschitz_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.principalCR_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.realConstantJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.restrictedValue_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.sourceCutoff_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.standardHolderInverse_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.standardJetCR_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.structureAlongDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.structureAlong_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedCauchyCLM_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedCauchy_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedCauchy_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedFieldAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedSourceCutoff_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncateShift_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncatedCoefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroNormalize_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroNormalize_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

lemma holder_norm_le_of_deriv_bounds (u : HMap D F)
    (hu : Differentiable ℝ (valueCLM _ u)) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hval : ∀ x, ‖valueCLM _ u x‖ ≤ M)
    (hder : ∀ x, ‖fderiv ℝ (valueCLM _ u) x‖ ≤ L) : ‖u‖ ≤ 2*M+L := by
  have he : u = ofBoundedDeriv (valueCLM _ u) hu M L hM hL hval hder := by
    apply value_ext
    intro x
    rfl
  rw [he]
  exact ofBoundedDeriv_norm_le _ _ _ _ _ _ _ _

lemma c_value_bound (u : COne D E) (x : D) : ‖cValue u x‖ ≤ ‖u‖ := jet_norm_value_le u x

section Superposition
variable {f : E → F} (hf : BoundedCThree f)
  {b : D → E} (hb : Differentiable ℝ b) {B : ℝ} (hB : 0 ≤ B)
  (hbB : ∀ x, ‖fderiv ℝ b x‖ ≤ B)

include hf hb in
lemma variation_differentiable (u h : COne D E) :
    Differentiable ℝ (fun z => fderiv ℝ f (b z+cValue u z) (cValue h z)) :=
  (coefficient_differentiable hf hb u).clm_apply (c_differentiable h)

lemma superpose_remainder_norm (u h : COne D E) :
    ‖superpose hf hb hB hbB (u+h) - superpose hf hb hB hbB u -
      superposeDeriv hf hb hB hbB u h‖ ≤ hf.bound*(3+B+‖u‖)*‖h‖^2 := by
  let r := superpose hf hb hB hbB (u+h) - superpose hf hb hB hbB u -
      superposeDeriv hf hb hB hbB u h
  have hv : (valueCLM _ r : D → F) = fun z =>
      f ((b z+cValue u z)+cValue h z)-f (b z+cValue u z)-
        fderiv ℝ f (b z+cValue u z) (cValue h z) := by
    funext z
    simp only [r, map_sub, BoundedContinuousFunction.sub_apply, superpose_value,
      superposeDeriv_value, cValue_add, add_assoc]
  have hd : Differentiable ℝ (valueCLM _ r) := by
    rw [hv]
    exact ((hf.smooth.differentiable (by simp)).comp
      ((hb.add (c_differentiable u)).add (c_differentiable h))).sub
      (superpose_differentiable hf hb u) |>.sub (variation_differentiable hf hb u h)
  have hb0 (x : D) : ‖valueCLM _ r x‖ ≤ hf.bound * ‖h‖^2 := by
    rw [hv]
    exact (hf.remainder_bound _ _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (c_value_bound h x) 2) hf.bound_nonneg)
  have hb1 (x : D) : ‖fderiv ℝ (valueCLM _ r) x‖ ≤
      hf.bound * (B+‖u‖+1) * ‖h‖^2 := by
    rw [hv]
    apply (norm_fderiv_composed_remainder hf ((hb.add (c_differentiable u)) x)
      (c_differentiable h x)).trans
    calc
      _ ≤ hf.bound * ‖h‖^2 * (B+‖u‖) + hf.bound * ‖h‖ * ‖h‖ := by
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (c_value_bound h x) 2) hf.bound_nonneg)
            (base_fderiv_bound hb hbB u x) (norm_nonneg _) (by positivity [hf.bound_nonneg])
        · rw [c_fderiv]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (c_value_bound h x) hf.bound_nonneg)
            (c_deriv_bound h x) (norm_nonneg _) (by positivity [hf.bound_nonneg])
      _ = _ := by ring
  have hh := holder_norm_le_of_deriv_bounds r hd
    (show 0 ≤ hf.bound * ‖h‖^2 by positivity [hf.bound_nonneg])
    (show 0 ≤ hf.bound * (B+‖u‖+1) * ‖h‖^2 by positivity [hf.bound_nonneg]) hb0 hb1
  convert! hh using 1; ring

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeAmbientMemSubmoduleRealHMap
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeAmbientMemSubmoduleHMap
lemma superpose_hasFDerivAt (u : COne D E) :
    HasFDerivAt (superpose hf hb hB hbB) (superposeDeriv hf hb hB hbB u) u := by
  have hC : 0 ≤ hf.bound * (3+B+‖u‖) := by positivity [hf.bound_nonneg]
  have hr : ∀ h : COne D E,
      ‖superpose (D := D) hf hb hB hbB (u+h) - superpose hf hb hB hbB u -
        superposeDeriv hf hb hB hbB u h‖ ≤ hf.bound * (3+B+‖u‖) * ‖h‖^2 :=
    superpose_remainder_norm (D := D) hf hb hB hbB u
  exact hasFDerivAt_of_quadratic_remainder (E := COne D E) (F := HMap D F)
    (g := superpose (D := D) hf hb hB hbB)
    (superposeDeriv (D := D) hf hb hB hbB u) u hC hr

end Superposition
end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.bumpHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.constHolderCLM_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffSlope_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameCRCoefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freePrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetDirectional_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.localizedJetValue_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivativeVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFiniteCorrection_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ofBoundedLipschitz_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.principalCR_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.restrictedValue_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.sourceCutoff_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedFieldAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedSourceCutoff_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncateShift_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncatedCoefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
universe u v
variable {D : Type v} {E F : Type u}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst10
local instance smoothSuperInst11 : ContinuousSMul ℝ (COne D E) := IsBoundedSMul.continuousSMul

variable {f : E → F} (hf : BoundedCThree f)
  {b : D → E} (hb : Differentiable ℝ b) {B : ℝ} (hB : 0 ≤ B)
  (hbB : ∀ x, ‖fderiv ℝ b x‖ ≤ B)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst13
lemma superposeDeriv_eq_assembly (u : COne D E) :
    superposeDeriv hf hb hB hbB u = derivativeAssembly (D := D) (E := E) (F := F) (coefficient hf hb hB hbB u) := rfl

lemma coefficient_eq_superpose (hdf : BoundedCThree (fderiv ℝ f)) (u : COne D E) :
    coefficient hf hb hB hbB u = superpose hdf hb hB hbB u := by
  apply value_ext
  intro x
  rfl

theorem superpose_contDiff_nat (m : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
      (hf : BoundedCThree f) (c : F) (_hc : HasCompactSupport (fun x => f x-c)),
      ContDiff ℝ m (superpose (D := D) hf hb hB hbB) := by
  induction m with
  | zero =>
      intro F _ _ f hf c hc
      have hc : Continuous (superpose (D := D) hf hb hB hbB) :=
        continuous_iff_continuousAt.mpr fun u =>
          (superpose_hasFDerivAt hf hb hB hbB u).continuousAt
      exact contDiff_zero.mpr hc
  | succ m ih =>
      intro F _ _ f hf c hc
      have hdc : HasCompactSupport (fderiv ℝ f) := compactSupport_fderiv_of_perturbation c hc
      have hdf : BoundedCThree (fderiv ℝ f) :=
        boundedCThree_of_compactSupport hf.fderiv_smooth hdc
      have hc' : HasCompactSupport (fun x => fderiv ℝ f x - 0) := by
        simpa only [sub_zero] using hdc
      have hd : ContDiff ℝ m (superpose hdf hb hB hbB) := ih hdf 0 hc'
      have hder : superposeDeriv (D := D) hf hb hB hbB =
          fun u => derivativeAssembly (D := D) (E := E) (F := F)
            (superpose hdf hb hB hbB u) := by
        funext u
        rw [superposeDeriv_eq_assembly, coefficient_eq_superpose]
      rw [show ((m+1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞)+1 by simp]
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨superposeDeriv hf hb hB hbB, ?_, fun u => superpose_hasFDerivAt hf hb hB hbB u⟩
      rw [hder]
      exact (derivativeAssembly (D := D) (E := E) (F := F)).contDiff.comp hd

theorem superpose_contDiff (c : F) (hc : HasCompactSupport (fun x => f x-c)) :
    ContDiff ℝ ∞ (superpose (D := D) hf hb hB hbB) := by
  apply contDiff_infty.mpr
  intro m
  exact superpose_contDiff_nat hb hB hbB m hf c hc


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



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

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst8
local instance markedChartInst13_rc6f0c9_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst14_rc6f0c9_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
omit [CompleteSpace E] in
lemma markedDX_contDiff [CompleteSpace E] (p q : E) (u : COne ℂ E) :
    ContDiff ℝ ∞ (markedDX p q u) := by
  have hC : ContDiff ℝ ∞ (fun h : COne ℂ E => (constHolderCLM (E := E)) (jetEval 1 h)) :=
    ((constHolderCLM (E := E)).comp (jetEval (E := E) 1)).contDiff
  have hD : ContDiff ℝ ∞ (fun h : COne ℂ E => jetDirection (E := E) 1 (u+h)) :=
    (jetDirection (E := E) 1).contDiff.comp (contDiff_const.add contDiff_id)
  exact (contDiff_const.sub hC).add hD

variable {P : E → E →L[ℝ] E} (hP : BoundedCThree P) (b : ContDiffBump (0:ℂ))

omit [CompleteSpace E] in
lemma truncatedCoefficient_contDiff [CompleteSpace E]
    (hc : HasCompactSupport P) (p q : E) (u : COne ℂ E) :
    ContDiff ℝ ∞ (truncatedCoefficient hP b p q u) := by
  have hS : ContDiff ℝ ∞ (structureAlong hP p (complexSlope (markedSlope p q u))) :=
    superpose_contDiff hP (affine_differentiable p _) (norm_nonneg _)
      (affine_fderiv_bound p _) 0 (by simpa only [sub_zero] using hc)
  exact hS.comp (contDiff_const.add (truncateShift (E := E) b).contDiff)

lemma chartNonlinearity_contDiff (hc : HasCompactSupport P) (p q : E) (u : COne ℂ E) :
    ContDiff ℝ ∞ (chartNonlinearity hP b p q u) := by
  exact ((bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip).contDiff.comp
    (truncatedCoefficient_contDiff hP b hc p q u)).clm_apply (markedDX_contDiff p q u)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst12
lemma markedChart_contDiff (hc : HasCompactSupport P) (p q : E)
    (u : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) :
    ContDiff ℝ ∞ (markedChart hP b p q u) := by
  have hL : ContDiff ℝ ∞ (fun h : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut) => (markedCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut)) (u+h)) :=
    (markedCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut)).contDiff.comp (contDiff_const.add contDiff_id)
  have hN := (chartNonlinearity_contDiff hP b hc p q u.val).comp
    (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL.contDiff
  exact hL.sub ((supportedSourceCutoff (E := E) b).contDiff.comp hN)



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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ}

variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst8
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) {B : ℝ}
    (hstd : ∀ x, B < ‖x‖ → J x = standardJ n)

variable (b : ContDiffBump (0:ℂ)) (p q : Phase n)

variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst13
lemma actualMarkedChart_contDiff_bp240_oai : ContDiff ℝ ∞ (actualMarkedChart hJ hstd b p q u) :=
  markedChart_contDiff (compactJPerturbationBound hJ hstd) b (compactJPerturbation_compact hstd) p q u


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_contDiff_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_contDiff_bp240_oai
