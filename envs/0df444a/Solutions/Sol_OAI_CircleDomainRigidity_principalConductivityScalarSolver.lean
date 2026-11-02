-- Prove2me | solution 1 for OAI.CircleDomainRigidity.principalConductivityScalarSolver
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:11:48.364206+00:00
-- url     : https://prove2.me/submissions/debb09b2-045e-4c69-bc6b-b833ff68a8cd

import Mathlib
import Definitions.Def_Q146C011
import Theorems.Thm_OAI_CircleDomainRigidity_PrincipalSmoothApproximation_exists_principal_limit_data
import Theorems.Thm_OAI_CircleDomainRigidity_exists_principal_smooth_approximation
import Theorems.Thm_OAI_CircleDomainRigidity_exteriorCoefficientAreaTheorem
import Theorems.Thm_OAI_CircleDomainRigidity_unorientedFiniteCircleGreenFormula

section
-- module Solutions.Q146_CD.Cannon_Beltrami_MultiplyLp
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section
section
section
section
section
section
section
section
section
section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace CannonBeltrami

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma multiplier_ae (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f : Lp ℂ 2 ν) :
    multiplier m hm hk hb f =ᵐ[ν] fun x => m x*f x := multiplyLp_ae m hm hb f

lemma norm_multiplier_eq (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    (hunit : ∀ᵐ x ∂ν, ‖m x‖=1) (f : Lp ℂ 2 ν) :
    ‖multiplier m hm zero_le_one (hunit.mono (fun _ h => h.le)) f‖=‖f‖ := by
  let g := multiplier m hm zero_le_one (hunit.mono (fun _ h => h.le)) f
  have he : ∀ᵐ x ∂ν, ‖g x‖=‖f x‖ := by
    filter_upwards [multiplier_ae m hm zero_le_one (hunit.mono (fun _ h => h.le)) f,hunit] with x hx hx'
    dsimp [g]
    rw [hx,norm_mul,hx',one_mul]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))

lemma norm_symbolMultiplier (f : PlaneL2) : ‖symbolMultiplier f‖=‖f‖ :=
  norm_multiplier_eq beurlingSymbol measurable_beurlingSymbol.aestronglyMeasurable
    (.of_forall norm_beurlingSymbol) f

lemma norm_beurling (f : PlaneL2) : ‖beurling f‖=‖f‖ := by
  change ‖planeFourier.symm (symbolMultiplier (planeFourier f))‖=‖f‖
  rw [planeFourier.symm.norm_map,norm_symbolMultiplier,planeFourier.norm_map]

open FourierTransform

open scoped ENNReal

end CannonBeltrami

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.Q146_CD.Cannon_Beltrami_CauchySymbol
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

namespace CannonBeltrami
lemma realCLM_apply (D : ℂ →L[ℝ] ℂ) (v : ℂ) :
    D v = (v.re:ℂ)*D 1+(v.im:ℂ)*D Complex.I := by
  have hv : v = v.re • (1:ℂ)+v.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hv,map_add,map_smul,map_smul]
  simp only [Complex.real_smul]

lemma fderiv_wirtinger (f : ℂ → ℂ) (z v : ℂ) :
    fderiv ℝ f z v=partialZ f z*v+partialBar f z*star v := by
  rw [realCLM_apply]
  unfold partialZ partialBar
  have hv := Complex.re_add_im v
  conv_rhs => rw [← hv]
  simp only [map_add,map_mul,Complex.star_def,Complex.conj_ofReal,Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]

lemma partials_id (z : ℂ) : partialZ (fun w : ℂ => w) z=1 ∧
    partialBar (fun w : ℂ => w) z=0 := by
  simp [partialZ,partialBar]

end CannonBeltrami

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.Q146_CD.Cannon_Beltrami_TwoPointNormalize
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

namespace CannonBeltrami
lemma partials_comp {F G : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ F (G z)) (hg : DifferentiableAt ℝ G z) :
    partialZ (F ∘ G) z=partialZ F (G z)*partialZ G z+partialBar F (G z)*star (partialBar G z) ∧
    partialBar (F ∘ G) z=partialZ F (G z)*partialBar G z+partialBar F (G z)*star (partialZ G z) := by
  have hd := (hf.hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  constructor
  · change (fderiv ℝ (F ∘ G) z 1-Complex.I*fderiv ℝ (F ∘ G) z Complex.I)/2= _
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [fderiv_wirtinger F (G z),fderiv_wirtinger F (G z)]
    simp only [partialZ,partialBar,map_div₀,map_add,map_mul,Complex.star_def,
      Complex.conj_I,map_ofNat]
    ring_nf
  · change (fderiv ℝ (F ∘ G) z 1+Complex.I*fderiv ℝ (F ∘ G) z Complex.I)/2= _
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [fderiv_wirtinger F (G z),fderiv_wirtinger F (G z)]
    simp only [partialZ,partialBar,map_div₀,map_sub,map_mul,Complex.star_def,
      Complex.conj_I,map_ofNat]
    ring_nf

lemma inverse_partialBar (F : ℂ ≃ₜ ℂ) (hf : Differentiable ℝ (F : ℂ → ℂ))
    (hg : Differentiable ℝ (F.symm : ℂ → ℂ)) (μ : ℂ → ℂ)
    (he : ∀ z, partialBar F z=μ z*partialZ F z)
    (hn : ∀ z, partialZ F z ≠ 0) (z : ℂ) :
    partialBar F.symm z= -μ (F.symm z)*star (partialZ F.symm z) := by
  have hp := (partials_comp (hf (F.symm z)) (hg z)).2
  have hid : (F : ℂ → ℂ) ∘ F.symm=id := funext F.apply_symm_apply
  rw [hid] at hp
  change partialBar (fun w : ℂ => w) z = _ at hp
  rw [(partials_id z).2,he] at hp
  apply mul_left_cancel₀ (hn (F.symm z))
  linear_combination -hp

end CannonBeltrami

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonBeltrami

lemma realCLM_det_wirtinger (D : ℂ →L[ℝ] ℂ) (a b : ℂ)
    (hD : ∀ v, D v=a*v+b*star v) :
    D.det = ‖a‖^2-‖b‖^2 := by
  change LinearMap.det (D : ℂ →ₗ[ℝ] ℂ) = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply,ContinuousLinearMap.coe_coe,
    Complex.coe_basisOneI,Matrix.cons_val_zero,Matrix.cons_val_one,
    Complex.coe_basisOneI_repr,hD,
    star_one,mul_one,Complex.star_def,Complex.conj_I]
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im]
  rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply]
  ring

lemma realCLM_opNorm_wirtinger (D : ℂ →L[ℝ] ℂ) (a b : ℂ)
    (hD : ∀ v, D v=a*v+b*star v) : ‖D‖ ≤ ‖a‖+‖b‖ := by
  apply D.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  rw [hD]
  calc
    _ ≤ ‖a*v‖+‖b*star v‖ := norm_add_le _ _
    _ = (‖a‖+‖b‖)*‖v‖ := by simp only [norm_mul,norm_star] <;> ring

theorem wirtinger_energy_distortion (D : ℂ →L[ℝ] ℂ) (a b : ℂ)
    (hD : ∀ v, D v=a*v+b*star v) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hba : ‖b‖ ≤ k*‖a‖) :
    0 ≤ D.det ∧ ‖D‖^2 ≤ ((1+k)/(1-k))*|D.det| := by
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hnorm_sq : ‖b‖^2 ≤ k^2*‖a‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ hb (mul_nonneg hk ha)).mpr hba
  have hk_sq : k^2 ≤ 1 := by nlinarith
  have hd := realCLM_det_wirtinger D a b hD
  have hdet : 0 ≤ D.det := by
    rw [hd]
    exact sub_nonneg.mpr (hnorm_sq.trans
      ((mul_le_mul_of_nonneg_right hk_sq (sq_nonneg ‖a‖)).trans_eq (one_mul _)))
  refine ⟨hdet,?_⟩
  rw [abs_of_nonneg hdet,hd]
  have hn := realCLM_opNorm_wirtinger D a b hD
  have hns : ‖D‖^2 ≤ (‖a‖+‖b‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg ha hb)).mpr hn
  have hprod : 0 ≤ (k*‖a‖-‖b‖)*(‖a‖+‖b‖) :=
    mul_nonneg (sub_nonneg.mpr hba) (add_nonneg ha hb)
  apply hns.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hk1)).mpr
  nlinarith

end CannonBeltrami

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.Q146_CD.Cannon_Beltrami_DirichletPullback
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonBeltrami
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dirichlet_pullback_le (F : ℂ ≃ₜ ℂ) (hF : ContDiff ℝ 1 (F : ℂ → ℂ))
    (u : ℂ → E) (hu : ContDiff ℝ 1 u) {S : Set ℂ} (hS : IsCompact S)
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F : ℂ → ℂ) z).det|) :
    (∫ z in S, ‖fderiv ℝ (u ∘ F) z‖^2) ≤
      K*(∫ w in F '' S, ‖fderiv ℝ u w‖^2) := by
  have huD : Continuous (fun z => ‖fderiv ℝ u z‖^2) :=
    (hu.continuous_fderiv (by simp)).norm.pow 2
  have hFi : ∀ z ∈ S, HasFDerivWithinAt (F : ℂ → ℂ) (fderiv ℝ (F : ℂ → ℂ) z) S z :=
    fun z _ => (hF.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume hS.measurableSet
    hFi F.injective.injOn (fun z => ‖fderiv ℝ u z‖^2)
  have hint : IntegrableOn (fun z => |(fderiv ℝ (F : ℂ → ℂ) z).det| *‖fderiv ℝ u (F z)‖^2) S volume := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS.measurableSet
      hFi F.injective.injOn (fun z => ‖fderiv ℝ u z‖^2)).mp
    exact huD.continuousOn.integrableOn_compact (hS.image F.continuous)
  have hlint : IntegrableOn (fun z => ‖fderiv ℝ (u ∘ F) z‖^2) S volume :=
    ((hu.comp hF).continuous_fderiv (by simp)).norm.pow 2 |>.continuousOn.integrableOn_compact hS
  calc
    _ ≤ ∫ z in S, K*(|(fderiv ℝ (F : ℂ → ℂ) z).det| *‖fderiv ℝ u (F z)‖^2) := by
      apply setIntegral_mono_on hlint (hint.const_mul K) hS.measurableSet
      intro z _hz
      rw [fderiv_comp z (hu.differentiable (by simp) (F z)) (hF.differentiable (by simp) z)]
      have hn := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ u (F z)) (fderiv ℝ (F : ℂ → ℂ) z)
      have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
      have hdistortion := mul_le_mul (hD z) (le_refl (‖fderiv ℝ u (F z)‖^2))
        (sq_nonneg _) (mul_nonneg hK (abs_nonneg _))
      nlinarith [hdistortion]
    _ = K*(∫ z in S, |(fderiv ℝ (F : ℂ → ℂ) z).det| *‖fderiv ℝ u (F z)‖^2) := integral_const_mul _ _
    _ = _ := by rw [hchange]; rfl

end CannonBeltrami

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_SmoothBeltramiDistortion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth principal maps and their inverses satisfy the same
uniform quasiconformal distortion bound. -/
open MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma smooth_homeomorph_partialZ_ne_zero (F : ℂ ≃ₜ ℂ)
    (hF : Differentiable ℝ (F : ℂ → ℂ))
    (hFi : Differentiable ℝ (F.symm : ℂ → ℂ)) (μ : ℂ → ℂ)
    (he : ∀ z, partialBar F z=μ z*partialZ F z) (z : ℂ) : partialZ F z ≠ 0 := by
  intro hz
  have hz' : partialBar F z=0 := by rw [he z, hz, mul_zero]
  have hzero : fderiv ℝ (F : ℂ → ℂ) z 1=0 := by
    rw [fderiv_wirtinger F z, hz, hz']
    simp
  have hc := ((hFi (F z)).hasFDerivAt.comp z (hF z).hasFDerivAt).fderiv
  have hid : (F.symm : ℂ → ℂ) ∘ F=id := funext F.symm_apply_apply
  rw [hid, fderiv_id] at hc
  have hh := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) hc
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    hzero, map_zero] at hh
  exact one_ne_zero hh

lemma smooth_beltrami_two_sided_distortion (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ ∞ (F : ℂ → ℂ))
    (hFi : ContDiff ℝ ∞ (F.symm : ℂ → ℂ)) (μ : ℂ → ℂ)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k)
    (he : ∀ z, partialBar F z=μ z*partialZ F z) :
    (∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤
      ((1+k)/(1-k))*|(fderiv ℝ (F : ℂ → ℂ) z).det|) ∧
    ∀ z, ‖fderiv ℝ (F.symm : ℂ → ℂ) z‖^2 ≤
      ((1+k)/(1-k))*|(fderiv ℝ (F.symm : ℂ → ℂ) z).det| := by
  have hd := hF.differentiable (by simp)
  have hdi := hFi.differentiable (by simp)
  have hn := smooth_homeomorph_partialZ_ne_zero F hd hdi μ he
  constructor
  · intro z
    exact (wirtinger_energy_distortion _ _ _ (fderiv_wirtinger F z) hk hk1 (by
      rw [he, norm_mul]
      exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _))).2
  · intro z
    have hi := inverse_partialBar F hd hdi μ he hn z
    exact (wirtinger_energy_distortion _ _ _ (fderiv_wirtinger F.symm z) hk hk1 (by
      rw [hi, norm_mul, norm_neg, norm_star]
      exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))).2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityContraction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real-linear conductivity equation is solved in the actual complex
L2 space by contraction. The operator parameter is only the contraction
property of the Beurling operator; the fixed point and its support are
constructed here. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem conductivityProduct_coe (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) (k : ℝ≥0)
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) (f : ComplexPlaneL2) :
    conductivityProduct q hq k hb f =ᵐ[volume] fun x => q x • f x :=
  MemLp.coeFn_toLp _

 theorem conductivityConj_coe (f : ComplexPlaneL2) :
    conductivityConj f =ᵐ[volume] fun x => star (f x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLp f

 theorem conductivitySource_coe (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume) :
    conductivitySource q hq =ᵐ[volume] fun x => (q x : ℂ) :=
  MemLp.coeFn_toLp _

 theorem conductivityIteration_coe (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume)
    (k : ℝ≥0) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k)
    (S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2) (f : ComplexPlaneL2) :
    conductivityIteration q hq k hb S f =ᵐ[volume]
      fun x => (q x : ℂ) * star (1 + S f x) := by
  filter_upwards [Lp.coeFn_add (conductivitySource q hq)
      (conductivityProduct q hq.aestronglyMeasurable k hb (conductivityConj (S f))),
    conductivitySource_coe q hq,
    conductivityProduct_coe q hq.aestronglyMeasurable k hb (conductivityConj (S f)),
    conductivityConj_coe (S f)] with x hx hq' hp hc
  rw [conductivityIteration, hx, Pi.add_apply, hq', hp, hc]
  simp only [Complex.real_smul, star_add, star_one]
  ring

 theorem conductivityIteration_contracting (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k)
    (S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2) (hS : ∀ f, ‖S f‖ ≤ ‖f‖) :
    ContractingWith k (conductivityIteration q hq k hb S) := by
  refine ⟨hk, LipschitzWith.of_dist_le_mul fun f g => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  have he : ‖conductivityIteration q hq k hb S f - conductivityIteration q hq k hb S g‖ ≤
      (k : ℝ) * ‖S (f - g)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [conductivityIteration_coe q hq k hb S f,
      conductivityIteration_coe q hq k hb S g,
      Lp.coeFn_sub (conductivityIteration q hq k hb S f) (conductivityIteration q hq k hb S g),
      Lp.coeFn_sub (S f) (S g), hb] with x hf hg hd hs hqx
    rw [Pi.sub_apply, hf, hg] at hd
    rw [hd, map_sub S, hs]
    have ha : (q x : ℂ) * star (1 + S f x) - (q x : ℂ) * star (1 + S g x) =
        (q x : ℂ) * star (S f x - S g x) := by
      simp only [star_add, star_sub, star_one]
      ring
    rw [ha, norm_mul, norm_star, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right hqx (norm_nonneg _)
  exact he.trans (mul_le_mul_of_nonneg_left (hS (f - g)) k.2)

 theorem exists_conductivity_density (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k)
    (S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2) (hS : ∀ f, ‖S f‖ ≤ ‖f‖) :
    ∃ g : ComplexPlaneL2,
      (∀ᵐ x ∂volume, g x = (q x : ℂ) * star (1 + S g x)) ∧
      ‖g‖ ≤ ‖conductivitySource q hq‖ / (1 - (k : ℝ)) := by
  let A := conductivityIteration q hq k hb S
  have hA : ContractingWith k A := conductivityIteration_contracting q hq k hk hb S hS
  let g := hA.fixedPoint A
  have hg : A g = g := hA.fixedPoint_isFixedPt
  refine ⟨g, ?_, ?_⟩
  · have hh := conductivityIteration_coe q hq k hb S g
    change conductivityIteration q hq k hb S g = g at hg
    rw [hg] at hh
    exact hh
  · have h := hA.dist_fixedPoint_le (0 : ComplexPlaneL2)
    have hz : A 0 = conductivitySource q hq := by
      apply Lp.ext
      filter_upwards [conductivityIteration_coe q hq k hb S 0,
        conductivitySource_coe q hq, Lp.coeFn_zero ℂ 2 (volume : Measure EuclideanPlane)] with x hx hq' h0
      rw [hx, map_zero, h0, Pi.zero_apply, add_zero, star_one, mul_one, hq']
    simpa only [g, dist_zero_left, hz] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityAlgebra
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and complex forms of the two-dimensional conductivity system.
These pointwise identities retain the signs and normalization used in the
Dirichlet-energy argument. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem conductivity_system_iff {k aX aY vX vY : ℝ} (hk : 0 ≤ k) :
    planarDbar aX aY vX vY = ((k - 1) / (k + 1) : ℝ) • star (planarDz aX aY vX vY) ↔
      aX = k * vY ∧ aY = -k * vX := by
  have hd : k + 1 ≠ 0 := by linarith
  have dzr (a b c d : ℝ) : (planarDz a b c d).re = (a + d) / 2 := by
    simp [planarDz]
  have dzi (a b c d : ℝ) : (planarDz a b c d).im = (c - b) / 2 := by
    simp [planarDz]
  have dbr (a b c d : ℝ) : (planarDbar a b c d).re = (a - d) / 2 := by
    simp [planarDbar]
  have dbi (a b c d : ℝ) : (planarDbar a b c d).im = (c + b) / 2 := by
    simp [planarDbar]
  have sr (q : ℝ) (z : ℂ) : (q • star z).re = q * z.re := by
    simp only [Complex.smul_re, Complex.star_def, Complex.conj_re, smul_eq_mul]
  have si (q : ℝ) (z : ℂ) : (q • star z).im = -(q * z.im) := by
    simp only [Complex.smul_im, Complex.star_def, Complex.conj_im, smul_eq_mul, mul_neg]
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    rw [dbr, sr, dzr] at hr
    rw [dbi, si, dzi] at hi
    field_simp at hr hi
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    apply Complex.ext
    · rw [dbr, sr, dzr]
      field_simp
    · rw [dbi, si, dzi]
      field_simp
      ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityCoefficient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual two-valued conductivity coefficient. Its strict contraction
constant is (n-1)/(n+1), and the constructed density vanishes off F. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem conductivityRatio_lt_one (n : ℕ) (hn : 1 ≤ n) : conductivityRatio n hn < 1 := by
  change ((n : ℝ) - 1) / ((n : ℝ) + 1) < 1
  apply (div_lt_one (by positivity)).mpr
  linarith

 theorem conductivityCoefficient_memLp {F : Set EuclideanPlane} (hF : IsCompact F) (n : ℕ) :
    MemLp (conductivityCoefficient F n) 2 volume :=
  memLp_indicator_const 2 hF.measurableSet _ (Or.inr hF.measure_lt_top.ne)

 theorem conductivityCoefficient_bound (F : Set EuclideanPlane) (n : ℕ) (hn : 1 ≤ n) :
    ∀ x, ‖conductivityCoefficient F n x‖ ≤ conductivityRatio n hn := by
  intro x
  by_cases hx : x ∈ F
  · simp only [conductivityCoefficient, indicator_of_mem hx, Real.norm_eq_abs]
    exact le_of_eq (abs_of_nonneg (conductivityRatio n hn).2)
  · simp only [conductivityCoefficient, indicator_of_notMem hx, norm_zero]
    exact (conductivityRatio n hn).2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConjugateBeltramiL2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Beurling operator in the physical plane. Its exact L2
isometry supplies the operator previously parameterized in conductivity
contraction; no second fixed-point argument is needed. -/
open MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma physicalBeurling_norm (f : ComplexPlaneL2) : ‖physicalBeurling f‖ = ‖f‖ := by
  change ‖complexLpToPhysical (beurling (physicalLpToComplex f))‖ = ‖f‖
  rw [complexLpToPhysical.norm_map, norm_beurling, physicalLpToComplex.norm_map]

lemma complexLpToPhysical_coe (f : PlaneL2) :
    complexLpToPhysical f =ᵐ[volume] fun x => f (complexPlaneCoordinates x) :=
  Lp.coeFn_compMeasurePreserving f complexPlaneCoordinates_measurePreserving

lemma physicalLpToComplex_coe (f : ComplexPlaneL2) :
    physicalLpToComplex f =ᵐ[volume] fun z => f (complexPlaneCoordinates.symm z) :=
  Lp.coeFn_compMeasurePreserving f
    (complexPlaneCoordinates_measurePreserving.symm
      complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv)

lemma physicalLpToComplex_complexLpToPhysical (f : PlaneL2) :
    physicalLpToComplex (complexLpToPhysical f) = f := by
  apply Lp.ext
  filter_upwards [physicalLpToComplex_coe (complexLpToPhysical f),
    (complexPlaneCoordinates_measurePreserving.symm
      complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv).quasiMeasurePreserving.ae (complexLpToPhysical_coe f)]
    with z hz hw
  simpa only [hz, hw, ContinuousLinearEquiv.apply_symm_apply]

lemma physicalLpToComplex_beurling (f : ComplexPlaneL2) :
    physicalLpToComplex (physicalBeurling f) = beurling (physicalLpToComplex f) :=
  physicalLpToComplex_complexLpToPhysical _

lemma physicalBeurling_complex_coe (f : ComplexPlaneL2) :
    beurling (physicalLpToComplex f) =ᵐ[volume]
      fun z => physicalBeurling f (complexPlaneCoordinates.symm z) := by
  rw [← physicalLpToComplex_beurling]
  exact physicalLpToComplex_coe _

lemma exists_actual_conductivity_density (q : EuclideanPlane → ℝ)
    (hq : MemLp q 2 volume) (k : ℝ≥0) (hk : k < 1)
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ g : ComplexPlaneL2,
      (∀ᵐ x ∂volume, g x = (q x : ℂ) * star (1 + physicalBeurling g x)) ∧
      ‖g‖ ≤ ‖conductivitySource q hq‖ / (1 - (k : ℝ)) :=
  exists_conductivity_density q hq k hk hb physicalBeurling
    (fun f => (physicalBeurling_norm f).le)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalRealBeltrami
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise classical real-coefficient principal Beltrami input.

Published source: Clop and Cruz, *Weighted estimates for Beltrami
equations*, Ann. Acad. Sci. Fenn. Math. 38 (2013), 91–113,
DOI 10.5186/aasfm.2013.3818, section 4, opening paragraph, p. 107.
Their theorem states existence of a principal W^{1,2}_loc plane homeomorphism
for compactly supported measurable coefficients mu, nu with
|mu|+|nu| bounded by k<1. We use only mu=0 and real nu=q.

No height, energy inequality, extremality, circle model, or limiting
assertion is included in this input. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem conductivityCoefficient_ratio (F : Set EuclideanPlane) (n : ℕ) (x : EuclideanPlane) :
    conductivityCoefficient F n x =
      (conductivityValue F n x - 1) / (conductivityValue F n x + 1) := by
  classical
  by_cases hx : x ∈ F <;> simp [conductivityCoefficient, conductivityValue, hx]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalRoundIntegrals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of round-disk integrals and smooth partial derivatives
between the physical Euclidean plane and the complex plane. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem physical_complex_partial {a : EuclideanPlane → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (x v : EuclideanPlane) :
    fderiv ℝ (fun z => a (complexPlaneCoordinates.symm z)) (complexPlaneCoordinates x)
      (complexPlaneCoordinates v) = fderiv ℝ a x v := by
  change fderiv ℝ (a ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates x)
    (complexPlaneCoordinates v) = _
  rw [fderiv_comp (complexPlaneCoordinates x) (ha.differentiable (by simp)).differentiableAt
      complexPlaneCoordinates.symm.differentiableAt, complexPlaneCoordinates.symm.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexLocalSobolevTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Package actual complex weak directional fields as the physical local
Sobolev witness required by the principal-map construction. -/
open MeasureTheory Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma planarDz_of_complex_directions (a b : ℂ) :
    planarDz a.re b.re a.im b.im = (a - Complex.I * b) / 2 := by
  apply Complex.ext <;> simp [planarDz]

lemma planarDbar_of_complex_directions (a b : ℂ) :
    planarDbar a.re b.re a.im b.im = (a + Complex.I * b) / 2 := by
  apply Complex.ext <;> simp [planarDbar, add_comm, sub_eq_add_neg]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalWeakDirections
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strong principal density limit supplies the actual directional weak
derivatives of the locally uniform homeomorphism limit. -/
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma principalDirectionalCorrection_ae (g : PlaneL2) (v : ℂ) :
    principalDirectionalCorrection g v =ᵐ[volume]
      fun z => v*beurling g z + star v*g z := by
  filter_upwards [Lp.coeFn_add (v • beurling g) (star v • g),
    Lp.coeFn_smul v (beurling g), Lp.coeFn_smul (star v) g] with z h1 h2 h3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
  exact h1.trans (congrArg₂ (· + ·) h2 h3)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalPhysicalWitness
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the actual principal weak directional fields to the exact
physical Sobolev witness, retaining the real conjugate Beltrami equation. -/
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma principalPhysicalWitness_equation (H : ℂ ≃ₜ ℂ) (g : PlaneL2)
    (hw : ∀ (v : ℂ) (φ : SchwartzMap ℂ ℂ), HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, H z*fderiv ℝ (φ : ℂ → ℂ) z v) =
        -(∫ z, (v+principalDirectionalCorrection g v z)*φ z))
    (q : EuclideanPlane → ℝ)
    (hq : ∀ᵐ z ∂volume, g z=(q (complexPlaneCoordinates.symm z) : ℂ)*
      star (1+beurling g z)) :
    let D := principalPhysicalWitness H g hw
    ∀ᵐ x ∂volume,
      planarDbar (D.realGradient x 0) (D.realGradient x 1)
        (D.imagGradient x 0) (D.imagGradient x 1) =
      q x • star (planarDz (D.realGradient x 0) (D.realGradient x 1)
        (D.imagGradient x 0) (D.imagGradient x 1)) := by
  have hmp := complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving
  filter_upwards [hmp.ae hq, hmp.ae (principalDirectionalCorrection_ae g 1),
    hmp.ae (principalDirectionalCorrection_ae g Complex.I)] with x hqx h0 h1
  change planarDbar (principalWeakDirections g 0 (complexPlaneCoordinates x)).re
    (principalWeakDirections g 1 (complexPlaneCoordinates x)).re
    (principalWeakDirections g 0 (complexPlaneCoordinates x)).im
    (principalWeakDirections g 1 (complexPlaneCoordinates x)).im =
      q x • star (planarDz (principalWeakDirections g 0 (complexPlaneCoordinates x)).re
        (principalWeakDirections g 1 (complexPlaneCoordinates x)).re
        (principalWeakDirections g 0 (complexPlaneCoordinates x)).im
        (principalWeakDirections g 1 (complexPlaneCoordinates x)).im)
  rw [planarDbar_of_complex_directions, planarDz_of_complex_directions]
  simp only [principalWeakDirections, complexPlaneCoordinates_zero,
    complexPlaneCoordinates_one, h0, h1, star_one, Complex.star_def, Complex.conj_I,
    one_mul, neg_mul] at hqx ⊢
  have hb : (1+(beurling g (complexPlaneCoordinates x)+g (complexPlaneCoordinates x))+
      Complex.I*(Complex.I+(Complex.I*beurling g (complexPlaneCoordinates x)-
        Complex.I*g (complexPlaneCoordinates x))))/2 = g (complexPlaneCoordinates x) := by
    ring_nf
    simp [Complex.I_sq]
    ring
  have hz : (1+(beurling g (complexPlaneCoordinates x)+g (complexPlaneCoordinates x))-
      Complex.I*(Complex.I+(Complex.I*beurling g (complexPlaneCoordinates x)-
        Complex.I*g (complexPlaneCoordinates x))))/2 = 1+beurling g (complexPlaneCoordinates x) := by
    ring_nf
    simp [Complex.I_sq]
    ring
  simp only [sub_eq_add_neg] at hb hz ⊢
  rw [hb, hz]
  simpa only [ContinuousLinearEquiv.symm_apply_apply, Complex.real_smul] using hqx

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RealBeltramiCoefficientReduction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the actual conjugate Beltrami equation to a bounded standard
coefficient after constructing its L2 solution. No nonvanishing assumption
on the complex derivative is needed for this algebraic reduction. -/
open MeasureTheory Filter Set
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma realBeltramiStandardCoefficient_norm_le (q : ℝ) (a : ℂ) :
    ‖realBeltramiStandardCoefficient q a‖ ≤ ‖q‖ := by
  by_cases ha : a = 0
  · simp [realBeltramiStandardCoefficient, ha]
  · simp [realBeltramiStandardCoefficient, norm_ne_zero_iff.mpr ha]

lemma realBeltramiStandardCoefficient_mul (q : ℝ) (a : ℂ) :
    realBeltramiStandardCoefficient q a * a = (q : ℂ) * star a := by
  by_cases ha : a = 0
  · simp [realBeltramiStandardCoefficient, ha]
  · exact div_mul_cancel₀ _ ha

lemma realBeltramiStandardCoefficient_aeStronglyMeasurable
    (q : EuclideanPlane → ℝ) (a : EuclideanPlane → ℂ)
    (hq : AEStronglyMeasurable q volume) (ha : AEStronglyMeasurable a volume) :
    AEStronglyMeasurable (fun z => realBeltramiStandardCoefficient (q z) (a z)) volume := by
  exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable hq).mul ha.star).div₀ ha

lemma realBeltramiStandardCoefficient_zero (a : ℂ) :
    realBeltramiStandardCoefficient 0 a = 0 := by
  simp [realBeltramiStandardCoefficient]

lemma exists_compact_coefficient_representative (μ : EuclideanPlane → ℂ)
    (hm : AEStronglyMeasurable μ volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, μ x = 0)
    (k : ℝ≥0) (hb : ∀ᵐ x ∂volume, ‖μ x‖ ≤ k) :
    ∃ ν : EuclideanPlane → ℂ, Measurable ν ∧ (∀ x, ‖ν x‖ ≤ k) ∧
      (∀ x ∉ K, ν x = 0) ∧ μ =ᵐ[volume] ν := by
  classical
  let ν : EuclideanPlane → ℂ := fun x =>
    if x ∈ K ∧ ‖hm.mk μ x‖ ≤ k then hm.mk μ x else 0
  have hm' : Measurable (hm.mk μ) := hm.measurable_mk
  refine ⟨ν, Measurable.ite (hK.measurableSet.inter (measurableSet_le hm'.norm measurable_const))
    hm' measurable_const, ?_, ?_, ?_⟩
  · intro x
    dsimp only [ν]
    split_ifs with hx
    · exact hx.2
    · exact_mod_cast k.2
  · intro x hx
    exact ite_eq_right (fun h => hx h.1)
  · filter_upwards [hm.ae_eq_mk, hb] with x hx hb'
    by_cases hxK : x ∈ K
    · dsimp only [ν]
      rw [← hx, ite_eq_left ⟨hxK, hb'⟩]
    · dsimp only [ν]
      rw [ite_eq_right (fun h => hxK h.1)]
      exact hzero x hxK

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RealBeltramiL2Reduction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable standard coefficient built from the actual conductivity
L2 density. The zero-derivative set requires no division hypothesis. -/
open MeasureTheory Filter Set
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_real_beltrami_l2_reduction (q : EuclideanPlane → ℝ)
    (hq : MemLp q 2 volume) (k : ℝ≥0) (hk : k < 1)
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (h : ComplexPlaneL2) (μ : EuclideanPlane → ℂ),
      AEStronglyMeasurable μ volume ∧
      (∀ᵐ x ∂volume, ‖μ x‖ ≤ k) ∧
      (∀ x, q x = 0 → μ x = 0) ∧
      (∀ᵐ x ∂volume, h x = (q x : ℂ) * star (1 + physicalBeurling h x)) ∧
      (∀ᵐ x ∂volume, h x = μ x * (1 + physicalBeurling h x)) ∧
      ‖h‖ ≤ ‖conductivitySource q hq‖ / (1 - (k : ℝ)) := by
  obtain ⟨h, heq, hn⟩ := exists_actual_conductivity_density q hq k hk hb
  let μ : EuclideanPlane → ℂ := fun x =>
    realBeltramiStandardCoefficient (q x) (1 + physicalBeurling h x)
  refine ⟨h, μ, realBeltramiStandardCoefficient_aeStronglyMeasurable q _
    hq.aestronglyMeasurable
    (aestronglyMeasurable_const.add (Lp.aestronglyMeasurable _)), ?_, ?_, heq, ?_, hn⟩
  · filter_upwards [hb] with x hx
    exact (realBeltramiStandardCoefficient_norm_le _ _).trans hx
  · intro x hx
    simp only [μ, hx, realBeltramiStandardCoefficient_zero]
  · filter_upwards [heq] with x hx
    exact hx.trans (realBeltramiStandardCoefficient_mul _ _).symm

lemma real_beltrami_memLp_of_compact_support (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, q x = 0)
    (k : ℝ≥0) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) : MemLp q 2 volume := by
  have hm : MemLp (K.indicator (fun _ : EuclideanPlane => (k : ℝ))) 2 volume :=
    memLp_indicator_const 2 hK.measurableSet _ (Or.inr hK.measure_lt_top.ne)
  apply hm.of_le hq
  filter_upwards [hb] with x hx
  by_cases hxK : x ∈ K
  · simpa only [indicator_of_mem hxK, Real.norm_eq_abs] using
      hx.trans (le_abs_self (k : ℝ))
  · simp only [hzero x hxK, norm_zero, indicator_of_notMem hxK, le_refl]

lemma exists_compact_real_beltrami_l2_reduction (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, q x = 0)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (h : ComplexPlaneL2) (μ : EuclideanPlane → ℂ),
      AEStronglyMeasurable μ volume ∧ (∀ᵐ x ∂volume, ‖μ x‖ ≤ k) ∧
      (∀ x ∉ K, μ x = 0) ∧
      (∀ᵐ x ∂volume, h x = (q x : ℂ) * star (1 + physicalBeurling h x)) ∧
      (∀ᵐ x ∂volume, h x = μ x * (1 + physicalBeurling h x)) := by
  obtain ⟨h, μ, hm, hbμ, hzμ, hqeq, hμeq, _⟩ := exists_real_beltrami_l2_reduction q
    (real_beltrami_memLp_of_compact_support q hq hK hzero k hb) k hk hb
  exact ⟨h, μ, hm, hbμ, fun x hx => hzμ x (hzero x hx), hqeq, hμeq⟩

lemma exists_bounded_compact_real_beltrami_l2_reduction (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, q x = 0)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (h : ComplexPlaneL2) (μ : EuclideanPlane → ℂ), Measurable μ ∧
      (∀ x, ‖μ x‖ ≤ k) ∧ (∀ x ∉ K, μ x = 0) ∧
      (∀ᵐ x ∂volume, h x = (q x : ℂ) * star (1 + physicalBeurling h x)) ∧
      (∀ᵐ x ∂volume, h x = μ x * (1 + physicalBeurling h x)) := by
  obtain ⟨h, μ, hm, hbm, hzm, hqeq, hmeq⟩ :=
    exists_compact_real_beltrami_l2_reduction q hq hK hzero k hk hb
  obtain ⟨ν, hνm, hνb, hνz, heq⟩ :=
    exists_compact_coefficient_representative μ hm hK hzm k hbm
  refine ⟨h, ν, hνm, hνb, hνz, hqeq, ?_⟩
  filter_upwards [hmeq, heq] with x hx he
  rwa [he] at hx

lemma exists_complex_real_beltrami_l2_reduction (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, q x = 0)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (g : CannonBeltrami.PlaneL2) (μ : ℂ → ℂ), Measurable μ ∧
      (∀ z, ‖μ z‖ ≤ k) ∧
      (∀ z ∉ complexPlaneCoordinates '' K, μ z = 0) ∧
      (∀ᵐ z ∂volume,
        g z = (q (complexPlaneCoordinates.symm z) : ℂ) *
          star (1+CannonBeltrami.beurling g z)) ∧
      (∀ᵐ z ∂volume, g z = μ z*(1+CannonBeltrami.beurling g z)) := by
  obtain ⟨h, ν, hνm, hνb, hνz, hqe, hνe⟩ :=
    exists_bounded_compact_real_beltrami_l2_reduction q hq hK hzero k hk hb
  let g := physicalLpToComplex h
  let μ : ℂ → ℂ := ν ∘ complexPlaneCoordinates.symm
  have hmp := complexPlaneCoordinates_measurePreserving.symm
    complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv
  refine ⟨g, μ, hνm.comp complexPlaneCoordinates.symm.continuous.measurable,
    fun z => hνb _, ?_, ?_, ?_⟩
  · intro z hz
    exact hνz _ (fun h => hz ⟨_, h, complexPlaneCoordinates.apply_symm_apply z⟩)
  · filter_upwards [hmp.quasiMeasurePreserving.ae hqe, physicalLpToComplex_coe h,
      physicalBeurling_complex_coe h] with z hqz hgz hBz
    change physicalLpToComplex h z = _
    rw [hgz, hBz]
    exact hqz
  · filter_upwards [hmp.quasiMeasurePreserving.ae hνe, physicalLpToComplex_coe h,
      physicalBeurling_complex_coe h] with z hνz hgz hBz
    change physicalLpToComplex h z = _
    rw [hgz, hBz]
    exact hνz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MollificationMovingPoint
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive mollifiers converge at moving points whenever
those points converge. Only continuity near a compact ball is used. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma planarMollification_tendsto_moving
    {u : EuclideanPlane → ℝ} (hu : Continuous u)
    {x : ℕ → EuclideanPlane} {y : EuclideanPlane}
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n => planarMollification u n (x n)) atTop (𝓝 (u y)) := by
  have herr : Tendsto (fun n => planarMollification u n (x n)-u (x n)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hm := planarMollification_uniform_on_compact hu.aestronglyMeasurable
      (isCompact_closedBall y 1) isOpen_univ (subset_univ _) hu.continuousOn hε
    have hb : ∀ᶠ n in atTop, x n ∈ closedBall y 1 :=
      (hx.eventually (Metric.ball_mem_nhds y zero_lt_one)).mono fun _ h => ball_subset_closedBall h
    filter_upwards [hm, hb] with n hn hb
    simpa only [dist_zero_right, Real.norm_eq_abs] using hn (x n) hb
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using herr.add (hu.continuousAt.tendsto.comp hx)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothPhysicalPullback
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth quasiconformal pullback energy in the actual physical plane.
Only the finite compact-set estimate needed for the limiting scalar
transport is asserted. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma physicalSmoothEnergy_eq_complex {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : EuclideanPlane) :
    physicalSmoothEnergy u x =
      ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates x)‖^2 := by
  rw [complexCovector_norm_sq, ← complexPlaneCoordinates_zero,
    ← complexPlaneCoordinates_one]
  simp only [Function.comp_def]
  rw [physical_complex_partial hu, physical_complex_partial hu]
  rfl

lemma physicalSmoothEnergy_integral {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (S : Set EuclideanPlane) :
    (∫ x in S, physicalSmoothEnergy u x) =
      ∫ z in complexPlaneCoordinates '' S,
        ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖^2 := by
  calc
    _ = ∫ x in S,
        ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates x)‖^2 := by
      apply integral_congr_ae
      exact Eventually.of_forall (physicalSmoothEnergy_eq_complex hu)
    _ = _ := by
      have h := complexPlaneCoordinates_measurePreserving.setIntegral_preimage_emb
        complexPlaneCoordinates.toHomeomorph.measurableEmbedding
        (fun z => ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖^2)
        (complexPlaneCoordinates '' S)
      simpa only [preimage_image_eq _ complexPlaneCoordinates.injective] using h

lemma physicalHomeomorph_contDiff (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F : ℂ → ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalHomeomorph F : EuclideanPlane → EuclideanPlane) :=
  complexPlaneCoordinates.symm.contDiff.comp (hF.comp complexPlaneCoordinates.contDiff)

lemma physicalSmoothPullback_energy (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F : ℂ → ℂ))
    {u : EuclideanPlane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤
      K*|(fderiv ℝ (F : ℂ → ℂ) z).det|)
    {S : Set EuclideanPlane} (hS : IsCompact S) :
    (∫ x in S, physicalSmoothEnergy (u ∘ physicalHomeomorph F) x) ≤
      K*(∫ x in physicalHomeomorph F '' S, physicalSmoothEnergy u x) := by
  have hv := hu.comp (physicalHomeomorph_contDiff F hF)
  have he : (u ∘ physicalHomeomorph F) ∘ complexPlaneCoordinates.symm =
      (u ∘ complexPlaneCoordinates.symm) ∘ F := by
    funext z
    simp only [Function.comp_apply, physicalHomeomorph_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  have hi : F '' (complexPlaneCoordinates '' S) =
      complexPlaneCoordinates '' (physicalHomeomorph F '' S) := by
    rw [image_image, image_image]
    congr 1
  rw [physicalSmoothEnergy_integral hv, he]
  have h := CannonBeltrami.dirichlet_pullback_le F (hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (u ∘ complexPlaneCoordinates.symm)
    ((hu.comp complexPlaneCoordinates.symm.contDiff).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (hS.image complexPlaneCoordinates.continuous) hK hD
  rw [hi, ← physicalSmoothEnergy_integral hu] at h
  exact h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothPhysicalPullbackBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global and localized energy bounds for a compact smooth scalar under
the actual smooth plane homeomorphism. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma physicalSmoothPartial_memLp {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hs : HasCompactSupport u) (i : Fin 2) :
    MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) 2 volume :=
  ((hu.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hs.fderiv_apply ℝ _)

lemma physicalSmoothEnergy_integrable {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hs : HasCompactSupport u) :
    Integrable (physicalSmoothEnergy u) volume :=
  (physicalSmoothPartial_memLp hu hs 0).integrable_sq.add
    (physicalSmoothPartial_memLp hu hs 1).integrable_sq

lemma physicalSmoothEnergy_nonneg (u : EuclideanPlane → ℝ) (x : EuclideanPlane) :
    0 ≤ physicalSmoothEnergy u x := add_nonneg (sq_nonneg _) (sq_nonneg _)

lemma physicalSmoothPullback_energy_global (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F : ℂ → ℂ))
    {u : EuclideanPlane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hs : HasCompactSupport u)
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F : ℂ → ℂ) z).det|) :
    (∫ x, physicalSmoothEnergy (u ∘ physicalHomeomorph F) x) ≤
      K*(∫ x, physicalSmoothEnergy u x) := by
  have hvs := hs.comp_homeomorph (physicalHomeomorph F)
  have he := physicalSmoothPullback_energy F hF hu hK hD hvs.isCompact
  have hz : ∀ x ∉ tsupport (u ∘ physicalHomeomorph F),
      physicalSmoothEnergy (u ∘ physicalHomeomorph F) x=0 := by
    intro x hx
    simp [physicalSmoothEnergy, fderiv_of_notMem_tsupport ℝ hx]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz] at he
  exact he.trans (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral (physicalSmoothEnergy_integrable hu hs)
      (.of_forall (physicalSmoothEnergy_nonneg u))) hK)

lemma physicalSmoothPullback_energy_subset (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F : ℂ → ℂ))
    {u : EuclideanPlane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hs : HasCompactSupport u)
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F : ℂ → ℂ) z).det|)
    {A U : Set EuclideanPlane} (hA : IsCompact A) (hAU : MapsTo (physicalHomeomorph F) A U) :
    (∫ x in A, physicalSmoothEnergy (u ∘ physicalHomeomorph F) x) ≤
      K*(∫ x in U, physicalSmoothEnergy u x) := by
  apply (physicalSmoothPullback_energy F hF hu hK hD hA).trans
  apply mul_le_mul_of_nonneg_left _ hK
  exact setIntegral_mono_set (physicalSmoothEnergy_integrable hu hs).integrableOn
    (.of_forall (physicalSmoothEnergy_nonneg u)) (Eventually.of_forall (image_subset_iff.mpr hAU))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_HeightTestLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact test pairings converge for the locally bounded pointwise
limit of the actual continuous height functions. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem height_test_integral_tendsto
    (f : ℕ → EuclideanPlane → ℝ) (hf : ∀ n, Continuous (f n))
    {v : EuclideanPlane → ℝ}
    (hp : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (v p)))
    (hb : ∀ K : Set EuclideanPlane, IsCompact K →
      ∃ C : ℝ, ∀ n p, p ∈ K → ‖f n p‖ ≤ C)
    {ψ : EuclideanPlane → ℝ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ p, f n p*ψ p) atTop (𝓝 (∫ p, v p*ψ p)) := by
  obtain ⟨C, hC⟩ := hb (tsupport ψ) hs.isCompact
  apply tendsto_integral_of_dominated_convergence (bound := fun p => C*‖ψ p‖)
  · intro n
    exact (hf n).aestronglyMeasurable.mul hψ.aestronglyMeasurable
  · exact (hψ.integrable_of_hasCompactSupport hs).norm.const_mul C
  · intro n
    apply Eventually.of_forall
    intro p
    by_cases hp : p ∈ tsupport ψ
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC n p hp) (norm_nonneg _)
    · simp only [image_eq_zero_of_notMem_tsupport hp, mul_zero, norm_zero, le_refl]
  · exact Eventually.of_forall (fun p => (hp p).mul_const (ψ p))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakPartialPairingLimit
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak L2 pairings identify derivatives of bounded pointwise limits.
The same pairings retain localized energy estimates on measurable sets. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma weakPartial_of_bounded_pointwise_weak_limit
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (hu : ∀ n, Continuous (u n))
    {C : ℝ} (hb : ∀ n x, ‖u n x‖ ≤ C)
    (hp : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {g : ℕ → EuclideanPlane → ℝ} {G : EuclideanPlane → ℝ} {i : Fin 2}
    (hw : ∀ n, DeGiorgi.HasWeakPartialDeriv i (g n) (u n) univ)
    (hl : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ x, g n x*w x) atTop (𝓝 (∫ x, G x*w x))) :
    DeGiorgi.HasWeakPartialDeriv i G v univ := by
  intro φ hφ hs _
  simp only [Measure.restrict_univ]
  let ψ (x : EuclideanPlane) := fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hψ : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsψ : HasCompactSupport ψ := hs.fderiv_apply (𝕜 := ℝ) _
  have ht := height_test_integral_tendsto u hu hp
    (fun _ _ => ⟨C, fun n x _ => hb n x⟩) hψ hsψ
  have hg := tendsto_pairings_with_memLp_test hl
    (hφ.continuous.memLp_of_hasCompactSupport hs (p := 2) (μ := volume))
  have he (n : ℕ) : (∫ x, u n x*ψ x) = -(∫ x, g n x*φ x) := by
    simpa only [Measure.restrict_univ] using hw n φ hφ hs (subset_univ _)
  exact tendsto_nhds_unique (ht.congr' (.of_forall he)) hg.neg

lemma weak_pairings_restrict
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : ℕ → X → ℝ} {G : X → ℝ}
    (hl : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, u n x*w x ∂μ)
      atTop (𝓝 (∫ x, G x*w x ∂μ)))
    {A : Set X} (hA : MeasurableSet A) {w : X → ℝ} (hw : MemLp w 2 μ) :
    Tendsto (fun n => ∫ x in A, u n x*w x ∂μ) atTop
      (𝓝 (∫ x in A, G x*w x ∂μ)) := by
  have ht := tendsto_pairings_with_memLp_test hl (hw.indicator hA)
  have he (f : X → ℝ) : (∫ x, f x*A.indicator w x ∂μ) = ∫ x in A, f x*w x ∂μ := by
    rw [← integral_indicator hA]
    congr 1
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  simpa only [he] using ht

lemma weak_pair_energy_restrict_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u₀ u₁ : ℕ → X → ℝ} (hu₀ : ∀ n, MemLp (u₀ n) 2 μ)
    (hu₁ : ∀ n, MemLp (u₁ n) 2 μ) (G₀ G₁ : X → ℝ)
    (hm₀ : MemLp G₀ 2 μ) (hm₁ : MemLp G₁ 2 μ)
    (hl₀ : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, u₀ n x*w x ∂μ)
      atTop (𝓝 (∫ x, G₀ x*w x ∂μ)))
    (hl₁ : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, u₁ n x*w x ∂μ)
      atTop (𝓝 (∫ x, G₁ x*w x ∂μ)))
    {A : Set X} (hA : MeasurableSet A) {B : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, (∫ x in A, (u₀ n x)^2+(u₁ n x)^2 ∂μ) ≤ B+ε n) :
    (∫ x in A, (G₀ x)^2+(G₁ x)^2 ∂μ) ≤ B := by
  let hG₀ := hm₀.restrict A
  let hG₁ := hm₁.restrict A
  have he₀ := hG₀.coeFn_toLp
  have he₁ := hG₁.coeFn_toLp
  have hp₀ := weak_pairings_restrict hl₀ hA hm₀
  have hp₁ := weak_pairings_restrict hl₁ hA hm₁
  have ht₀ : Tendsto (fun n => ∫ x in A, u₀ n x*hG₀.toLp G₀ x ∂μ) atTop
      (𝓝 (∫ x in A, hG₀.toLp G₀ x*hG₀.toLp G₀ x ∂μ)) := by
    convert hp₀ using 1
    · funext n
      exact integral_congr_ae (he₀.mono fun x hx => by dsimp only; rw [hx])
    · exact congrArg (𝓝 : ℝ → Filter ℝ) (integral_congr_ae (he₀.mono fun x hx => by dsimp only; rw [hx]))
  have ht₁ : Tendsto (fun n => ∫ x in A, u₁ n x*hG₁.toLp G₁ x ∂μ) atTop
      (𝓝 (∫ x in A, hG₁.toLp G₁ x*hG₁.toLp G₁ x ∂μ)) := by
    convert hp₁ using 1
    · funext n
      exact integral_congr_ae (he₁.mono fun x hx => by dsimp only; rw [hx])
    · exact congrArg (𝓝 : ℝ → Filter ℝ) (integral_congr_ae (he₁.mono fun x hx => by dsimp only; rw [hx]))
  have h := paired_L2_energy_le (fun n => (hu₀ n).restrict A)
    (fun n => (hu₁ n).restrict A) (hG₀.toLp G₀) (hG₁.toLp G₁) hε hb ht₀ ht₁
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [he₀, he₁] with x hx hy
  rw [hx, hy]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothScalarWeakLimit
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded smooth scalar energies give an actual Sobolev limit, retaining
the common subsequence and every L2 derivative pairing. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_scalarSmoothWeakLimit
    {u : EuclideanPlane → ℝ} (hu : MemLp u 2 volume)
    (v : ℕ → EuclideanPlane → ℝ)
    (hv : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n))
    (hgrad : ∀ n i, MemLp (fun x => fderiv ℝ (v n) x (EuclideanSpace.single i 1)) 2 volume)
    {C M : ℝ} (hb : ∀ n x, ‖v n x‖ ≤ C)
    (hp : ∀ x, Tendsto (fun n => v n x) atTop (𝓝 (u x)))
    (henergy : ∀ n, (∫ x, physicalSmoothEnergy (v n) x) ≤ M) :
    Nonempty (ScalarSmoothWeakLimit v u) := by
  let g (i : Fin 2) (n : ℕ) (x : EuclideanPlane) :=
    fderiv ℝ (v n) x (EuclideanSpace.single i 1)
  have hnorm (n : ℕ) (i : Fin 2) : ‖(hgrad n i).toLp (g i n)‖ ≤ M+1 := by
    have he (j : Fin 2) : (∫ x, g j n x^2) = ‖(hgrad n j).toLp (g j n)‖^2 := by
      rw [Lp.norm_toLp, integral_sq_eq_eLpNorm_toReal_sq (hgrad n j)]
    have hm := henergy n
    change (∫ x, g 0 n x^2+g 1 n x^2) ≤ M at hm
    rw [integral_add (hgrad n 0).integrable_sq (hgrad n 1).integrable_sq, he, he] at hm
    fin_cases i
    · change ‖(hgrad n 0).toLp (g 0 n)‖ ≤ M+1
      nlinarith [sq_nonneg (‖(hgrad n 0).toLp (g 0 n)‖-1),
        sq_nonneg ‖(hgrad n 1).toLp (g 1 n)‖]
    · change ‖(hgrad n 1).toLp (g 1 n)‖ ≤ M+1
      nlinarith [sq_nonneg (‖(hgrad n 1).toLp (g 1 n)‖-1),
        sq_nonneg ‖(hgrad n 0).toLp (g 0 n)‖]
  obtain ⟨G₀, _, s₀, hs₀, hl₀⟩ := exists_L2_weak_subsequence volume (g 0)
    (fun n => hgrad n 0) (M+1) (fun n => hnorm n 0)
  obtain ⟨G₁, _, s₁, hs₁, hl₁⟩ := exists_L2_weak_subsequence volume (g 1 ∘ s₀)
    (fun n => hgrad (s₀ n) 1) (M+1) (fun n => hnorm (s₀ n) 1)
  let σ := s₀ ∘ s₁
  have hσ : StrictMono σ := hs₀.comp hs₁
  have hpair₀ (w : Lp ℝ 2 (volume : Measure EuclideanPlane)) :
      Tendsto (fun n => ∫ x, g 0 (σ n) x*w x) atTop (𝓝 (∫ x, G₀ x*w x)) :=
    (hl₀ w).comp hs₁.tendsto_atTop
  let W : DeGiorgi.MemW1pWitness 2 u univ := {
    memLp := by simpa only [Measure.restrict_univ] using hu
    weakGrad := fun x => WithLp.toLp 2 (fun i => if i=0 then G₀ x else G₁ x)
    weakGrad_component_memLp := by
      intro i
      fin_cases i
      · simpa using Lp.memLp G₀
      · simpa using Lp.memLp G₁
    isWeakGrad := by
      intro i
      fin_cases i
      · apply weakPartial_of_bounded_pointwise_weak_limit
          (fun n => (hv (σ n)).continuous) (fun n x => hb (σ n) x)
          (fun x => (hp x).comp hσ.tendsto_atTop)
          (fun n => weakPartial_of_smooth_on isOpen_univ ((hv (σ n)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn 0)
        exact hpair₀
      · apply weakPartial_of_bounded_pointwise_weak_limit
          (fun n => (hv (σ n)).continuous) (fun n x => hb (σ n) x)
          (fun x => (hp x).comp hσ.tendsto_atTop)
          (fun n => weakPartial_of_smooth_on isOpen_univ ((hv (σ n)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn 1)
        exact hl₁ }
  refine ⟨⟨W, σ, hσ, ?_⟩⟩
  intro i w
  fin_cases i
  · exact hpair₀ w
  · exact hl₁ w

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactMapContainment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact-open convergence retains containment of each fixed compact
set in an open neighborhood of its limiting image. -/
open Set Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma eventually_mapsTo_of_compact_convergence
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : ℕ → C(X, Y)} {g : C(X, Y)}
    (hf : Tendsto f atTop (𝓝 g)) {K : Set X} (hK : IsCompact K)
    {U : Set Y} (hU : IsOpen U) (h : MapsTo g K U) :
    ∀ᶠ n in atTop, MapsTo (f n) K U :=
  hf.eventually (ContinuousMap.eventually_mapsTo hK hU h)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalScalarWeakLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained actual smooth principal maps transport the positive
mollifications of a continuous compact Sobolev scalar to an actual weak
Sobolev limit on the image plane. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami CannonPlane

variable {g : PlaneL2} {k R : ℝ} {S : PrincipalSmoothApproximation g k R}

lemma PrincipalMapLimit.inverse_physical_tendsto (L : PrincipalMapLimit S)
    (x : EuclideanPlane) :
    Tendsto (fun n => physicalHomeomorph (S.map (L.index n)).symm x) atTop
      (𝓝 (physicalHomeomorph L.map.symm x)) := by
  have h := (continuous_eval_const (complexPlaneCoordinates x)).tendsto
    (homeomorphMap L.map.symm) |>.comp L.inverse
  exact complexPlaneCoordinates.symm.continuous.continuousAt.tendsto.comp h

lemma PrincipalMapLimit.scalar_approximation_smooth (L : PrincipalMapLimit S)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (principalScalarApproximation L u n) :=
  (planarMollification_smooth hu.locallyIntegrable n).comp
    (physicalHomeomorph_contDiff _ (S.inverse_smooth _))

lemma PrincipalMapLimit.scalar_approximation_compact (L : PrincipalMapLimit S)
    {u : EuclideanPlane → ℝ} (hs : HasCompactSupport u) (n : ℕ) :
    HasCompactSupport (principalScalarApproximation L u n) :=
  (planarMollification_hasCompactSupport hs n).comp_homeomorph _

lemma PrincipalMapLimit.scalar_approximation_tendsto (L : PrincipalMapLimit S)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (x : EuclideanPlane) :
    Tendsto (fun n => principalScalarApproximation L u n x) atTop
      (𝓝 ((u ∘ physicalHomeomorph L.map.symm) x)) :=
  planarMollification_tendsto_moving hu (L.inverse_physical_tendsto x)

lemma PrincipalMapLimit.scalar_weak_limit (L : PrincipalMapLimit S)
    (hk : 0 ≤ k) (hk1 : k < 1) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) :
    Nonempty (ScalarSmoothWeakLimit (principalScalarApproximation L u)
      (u ∘ physicalHomeomorph L.map.symm)) := by
  let K := (1+k)/(1-k)
  have hK : 0 ≤ K := div_nonneg (by linarith) (by linarith)
  have hdist (n : ℕ) := (smooth_beltrami_two_sided_distortion (S.map (L.index n))
    (S.smooth _) (S.inverse_smooth _) (S.coefficient _) hk hk1
    (S.coefficient_bound _) (S.equation _)).2
  have he := planarMollification_energy_tendsto W hs univ
  simp only [Measure.restrict_univ] at he
  obtain ⟨B, hB⟩ := he.bddAbove_range
  obtain ⟨C, hC⟩ := hu.bounded_above_of_compact_support hs
  have hb (n : ℕ) (x : EuclideanPlane) : ‖principalScalarApproximation L u n x‖ ≤ C := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (planarMollification_mem_Icc hu.aestronglyMeasurable
      (fun y => abs_le.mp (by simpa only [Real.norm_eq_abs] using hC y)) n _)
  apply exists_scalarSmoothWeakLimit
    ((hu.comp (physicalHomeomorph L.map.symm).continuous).memLp_of_hasCompactSupport
      (hs.comp_homeomorph _)) _ (L.scalar_approximation_smooth hu)
    (fun n i => physicalSmoothPartial_memLp (L.scalar_approximation_smooth hu n)
      (L.scalar_approximation_compact hs n) i) hb (L.scalar_approximation_tendsto hu)
  intro n
  apply (physicalSmoothPullback_energy_global (S.map (L.index n)).symm
    (S.inverse_smooth _) (planarMollification_smooth hu.locallyIntegrable n)
    (planarMollification_hasCompactSupport hs n) hK (hdist n)).trans
  exact mul_le_mul_of_nonneg_left (hB (mem_range_self n)) hK

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarWeakLimitZeroSet
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing energy on a fixed measurable set survives the actual
retained weak derivative limit. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma ScalarSmoothWeakLimit.gradient_zero_of_energy
    {v : ℕ → EuclideanPlane → ℝ} {u : EuclideanPlane → ℝ}
    (L : ScalarSmoothWeakLimit v u)
    (hm : ∀ n i, MemLp (fun x => fderiv ℝ (v n) x (EuclideanSpace.single i 1)) 2 volume)
    {A : Set EuclideanPlane} (hA : MeasurableSet A)
    (ht : Tendsto (fun n => ∫ x in A, physicalSmoothEnergy (v n) x) atTop (𝓝 0)) :
    ∀ i, ∀ᵐ x ∂volume, x ∈ A → L.witness.weakGrad x i=0 := by
  have hG (i : Fin 2) : MemLp (fun x => L.witness.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using L.witness.weakGrad_component_memLp i
  have he := weak_pair_energy_restrict_le
    (fun n => hm (L.index n) 0) (fun n => hm (L.index n) 1)
    (fun x => L.witness.weakGrad x 0) (fun x => L.witness.weakGrad x 1)
    (hG 0) (hG 1) (L.pairing 0) (L.pairing 1) hA
    (B := 0) (ht.comp L.index_strict.tendsto_atTop)
    (.of_forall fun n => le_of_eq (zero_add _).symm)
  have hz : (∫ x in A, (L.witness.weakGrad x 0)^2+(L.witness.weakGrad x 1)^2)=0 :=
    le_antisymm he (integral_nonneg fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => add_nonneg (sq_nonneg (L.witness.weakGrad x 0))
      (sq_nonneg (L.witness.weakGrad x 1)))
    (((hG 0).restrict A).integrable_sq.add ((hG 1).restrict A).integrable_sq)).mp hz
  intro i
  apply (ae_restrict_iff' hA).mp
  filter_upwards [hae] with x hx
  change (L.witness.weakGrad x 0)^2+(L.witness.weakGrad x 1)^2=(0 : ℝ) at hx
  fin_cases i
  · change L.witness.weakGrad x 0=0
    nlinarith [sq_nonneg (L.witness.weakGrad x 1)]
  · change L.witness.weakGrad x 1=0
    nlinarith [sq_nonneg (L.witness.weakGrad x 0)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmallGradientNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integrable gradient that vanishes on a closed set has arbitrarily
small energy on open neighborhoods of that set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_open_integral_small_of_zero_on_closed
    {f : EuclideanPlane → ℝ} (hf : Integrable f volume)
    {F : Set EuclideanPlane} (hF : IsClosed F)
    (hz : ∀ᵐ x ∂volume, x ∈ F → f x=0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set EuclideanPlane, IsOpen U ∧ F ⊆ U ∧ (∫ x in U, f x) < ε := by
  let U (n : ℕ) := thickening (1/((n : ℝ)+1)) F
  have ho (n : ℕ) : IsOpen (U n) := isOpen_thickening
  have hsub (n : ℕ) : F ⊆ U n := by
    intro x hx
    exact mem_thickening_iff.mpr ⟨x, hx, by simp <;> positivity⟩
  have ha : Antitone U := by
    intro m n hmn
    apply thickening_mono
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hcap : (⋂ n, U n) = F := by
    apply Subset.antisymm
    · intro x hx
      rw [← hF.closure_eq, closure_eq_iInter_thickening]
      refine mem_iInter.mpr fun r => mem_iInter.mpr fun hr => ?_
      have ht := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hr)
      obtain ⟨n, hn⟩ := ht.exists
      exact thickening_mono hn.le F (mem_iInter.mp hx n)
    · exact subset_iInter hsub
  have ht := tendsto_setIntegral_of_antitone (fun n => (ho n).measurableSet) ha
    ⟨0, hf.integrableOn⟩
  have hzero : (∫ x in F, f x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem hF.measurableSet] with x hx hxF
    exact hx hxF
  rw [hcap, hzero] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨U n, ho n, hsub n, hn⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalScalarZeroSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero gradient on a compact source set is preserved by the actual
principal-map limit. This follows from compact containment and localized
smooth energy bounds, without invoking a quasiconformal chain rule. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami CannonPlane
variable {g : PlaneL2} {k R : ℝ} {S : PrincipalSmoothApproximation g k R}

lemma PrincipalMapLimit.inverse_mapsTo_neighborhood (L : PrincipalMapLimit S)
    {F U : Set EuclideanPlane} (hF : IsCompact F) (hU : IsOpen U) (hFU : F ⊆ U) :
    ∀ᶠ n in atTop, MapsTo (physicalHomeomorph (S.map (L.index n)).symm)
      (physicalHomeomorph L.map '' F) U := by
  let A := physicalHomeomorph L.map '' F
  have hA : IsCompact A := hF.image (physicalHomeomorph L.map).continuous
  have hlim : MapsTo (homeomorphMap L.map.symm) (complexPlaneCoordinates '' A)
      (complexPlaneCoordinates.symm ⁻¹' U) := by
    rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    change physicalHomeomorph L.map.symm (physicalHomeomorph L.map x) ∈ U
    rw [← physicalHomeomorph_symm, Homeomorph.symm_apply_apply]
    exact hFU hx
  have he := eventually_mapsTo_of_compact_convergence L.inverse
    (hA.image complexPlaneCoordinates.continuous) (hU.preimage complexPlaneCoordinates.symm.continuous) hlim
  filter_upwards [he] with n hn x hx
  exact hn (mem_image_of_mem complexPlaneCoordinates hx)

lemma PrincipalMapLimit.scalar_energy_zero_set (L : PrincipalMapLimit S)
    (hk : 0 ≤ k) (hk1 : k < 1) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hz : ∀ i, ∀ᵐ x ∂volume, x ∈ F → W.weakGrad x i=0) :
    Tendsto (fun n => ∫ x in physicalHomeomorph L.map '' F,
      physicalSmoothEnergy (principalScalarApproximation L u n) x) atTop (𝓝 0) := by
  let K := (1+k)/(1-k)
  have hK : 0 ≤ K := div_nonneg (by linarith) (by linarith)
  let e (x : EuclideanPlane) := (W.weakGrad x 0)^2+(W.weakGrad x 1)^2
  have hg (i : Fin 2) : MemLp (fun x => W.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i
  have hi : Integrable e volume := (hg 0).integrable_sq.add (hg 1).integrable_sq
  have hez : ∀ᵐ x ∂volume, x ∈ F → e x=0 := by
    filter_upwards [hz 0, hz 1] with x h0 h1 hx
    simp only [e, h0 hx, h1 hx, zero_pow two_ne_zero, add_zero]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let t := ε/(K+1)
  have ht : 0 < t := div_pos hε (by linarith)
  have hKt : K*t < ε := by
    dsimp only [t]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < K+1)).mpr
    nlinarith
  obtain ⟨U, hU, hFU, heU⟩ := exists_open_integral_small_of_zero_on_closed hi hF.isClosed hez ht
  have henergy := planarMollification_energy_tendsto W hs U
  have hen : ∀ᶠ n in atTop, (∫ x in U, physicalSmoothEnergy (planarMollification u n) x) < t :=
    henergy.eventually (gt_mem_nhds heU)
  filter_upwards [L.inverse_mapsTo_neighborhood hF hU hFU, hen] with n hn he
  have hd := (smooth_beltrami_two_sided_distortion (S.map (L.index n))
    (S.smooth _) (S.inverse_smooth _) (S.coefficient _) hk hk1
    (S.coefficient_bound _) (S.equation _)).2
  have hb := physicalSmoothPullback_energy_subset (S.map (L.index n)).symm
    (S.inverse_smooth _) (planarMollification_smooth hu.locallyIntegrable n)
    (planarMollification_hasCompactSupport hs n) hK hd
    (hF.image (physicalHomeomorph L.map).continuous) hn
  have hsmall := (hb.trans (mul_le_mul_of_nonneg_left he.le hK)).trans_lt hKt
  have hnn : 0 ≤ ∫ x in physicalHomeomorph L.map '' F,
      physicalSmoothEnergy (principalScalarApproximation L u n) x :=
    integral_nonneg fun x => physicalSmoothEnergy_nonneg _ x
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnn]
  change (∫ x in physicalHomeomorph L.map '' F,
    physicalSmoothEnergy (planarMollification u n ∘ physicalHomeomorph (S.map (L.index n)).symm) x) < ε
  exact hsmall

lemma PrincipalMapLimit.scalar_transport_zero_set (L : PrincipalMapLimit S)
    (hk : 0 ≤ k) (hk1 : k < 1) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hz : ∀ i, ∀ᵐ x ∂volume, x ∈ F → W.weakGrad x i=0) :
    ∃ V : DeGiorgi.MemW1pWitness 2 (u ∘ physicalHomeomorph L.map.symm) univ,
      ∀ i, ∀ᵐ x ∂volume, x ∈ physicalHomeomorph L.map '' F → V.weakGrad x i=0 := by
  obtain ⟨T⟩ := L.scalar_weak_limit hk hk1 hu hs W
  exact ⟨T.witness, T.gradient_zero_of_energy
    (fun n i => physicalSmoothPartial_memLp (L.scalar_approximation_smooth hu n)
      (L.scalar_approximation_compact hs n) i)
    (hF.image (physicalHomeomorph L.map).continuous).measurableSet
    (L.scalar_energy_zero_set hk hk1 hu hs W hF hz)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalScalarSolverProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The internal conductivity/scalar interface is constructed from the
actual principal smooth approximation. No quasiconformal Sobolev calculus
is assumed. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_principal_real_with_scalar_pullback
    (q : EuclideanPlane → ℝ) (hq : AEStronglyMeasurable q volume)
    {F : Set EuclideanPlane} (hF : IsCompact F) (hFzero : ∀ x ∉ F, q x=0)
    (k : ℝ≥0) (hk : k<1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))),
      Tendsto (fun z => φ z-z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      (∀ᵐ x ∂volume,
        planarDbar (D.realGradient x 0) (D.realGradient x 1)
          (D.imagGradient x 0) (D.imagGradient x 1) =
        q x • star (planarDz (D.realGradient x 0) (D.realGradient x 1)
          (D.imagGradient x 0) (D.imagGradient x 1))) ∧
      CompactScalarPullback φ := by
  obtain ⟨g, μ, hm, hbound, hzero, hreal, he⟩ :=
    exists_complex_real_beltrami_l2_reduction q hq hF hFzero k hk hb
  obtain ⟨R, hR⟩ := (hF.image complexPlaneCoordinates.continuous).isBounded.subset_ball 0
  have hs : ∀ z, R ≤ ‖z‖ → μ z=0 := by
    intro z hz
    apply hzero
    intro hzF
    have hh := hR hzF
    simp only [Metric.mem_ball, dist_zero_right] at hh
    linarith
  have hk0 : 0 ≤ (k : ℝ) := k.2
  have hk1 : (k : ℝ) < 1 := by exact_mod_cast hk
  obtain ⟨S⟩ := exists_principal_smooth_approximation μ hm.aestronglyMeasurable
    hk0 hk1 hbound hs g he
  let T := max (R+2) 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨L⟩ := S.exists_principal_limit_data
    (exteriorCoefficientAreaTheorem planarSchoenflies unorientedFiniteCircleGreenFormula)
    hk0 hk1 hT (le_max_left _ _)
  refine ⟨L.map, principalPhysicalWitness L.map g L.weak, L.principal,
    principalPhysicalWitness_equation L.map g L.weak q hreal, ?_⟩
  intro u hu hsupport W A hA hz
  exact L.scalar_transport_zero_set hk0 hk1 hu hsupport W hA hz

lemma principalConductivityScalarSolver_oai : PrincipalConductivityScalarSolver := by
  intro F hF n hn
  obtain ⟨φ, D, ht, he, hscalar⟩ := exists_principal_real_with_scalar_pullback
    (conductivityCoefficient F n) (conductivityCoefficient_memLp hF n).aestronglyMeasurable
    hF (fun x hx => indicator_of_notMem hx _)
    (conductivityRatio n hn) (conductivityRatio_lt_one n hn)
    (.of_forall (conductivityCoefficient_bound F n hn))
  refine ⟨φ, D, ht, ?_, hscalar⟩
  filter_upwards [he] with x hx
  have hk : 0 ≤ conductivityValue F n x := by
    classical
    unfold conductivityValue
    split <;> positivity
  apply (conductivity_system_iff hk).mp
  rwa [conductivityCoefficient_ratio] at hx

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.principalConductivityScalarSolver_oai := @OAI.CircleDomainRigidity.principalConductivityScalarSolver_oai
