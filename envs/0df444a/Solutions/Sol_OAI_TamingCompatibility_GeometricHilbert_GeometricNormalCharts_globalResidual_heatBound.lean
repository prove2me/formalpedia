-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalResidual_heatBound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:21:45.513984+00:00
-- url     : https://prove2.me/submissions/7e539469-f5bd-4c95-b37c-ffa846aa75ef

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc023
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledB_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_residualCoordinate_gaussian
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalMetricCalculus_volumeDensity_pos

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_FlatHeat
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open _root_.MeasureTheory Set
open scoped RealInnerProductSpace ContDiff

lemma heat_nonneg (t : ℝ) (z : V) : 0 ≤ heat t z := by
  unfold heat
  positivity

lemma gaussian_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : V => Real.exp (-b*‖z‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (b:ℂ)) hb 0 0).norm
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h

lemma gaussian_integral {b : ℝ} (hb : 0 < b) :
    (∫ z : V, Real.exp (-b*‖z‖^2)) = (Real.pi/b)^2 := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) hb
  norm_num only [finrank_euclideanSpace, Fintype.card_fin, show (4:ℝ)/2 = 2 by norm_num,
    Real.rpow_natCast] at h
  simpa only [Real.rpow_ofNat] using h

lemma heat_integrable {t : ℝ} (ht : 0 < t) : Integrable (heat t) := by
  have h := (gaussian_integrable (show 0 < 1/(4*t) by positivity)).const_mul ((4*Real.pi*t)⁻¹^2)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  unfold heat
  congr 2
  ring

lemma heat_integral {t : ℝ} (ht : 0 < t) : (∫ z : V, heat t z) = 1 := by
  have he : heat t = fun z : V => (4*Real.pi*t)⁻¹^2 * Real.exp (-(1/(4*t))*‖z‖^2) := by
    funext z
    unfold heat
    congr 2
    ring
  rw [he, integral_const_mul, gaussian_integral (by positivity)]
  field_simp

lemma heat_hasFDerivAt (t : ℝ) (z : V) :
    HasFDerivAt (heat t) ((-heat t z/(2*t)) • innerSL ℝ z) z := by
  have h := ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.neg.mul_const (4*t)⁻¹).exp).const_mul
    ((4*Real.pi*t)⁻¹^2))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext w
  simp only [heat, smul_apply, neg_apply,
    smul_eq_mul, innerSL_apply_apply, Pi.neg_apply]
  ring_nf

lemma heat_fderiv (t : ℝ) (z w : V) :
    fderiv ℝ (heat t) z w = -heat t z/(2*t) * ⟪z,w⟫ := by
  rw [(heat_hasFDerivAt t z).fderiv]
  rfl

lemma heat_directional_hasFDerivAt (t : ℝ) (z v : V) :
    HasFDerivAt (fun y => fderiv ℝ (heat t) y v)
      ((heat t z * ⟪z,v⟫/(4*t^2)) • innerSL ℝ z -
        (heat t z/(2*t)) • innerSL ℝ v) z := by
  have hlin : HasFDerivAt (fun y : V => ⟪y,v⟫) (innerSL ℝ v) z := by
    convert! (innerSL ℝ v).hasFDerivAt (x := z) using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    exact real_inner_comm v y
  have h := ((heat_hasFDerivAt t z).neg.mul_const (2*t)⁻¹).mul hlin
  have he : (fun y => fderiv ℝ (heat t) y v) =
      (fun y => -heat t y*(2*t)⁻¹ * ⟪y,v⟫) := by
    funext y
    rw [heat_fderiv]
    ring
  rw [he]
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext u
  simp only [sub_apply, smul_apply, innerSL_apply_apply, add_apply, neg_apply,
    smul_eq_mul, Pi.neg_apply]
  ring

lemma heat_hessian (t : ℝ) (z u v : V) :
    fderiv ℝ (fun y => fderiv ℝ (heat t) y v) z u =
      heat t z * (⟪z,u⟫*⟪z,v⟫/(4*t^2) - ⟪u,v⟫/(2*t)) := by
  rw [(heat_directional_hasFDerivAt t z v).fderiv]
  simp only [sub_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm (y := v)]
  ring

lemma gaussian_weight_absorption {t : ℝ} (ht : 0 < t) (z : V) (n : ℕ) :
    ‖z‖^(2*n) * heat t z ≤ 4 * (8*t)^n * (n.factorial : ℝ) * heat (2*t) z := by
  let a : ℝ := ‖z‖^2/(8*t)
  have ha : 0 ≤ a := by dsimp [a] <;> positivity
  have h := Real.pow_div_factorial_le_exp a ha n
  have hf : 0 < (n.factorial : ℝ) := by positivity
  have h1 : a^n * Real.exp (-a) ≤ (n.factorial : ℝ) := by
    calc
      _ ≤ ((n.factorial : ℝ) * Real.exp a) * Real.exp (-a) :=
        mul_le_mul_of_nonneg_right (by nlinarith [(div_le_iff₀ hf).mp h]) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; simp
  have hz : ‖z‖^(2*n) = (8*t)^n*a^n := by
    rw [← mul_pow, pow_mul]
    congr 1
    dsimp [a]
    field_simp
  have hH : heat t z = 4 * heat (2*t) z * Real.exp (-a) := by
    have hp : (4*Real.pi*t)⁻¹^2 = 4*(4*Real.pi*(2*t))⁻¹^2 := by field_simp <;> ring
    have he : -‖z‖^2/(4*t) = -a + -a := by dsimp [a] <;> ring
    have he2 : -‖z‖^2/(4*(2*t)) = -a := by dsimp [a] <;> ring
    unfold heat
    rw [hp, he, he2, Real.exp_add]
    ring
  have hp := heat_nonneg (2*t) z
  rw [hz, hH]
  calc
    _ = (4*(8*t)^n*heat (2*t) z) * (a^n*Real.exp (-a)) := by ring
    _ ≤ (4*(8*t)^n*heat (2*t) z) * (n.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

end TamingCompatibility.GeometricHilbert.FlatHeat

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets

open Filter
open scoped ContDiff Topology
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma slice_fderiv_contDiffAt (F : P × V → W) {x : P × V}
    (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (fun y : P × V => fderiv ℝ (fun z => F (y.1,z)) y.2) x := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y :=
    ((hF.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by norm_num)).mono
      fun y hy => hy.differentiableAt (by norm_num)
  apply (dpos_contDiffAt F x hF).congr_of_eventuallyEq
  filter_upwards [hd] with y hy
  exact (dpos_eq_at F y.1 y.2 hy).symm

end TamingCompatibility.GeometricHilbert.UniformJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstMatrixJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus

section MatrixFamilies
open UniformJets
open scoped ContDiff
variable {P V W Q ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma firstMatrix_joint (e : ι → V) (a : ι → P × V → W →L[ℝ] Q)
    (b : P × V → W →L[ℝ] Q) (ρ : P × V → ℝ) {x : P × V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hρx : ρ x ≠ 0) (j : ι) :
    ContDiffAt ℝ ∞ (fun y : P × V => firstMatrix e (fun i z => a i (y.1,z))
      (fun z => b (y.1,z)) (fun z => ρ (y.1,z)) j y.2) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hp (i : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      principalMatrix (fun k z => a k (y.1,z)) (fun z => ρ (y.1,z)) i j y.2) x :=
    (S.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_comp (ha j)
  have hsum := ContDiffAt.sum (s := Finset.univ) (fun i _ =>
    (slice_fderiv_contDiffAt _ (hp i)).clm_apply (contDiffAt_const (c := e i)))
  exact (((hρ.inv hρx).neg.smul hsum).add
    ((S.contDiff.contDiffAt.comp x hb).clm_comp (ha j))).sub
      ((S.contDiff.contDiffAt.comp x (ha j)).clm_comp hb)

lemma zeroMatrix_joint (e : ι → V) (a : ι → P × V → W →L[ℝ] Q)
    (b : P × V → W →L[ℝ] Q) (ρ : P × V → ℝ) {x : P × V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hρx : ρ x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : P × V => zeroMatrix e (fun i z => a i (y.1,z))
      (fun z => b (y.1,z)) (fun z => ρ (y.1,z)) y.2) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hp (i : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      lowerMatrix (fun k z => a k (y.1,z)) (fun z => b (y.1,z))
        (fun z => ρ (y.1,z)) i y.2) x :=
    (S.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_comp hb
  have hsum := ContDiffAt.sum (s := Finset.univ) (fun i _ =>
    (slice_fderiv_contDiffAt _ (hp i)).clm_apply (contDiffAt_const (c := e i)))
  exact ((hρ.inv hρx).neg.smul hsum).add
    ((S.contDiff.contDiffAt.comp x hb).clm_comp hb)

end MatrixFamilies
open UniformJets FirstJetGauge OrthogonalJets
open scoped ContDiff
variable {P V W ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma gaugeFirst_joint (e : ι → V) (a : ι → ι → P × V → ℝ)
    (b : ι → P × V → W →L[ℝ] W) (U : P × V → W →L[ℝ] W) {x : P × V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hU : ContDiffAt ℝ ∞ U x) (j : ι) :
    ContDiffAt ℝ ∞ (fun y : P × V => gaugeFirst e (fun i j z => a i j (y.1,z))
      (fun j z => b j (y.1,z)) (fun z => U (y.1,z)) j y.2) x := by
  exact (adjointCLM.contDiff.contDiffAt.comp x hU).clm_comp
    (((hb j).clm_comp hU).sub (ContDiffAt.sum (fun i _ =>
      ((ha i j).add (ha j i)).smul
        ((slice_fderiv_contDiffAt U hU).clm_apply (contDiffAt_const (c := e i))))))

lemma gaugeZero_joint (e : ι → V) (a : ι → ι → P × V → ℝ)
    (b : ι → P × V → W →L[ℝ] W) (c U : P × V → W →L[ℝ] W) {x : P × V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hc : ContDiffAt ℝ ∞ c x) (hU : ContDiffAt ℝ ∞ U x) :
    ContDiffAt ℝ ∞ (fun y : P × V => gaugeZero e (fun i j z => a i j (y.1,z))
      (fun j z => b j (y.1,z)) (fun z => c (y.1,z)) (fun z => U (y.1,z)) y.2) x := by
  have hdu (j : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      fderiv ℝ (fun z => U (y.1,z)) y.2 (e j)) x :=
    (slice_fderiv_contDiffAt U hU).clm_apply contDiffAt_const
  have hddu (i j : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      fderiv ℝ (fun z => fderiv ℝ (fun w => U (y.1,w)) z (e j)) y.2 (e i)) x :=
    (slice_fderiv_contDiffAt _ (hdu j)).clm_apply contDiffAt_const
  exact (adjointCLM.contDiff.contDiffAt.comp x hU).clm_comp
    (((hc.clm_comp hU).add (ContDiffAt.sum (fun i _ => (hb i).clm_comp (hdu i)))).sub
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => (ha i j).smul (hddu i j)))

lemma gauge_joint (q : ι → V →L[ℝ] ℝ) (b : ι → P → W →L[ℝ] W)
    {x : P × V} (hb : ∀ i, ContDiffAt ℝ ∞ (b i) x.1) :
    ContDiffAt ℝ ∞ (fun y : P × V => gauge (halfJet q (fun i => b i y.1)) y.2) x := by
  have he : ContDiffAt ℝ ∞ (NormedSpace.exp : (W →L[ℝ] W) → (W →L[ℝ] W))
      (halfJet q (fun i => b i x.1) x.2) := (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt
  apply he.comp x
  simp only [halfJet, sum_apply, ContinuousLinearMap.smulRight_apply]
  exact ContDiffAt.sum fun i _ =>
    ((q i).contDiff.contDiffAt.comp x contDiffAt_snd).smul
      (((hb i).comp x contDiffAt_fst).const_smul (1/2 : ℝ))

end TamingCompatibility.GeometricHilbert.OperatorCalculus

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity Filter Set
open scoped ContDiff Topology
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedAddCommGroupMetricTensorV_1
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.instNormedSpaceRealMetricTensorV_1
lemma principal_contDiffAt_regular {M : MetricTensor (V := V)} (hM : M ∈ regularMetrics)
    (i j : Fin 4) : ContDiffAt ℝ ∞ (fun L => principal L i j) M :=
  ContDiffAt.inner ℝ (((hM.2.contDiffAt_map_inverse.comp M metricOperator.contDiff.contDiffAt).clm_apply
    contDiffAt_const)) contDiffAt_const

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_4
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_4
lemma normalPrincipal_smooth (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : normalMetric g B x ∈ regularMetrics) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (normalPrincipal g B i j) x :=
  (principal_contDiffAt_regular hx i j).comp x (normalMetric_contDiff g B hg hB).contDiffAt

lemma normalFirst_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) (j : Fin 4) :
    ContDiffAt ℝ ∞ (normalFirst J α ht p D g B j) x :=
  firstMatrix_joint EuclideanEnergy.e (fun i y => pulledA J α ht p D g B y.1 i y.2)
    (fun y => pulledB J α ht p D g B y.1 y.2) (normalDensity g B)
    (pulledA_joint J α ht p D g B hg hB hx.1)
    (pulledB_joint J α hs ht p D g B hg hB hx.1)
    (normalDensity_smooth g B hg hB hx.2) (ne_of_gt (volumeDensity_pos hx.2)) j

lemma normalZero_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (normalZero J α ht p D g B) x :=
  zeroMatrix_joint EuclideanEnergy.e (fun i y => pulledA J α ht p D g B y.1 i y.2)
    (fun y => pulledB J α ht p D g B y.1 y.2) (normalDensity g B)
    (pulledA_joint J α ht p D g B hg hB hx.1)
    (pulledB_joint J α hs ht p D g B hg hB hx.1)
    (normalDensity_smooth g B hg hB hx.2) (ne_of_gt (volumeDensity_pos hx.2))

attribute [local irreducible] normalFirst

lemma normalGauge_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : (x.1,0) ∈ normalDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (normalGauge J α ht p D g B) x := by
  have hc : ContDiffAt ℝ ∞ (fun q : Space => (q,(0 : Space))) x.1 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hf (i : Fin 4) : ContDiffAt ℝ ∞
      (fun q : Space => normalFirst J α ht p D g B i (q,0)) x.1 := by
    have hi : ContDiffAt ℝ ∞ (normalFirst J α ht p D g B i) (x.1,0) :=
      normalFirst_smooth J α ht p D g B hs hg hB hx i
    exact hi.comp x.1 hc
  exact gauge_joint (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
    (fun i q => normalFirst J α ht p D g B i (q,0)) (x := x) hf

lemma gaugedFirst_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ gaugedDomain J α ht p D g B) (j : Fin 4) :
    ContDiffAt ℝ ∞ (gaugedFirst J α ht p D g B j) x :=
  gaugeFirst_joint EuclideanEnergy.e (normalPrincipal g B) (normalFirst J α ht p D g B)
    (normalGauge J α ht p D g B) (normalPrincipal_smooth g B hg hB hx.1.2)
    (normalFirst_smooth J α ht p D g B hs hg hB hx.1)
    (normalGauge_smooth J α ht p D g B hs hg hB hx.2) j

lemma gaugedZero_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ gaugedDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (gaugedZero J α ht p D g B) x :=
  gaugeZero_joint EuclideanEnergy.e (normalPrincipal g B) (normalFirst J α ht p D g B)
    (normalZero J α ht p D g B) (normalGauge J α ht p D g B)
    (normalPrincipal_smooth g B hg hB hx.1.2)
    (normalFirst_smooth J α ht p D g B hs hg hB hx.1)
    (normalZero_smooth J α ht p D g B hs hg hB hx.1)
    (normalGauge_smooth J α ht p D g B hs hg hB hx.2)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCutoffSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets
open Set Metric
open scoped ContDiff
variable {P V W A B : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma linear_bound_on_tube (F : P × V → W) (K : Set P) (hK : IsCompact K)
    {r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContDiffAt ℝ ∞ F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ r →
      ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖ := by
  have hpc : ContinuousOn (dpos F) (K ×ˢ closedBall (0 : V) r) :=
    fun x hx => ((dpos_contDiffAt F x (hF x hx)).continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := (hK.prod (isCompact_closedBall (0 : V) r)).exists_bound_of_continuousOn hpc
  refine ⟨max C 0,le_max_right _ _,fun p hp z hz => ?_⟩
  have hd (u : V) (hu : u ∈ closedBall (0 : V) r) : DifferentiableAt ℝ F (p,u) :=
    (hF (p,u) ⟨hp,hu⟩).differentiableAt (by simp)
  have hb (u : V) (hu : u ∈ closedBall (0 : V) r) :
      ‖fderiv ℝ (fun v => F (p,v)) u‖ ≤ max C 0 := by
    rw [←dpos_eq_at F p u (hd u hu)]
    exact (hC (p,u) ⟨hp,hu⟩).trans (le_max_left _ _)
  simpa using (convex_closedBall (0 : V) r).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (hd u hu).comp u ((differentiableAt_const p).prodMk differentiableAt_id)) hb
    (show (0 : V) ∈ closedBall 0 r by simpa using hr)
    (show z ∈ closedBall 0 r by simpa using hz)

end TamingCompatibility.GeometricHilbert.UniformJets

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCutoffFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.CutoffFamilies
open OperatorCalculus NormalHeatResidual UniformJets FlatHeat Filter Set Metric
open scoped Topology ContDiff
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma principal_smooth (a : Fin 4 → Fin 4 → P × V → ℝ) (χ : V → ℝ)
    (hχ : ContDiff ℝ ∞ χ) {x : P × V} (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) :
    ContDiffAt ℝ ∞ (principal a χ) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact contDiffAt_const.add ((hχ.contDiffAt.comp x contDiffAt_snd).mul ((ha i j).sub contDiffAt_const))

lemma first_smooth (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (χ : V → ℝ)
    (hχ : ContDiff ℝ ∞ χ) {x : P × V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x) :
    ContDiffAt ℝ ∞ (first a b χ) x := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  apply contDiffAt_pi.mpr
  intro j
  exact ((hχ.contDiffAt.comp x contDiffAt_snd).smul (hb j)).sub
    ((ContDiffAt.sum (fun i _ => ((ha i j).add (ha j i)).mul
      ((hd.contDiffAt.comp x contDiffAt_snd).clm_apply contDiffAt_const))).smul contDiffAt_const)

lemma zero_smooth (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W) (χ : V → ℝ)
    (hχ : ContDiff ℝ ∞ χ) {x : P × V}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (a i j) x) (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hc : ContDiffAt ℝ ∞ c x) : ContDiffAt ℝ ∞ (zero a b c χ) x := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdd (j : Fin 4) : ContDiff ℝ ∞ (fderiv ℝ (fun y => fderiv ℝ χ y
      (EuclideanSpace.basisFun (Fin 4) ℝ j))) :=
    (hd.clm_apply contDiff_const).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact (((hχ.contDiffAt.comp x contDiffAt_snd).smul hc).sub
    ((ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => (ha i j).mul
      (((hdd j).contDiffAt.comp x contDiffAt_snd).clm_apply contDiffAt_const)))).smul contDiffAt_const)).add
    (ContDiffAt.sum (fun i _ => (((hd.contDiffAt.comp x contDiffAt_snd).clm_apply contDiffAt_const).smul (hb i))))

end TamingCompatibility.GeometricHilbert.CutoffFamilies

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatJointSmooth
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open scoped ContDiff

lemma heat_joint_contDiffAt {x : ℝ × V} (hx : x.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun v : ℝ × V => heat v.1 v.2) x := by
  have hp : ContDiffAt ℝ ∞ (fun v : ℝ × V => 4*Real.pi*v.1) x :=
    contDiffAt_const.mul contDiffAt_fst
  have hi : ContDiffAt ℝ ∞ (fun v : ℝ × V => (4*Real.pi*v.1)⁻¹^2) x :=
    (hp.inv (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx)).pow 2
  have hn : ContDiffAt ℝ ∞ (fun v : ℝ × V => -‖v.2‖^2) x :=
    (contDiffAt_snd.norm_sq (𝕜 := ℝ)).neg
  have he : ContDiffAt ℝ ∞ (fun v : ℝ × V => -‖v.2‖^2/(4*v.1)) x :=
    hn.div (contDiffAt_const.mul contDiffAt_fst) (mul_ne_zero (by norm_num) hx)
  exact hi.mul he.exp

end TamingCompatibility.GeometricHilbert.FlatHeat

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalInverse
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalInverseMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalInverseMetricTensorNormedSpace
variable (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
  (q : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q = Bq)

lemma geometricNormalChart_symm_right {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q Bq hBq).target) :
    normalMap g B x.1 ((geometricNormalChart g B hg hB q Bq hBq).symm x).2 = x.2 := by
  have he := congrArg Prod.snd ((geometricNormalChart g B hg hB q Bq hBq).right_inv hx)
  change normalMap g B ((geometricNormalChart g B hg hB q Bq hBq).symm x).1
    ((geometricNormalChart g B hg hB q Bq hBq).symm x).2 = x.2 at he
  rw [geometricNormalChart_symm_fst g B hg hB q Bq hBq hx] at he
  exact he

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelExtension
open Set Filter
open scoped Topology ContDiff
variable {E F W : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup W]
attribute [local instance] Classical.propDecidable

lemma support_push_subset (C : OpenPartialHomeomorph E F) (f : E → W) (K : Set E)
    (hf : Function.support f ⊆ K) : Function.support (push C f) ⊆ C '' K := by
  intro y hy
  have ht : y ∈ C.target := by
    by_contra h
    exact hy (by simp [push,h])
  refine ⟨C.symm y,hf ?_,C.right_inv ht⟩
  simpa [Function.mem_support,push,ht] using hy

lemma tsupport_push_subset (C : OpenPartialHomeomorph E F) (f : E → W) (K : Set E)
    (hK : IsCompact K) (hKC : K ⊆ C.source) (hf : Function.support f ⊆ K) :
    tsupport (push C f) ⊆ C '' K :=
  closure_minimal (support_push_subset C f K hf)
    (hK.image_of_continuousOn (C.continuousOn.mono hKC)).isClosed

end TamingCompatibility.GeometricHilbert.KernelExtension

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelExtension
open Set Filter
open scoped Topology ContDiff
variable {P E F W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] Classical.propDecidable

lemma push_family_contDiffAt (C : OpenPartialHomeomorph E F) (f : P → E → W) (K : Set E)
    (hK : IsCompact K) (hKC : K ⊆ C.source) (hfK : ∀ p, Function.support (f p) ⊆ K)
    {p : P} (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ (fun v : P × E => f v.1 v.2) (p,x))
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ (C.symm : F → E) (C x)) (y : F) :
    ContDiffAt ℝ ∞ (fun v : P × F => push C (f v.1) v.2) (p,y) := by
  by_cases hy : y ∈ C '' K
  · obtain ⟨x,hx,rfl⟩ := hy
    have ht := C.map_source (hKC hx)
    have he : (fun v : P × F => push C (f v.1) v.2) =ᶠ[𝓝 (p,C x)]
        (fun v : P × F => f v.1 (C.symm v.2)) := by
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (C.open_target.mem_nhds ht)] with v hv
      have hv' : v.2 ∈ C.target := hv
      simp [push,hv']
    apply ContDiffAt.congr_of_eventuallyEq _ he
    have hfx : ContDiffAt ℝ ∞ (fun v : P × E => f v.1 v.2) (p,C.symm (C x)) := by
      simpa [C.left_inv (hKC hx)] using hf x hx
    exact hfx.comp (p,C x) (contDiffAt_fst.prodMk ((hC x hx).comp (p,C x) contDiffAt_snd))
  · have hc : _root_.IsClosed (C '' K) := (hK.image_of_continuousOn (C.continuousOn.mono hKC)).isClosed
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hc.isOpen_compl.mem_nhds hy)] with v hv
    apply Function.notMem_support.mp
    exact fun h => hv (support_push_subset C (f v.1) K (hfK v.1) h)

end TamingCompatibility.GeometricHilbert.KernelExtension

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixGaussian
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
lemma heat_compare {t a : ℝ} (ht : 0 < t) (ha : 0 < a) {z w : V}
    (hw : ‖w‖ ≤ a*‖z‖) : heat t z ≤ a^4*heat (a^2*t) w := by
  have hs : ‖w‖^2 ≤ a^2*‖z‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg w) hw 2
  have he : -‖z‖^2/(4*t) ≤ -‖w‖^2/(4*(a^2*t)) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*(a^2*t))).mpr
    have heq : (-‖z‖^2/(4*t))*(4*(a^2*t)) = -(a^2*‖z‖^2) := by field_simp
    rw [heq]
    linarith
  have hp : a^4*(4*Real.pi*(a^2*t))⁻¹^2 = (4*Real.pi*t)⁻¹^2 := by
    field_simp
  unfold heat
  rw [←mul_assoc,hp]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (sq_nonneg _)
end TamingCompatibility.GeometricHilbert.FlatHeat

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set _root_.MeasureTheory
open HodgeNormalSymbol FirstJetGauge OrthogonalJets UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixGaussianMetricNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.hodgeParametrixGaussianMetricNormedSpace
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)

include hg hB

lemma normalMap_compact_bound (K : Set Space) (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ r →
      ‖normalMap g B q z - q‖ ≤ C*‖z‖ := by
  obtain ⟨C,hC,hb⟩ := linear_bound_on_tube (fun x : Space × Space => normalMap g B x.1 x.2)
    K hK hr (fun _ _ => (normalMap_joint g B hg hB).contDiffAt)
  refine ⟨C+1,by linarith,fun q hq z hz => ?_⟩
  have hh : ‖normalMap g B q z - q‖ ≤ C*‖z‖ := by
    simpa only [normalMap_zero] using hb q hq z hz
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z))

attribute [local irreducible] normalGauge normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeResidualFamily
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus FlatHeat Filter Set
open scoped Topology ContDiff RealInnerProductSpace
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma residual_family_smooth (a : P × V → Principal) (b : P × V → First (W := W))
    (c : P × V → W →L[ℝ] W) {x : P × V} {t : ℝ} (ht : t ≠ 0)
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x) (hc : ContDiffAt ℝ ∞ c x) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (P × V) =>
      residual (fun z => a (v.2.1,z)) (fun z => b (v.2.1,z))
        (fun z => c (v.2.1,z)) v.1 v.2.2) (t,x) := by
  have hh : ContDiffAt ℝ ∞ (fun v : ℝ × (P × V) => heat v.1 v.2.2) (t,x) :=
    (heat_joint_contDiffAt (x := (t,x.2)) ht).comp (t,x) (contDiffAt_fst.prodMk contDiffAt_snd.snd)
  have hi (u : V) : ContDiffAt ℝ ∞ (fun v : ℝ × (P × V) => ⟪v.2.2,u⟫) (t,x) :=
    contDiffAt_snd.snd.inner ℝ contDiffAt_const
  have hd : ContDiffAt ℝ ∞ (fun v : ℝ × (P × V) => (2*v.1)⁻¹) (t,x) :=
    (contDiffAt_const.mul contDiffAt_fst).inv (mul_ne_zero (by norm_num) ht)
  have hd2 : ContDiffAt ℝ ∞ (fun v : ℝ × (P × V) => (4*v.1^2)⁻¹) (t,x) :=
    (contDiffAt_const.mul (contDiffAt_fst.pow 2)).inv (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht))
  unfold residual
  simp_rw [heat_hessian,heat_fderiv,div_eq_mul_inv]
  apply ContDiffAt.add
  · apply ContDiffAt.add
    · apply ContDiffAt.sum
      intro i _
      apply ContDiffAt.sum
      intro j _
      have hk : ContDiffAt ℝ ∞ (fun v : ℝ × (P × V) =>
          (euclideanPrincipal i j - a v.2 i j) * (heat v.1 v.2.2 *
            (⟪v.2.2,EuclideanSpace.basisFun (Fin 4) ℝ i⟫ *
              ⟪v.2.2,EuclideanSpace.basisFun (Fin 4) ℝ j⟫ * (4*v.1^2)⁻¹ -
                ⟪EuclideanSpace.basisFun (Fin 4) ℝ i,EuclideanSpace.basisFun (Fin 4) ℝ j⟫ *
                  (2*v.1)⁻¹))) (t,x) :=
        (contDiffAt_const.sub ((contDiffAt_pi.mp (contDiffAt_pi.mp ha i) j).comp (t,x) contDiffAt_snd)).mul
          (hh.mul ((((hi (EuclideanSpace.basisFun (Fin 4) ℝ i)).mul
            (hi (EuclideanSpace.basisFun (Fin 4) ℝ j))).mul hd2).sub (contDiffAt_const.mul hd)))
      exact hk.smul (contDiffAt_const (c := ContinuousLinearMap.id ℝ W))
    · apply ContDiffAt.sum
      intro i _
      exact ((hh.neg.mul hd).mul (hi (EuclideanSpace.basisFun (Fin 4) ℝ i))).smul ((contDiffAt_pi.mp hb i).comp (t,x) contDiffAt_snd)
  · exact hh.smul (hc.comp (t,x) contDiffAt_snd)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in

lemma cutoff_residual_eq_zero (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (χ : V → ℝ) {z : V} (hz : z ∉ tsupport χ) (q : P) (t : ℝ) :
    residual (fun y => CutoffFamilies.principal a χ (q,y))
      (fun y => CutoffFamilies.first a b χ (q,y))
      (fun y => CutoffFamilies.zero a b c χ (q,y)) t z = 0 := by
  have he : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hz
  have hd : fderiv ℝ χ z = 0 := by simpa using he.fderiv_eq (𝕜 := ℝ)
  have hdd (v : V) : fderiv ℝ (fun y => fderiv ℝ χ y v) z = 0 := by
    have he' : (fun y => fderiv ℝ χ y v) =ᶠ[𝓝 z] 0 := by
      filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
      simpa using congrArg (fun C : V →L[ℝ] ℝ => C v) hy
    simpa using he'.fderiv_eq (𝕜 := ℝ)
  simp [residual,CutoffFamilies.principal,CutoffFamilies.first,CutoffFamilies.zero,
    cutoffPrincipal,cutoffFirst,cutoffZero,he.eq_of_nhds,hd,hdd]

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalGauge normalPrincipal gaugedFirst gaugedZero

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualFamilyMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualFamilyMetricTensorNormedSpace
lemma residualCoordinate_support (ψ χ : Space → ℝ) (t : ℝ) :
    Function.support (residualCoordinate J α ht p D g B ψ χ t) ⊆
      Function.support ψ ×ˢ tsupport χ := by
  classical
  intro x hx
  constructor
  · intro h
    apply hx
    simp only [residualCoordinate,h,zero_smul]
  · by_contra hz
    apply hx
    rw [residualCoordinate,NormalHeatResidual.cutoff_residual_eq_zero _ _ _ χ hz]
    simp

lemma residualCoordinate_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (ψ χ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    {t : ℝ} (htpos : 0 < t) {x : Space × Space} (hx : x ∈ gaugedDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) =>
      residualCoordinate J α ht p D g B ψ χ v.1 v.2) (t,x) := by
  have ha := fun i j => normalPrincipal_smooth g B hg hB hx.1.2 i j
  have hb := fun j => gaugedFirst_smooth J α ht p D g B hs hg hB hx j
  have hc := gaugedZero_smooth J α ht p D g B hs hg hB hx
  exact (hψ.contDiffAt.comp (t,x) contDiffAt_snd.fst).smul
    (((normalGauge_smooth J α ht p D g B hs hg hB hx.2).comp (t,x) contDiffAt_snd).clm_comp
      (NormalHeatResidual.residual_family_smooth _ _ _ (ne_of_gt htpos)
        (CutoffFamilies.principal_smooth _ χ hχ ha)
        (CutoffFamilies.first_smooth _ _ χ hχ ha hb)
        (CutoffFamilies.zero_smooth _ _ _ χ hχ ha hb hc)))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeResidualPush
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualPushMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualPushMetricTensorNormedSpace
lemma residualPatch_joint_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (K : Set (Space × Space)) (hK : IsCompact K)
    (hFK : Function.support ψ ×ˢ tsupport χ ⊆ K)
    (O : Set Space) (hKO : K ⊆ parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O)
    {t : ℝ} (htpos : 0 < t) (y : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) =>
      residualPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ v.1 v.2) (t,y) := by
  apply KernelExtension.push_family_contDiffAt _ _ K hK (fun x hx => (hKO hx).1.1.1)
    (fun s => (residualCoordinate_support J α ht p D g B ψ χ s).trans hFK)
  · intro x hx
    exact residualCoordinate_smooth J α ht p D g B hs hg hB ψ χ hψ hχ htpos (hKO hx).1.2
  · intro x hx
    have hi := (hKO hx).1.1.2
    exact (inverseRegularDomain_smooth _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq) _ hi).contDiffAt
      ((inverseRegularDomain_open _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq)).mem_nhds hi)

lemma residualPatch_gaussian (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (hψ : ∀ q, 0 ≤ ψ q ∧ ψ q ≤ 1)
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : Space)] 1)
    (K : Set Space) (hK : IsCompact K) (hψK : Function.support ψ ⊆ K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B)
    {r : ℝ} (hr : 0 ≤ r) (hχr : tsupport χ ⊆ Metric.closedBall (0 : Space) r)
    (hsub : K ×ˢ Metric.closedBall (0 : Space) r ⊆ gaugedDomain J α ht p D g B) :
    ∃ A L : ℝ, 0 ≤ A ∧ 0 < L ∧ ∀ t : ℝ, 0 < t → ∀ q y : Space,
      ‖residualPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (q,y)‖ ≤
        A*FlatHeat.heat (L*t) (y-q) := by
  classical
  obtain ⟨A,hA,hb⟩ := residualCoordinate_gaussian J α ht p D g B hs hg hB ψ χ hψ hχ hχ0
    K hK hψK hactual hr hχr hsub
  obtain ⟨L,hL,hmap⟩ := normalMap_compact_bound g B hg hB K hK hr
  refine ⟨A*L^4,2*L^2,mul_nonneg hA (by positivity),by positivity,fun t htpos q y => ?_⟩
  let N := geometricNormalChart g B hg hB q₀ Bq hBq
  have hright : 0 ≤ (A*L^4)*FlatHeat.heat (2*L^2*t) (y-q) :=
    mul_nonneg (mul_nonneg hA (by positivity)) (FlatHeat.heat_nonneg _ _)
  by_cases hy : (q,y) ∈ N.target
  · let x := N.symm (q,y)
    have hfst : x.1 = q := geometricNormalChart_symm_fst g B hg hB q₀ Bq hBq hy
    have hsnd : normalMap g B q x.2 = y := geometricNormalChart_symm_right g B hg hB q₀ Bq hBq hy
    have he : residualPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (q,y) =
        residualCoordinate J α ht p D g B ψ χ t (q,x.2) := by
      change (if (q,y) ∈ N.target then residualCoordinate J α ht p D g B ψ χ t x else 0) = _
      rw [ite_eq_left hy]
      rw [show x = (q,x.2) from Prod.ext hfst rfl]
    rw [he]
    by_cases hz : residualCoordinate J α ht p D g B ψ χ t (q,x.2) = 0
    · simpa only [hz,norm_zero] using hright
    have hsupp := residualCoordinate_support J α ht p D g B ψ χ t hz
    have hzr : ‖x.2‖ ≤ r := by simpa using hχr hsupp.2
    have hheat := FlatHeat.heat_compare (mul_pos (by norm_num : (0:ℝ)<2) htpos) hL
      (show ‖y-q‖ ≤ L*‖x.2‖ by rw [← hsnd]; exact hmap q (hψK hsupp.1) x.2 hzr)
    calc
      _ ≤ A*FlatHeat.heat (2*t) x.2 := hb t htpos q x.2
      _ ≤ A*(L^4*FlatHeat.heat (L^2*(2*t)) (y-q)) := mul_le_mul_of_nonneg_left hheat hA
      _ = _ := by rw [show L^2*(2*t) = 2*L^2*t by ring]; ring
  · have he : residualPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (q,y) = 0 := ite_eq_right hy
    simpa only [he,norm_zero] using hright

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixPartition
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldLocalization
open Set ManifoldForms
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X)
attribute [local instance] Classical.propDecidable

omit [T2Space X] [CompactSpace X] in
lemma coordinatePartition_bounds (p : A.centers) (q : Space) :
    0 ≤ coordinatePartition A p q ∧ coordinatePartition A p q ≤ 1 := by
  by_cases hq : q ∈ (extChartAt Model p.val).target
  · simp only [coordinatePartition,Set.indicator_of_mem hq]
    exact ⟨A.partition.nonneg _ _,A.partition.le_one _ _⟩
  · simp only [coordinatePartition,Set.indicator_of_notMem hq,le_refl,zero_le_one,and_self]

end TamingCompatibility.ManifoldLocalization

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixWeakEquation
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedSpace
lemma actual {q : Space} (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius) :
    ActualData J α ht p D.chart q D.metricExtension D.frameExtension :=
  ⟨D.actualDomain,D.actual_open,D.centers_actual hq,D.actual_subset,
    D.metric_actual,D.frame_actual,D.metric_symmetric⟩

end ParametrixData

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAtlasPatches
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_rb6c063_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_rb6c063_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma normalCutoff_tsupport : tsupport (D.normalCutoff : Space → ℝ) ⊆ Metric.closedBall (0 : Space) D.radius := by
  rw [D.normalCutoff.tsupport_eq]
  apply Metric.closedBall_subset_closedBall
  change D.radius/2 ≤ D.radius
  linarith [D.radius_pos]

end ParametrixData

variable [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_rb6c063_2 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_rb6c063_2 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
include hD in
lemma coordinatePartition_centerSupport (p : A.centers) :
    tsupport (coordinatePartition A p) ⊆ Metric.closedBall (extChartAt Model p.val p.val) (D p).radius := by
  intro q hq
  obtain ⟨x,hx,rfl⟩ := coordinatePartition_tsupport A p hq
  exact Metric.closedBall_subset_closedBall (by linarith [(D p).radius_pos])
    ((D p).source_image_subset ⟨x,hD p hx,rfl⟩)

include hD in
lemma partition_patch_support (p : A.centers) :
    Function.support (coordinatePartition A p) ×ˢ tsupport ((D p).normalCutoff : Space → ℝ) ⊆
      (D p).normalCompact :=
  Set.prod_mono ((subset_tsupport _).trans (coordinatePartition_centerSupport J α ht A D hD p))
    (D p).normalCutoff_tsupport

include hD in
lemma partitionResidual_smooth (hs : IsSmooth α) (p : A.centers) {t : ℝ} (htp : 0 < t) (y : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => partitionResidual J α ht A D p v.1 v.2) (t,y) :=
  residualPatch_joint_smooth J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension hs
    (D p).metric_smooth (D p).frame_smooth (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff
    (coordinatePartition_smooth_compact A p).1 (D p).normalCutoff.contDiff
    (D p).normalCompact (D p).normalCompact_compact (partition_patch_support J α ht A D hD p)
    (D p).actualDomain (D p).tube htp y

include hD in
lemma partitionResidual_tsupport (p : A.centers) (t : ℝ) :
    tsupport (partitionResidual J α ht A D p t) ⊆ (D p).physicalCompact := by
  apply KernelExtension.tsupport_push_subset _ _ _ (D p).normalCompact_compact (D p).normalCompact_source
  exact (residualCoordinate_support J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    _ _ t).trans (partition_patch_support J α ht A D hD p)

include hD in
lemma partitionResidual_gaussian (hs : IsSmooth α) (p : A.centers) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 < L ∧ ∀ t : ℝ, 0 < t → ∀ q y : Space,
      ‖partitionResidual J α ht A D p t (q,y)‖ ≤ M*FlatHeat.heat (L*t) (y-q) :=
  residualPatch_gaussian J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension hs
    (D p).metric_smooth (D p).frame_smooth (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff
    (coordinatePartition_bounds A p) (D p).normalCutoff.contDiff (D p).normalCutoff.eventuallyEq_one
    (Metric.closedBall (extChartAt Model p.val p.val) (D p).radius) (isCompact_closedBall _ _)
    ((subset_tsupport _).trans (coordinatePartition_centerSupport J α ht A D hD p))
    (fun _ hq => (D p).actual hq) (D p).radius_pos.le (D p).normalCutoff_tsupport
    (fun _ hx => ((D p).tube hx).1.2)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCoordinateRetraction
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma coordinateEncode_smooth (hs : IsSmooth α) (p : A.centers) :
    ContDiffOn ℝ ∞ (coordinateEncode J α ht A D p) (D p).chart.domain := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_pi.mpr
  intro i
  exact (HodgeChart.rawVector_smooth J α ht p.val (D p).chart
    (globalFrame_smooth J α ht A D hD hs i.1 i.2)).inner ℝ contDiffOn_const

include hD in
lemma coordinateDecode_smooth (hs : IsSmooth α) (p : A.centers) :
    ContDiffOn ℝ ∞ (coordinateDecode J α ht A D p) (D p).chart.domain := by
  have hmass := (((squareMass_inv_smooth A).comp_contMDiffOn
      (contMDiffOn_extChartAt_symm p.val)).contDiffOn).mono (D p).chart.domain_subset
  have hsum : ContDiffOn ℝ ∞ (fun q => ∑ i : A.centers × Fin 6,
      (ContinuousLinearMap.proj i : FrameSpace A →L[ℝ] ℝ).smulRight
        (HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q))
      (D p).chart.domain := by
    apply ContDiffOn.sum
    intro i _
    exact contDiffOn_const.smulRight (HodgeChart.rawVector_smooth J α ht p.val (D p).chart
      (globalFrame_smooth J α ht A D hD hs i.1 i.2))
  exact hmass.smul hsum

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeVolterraKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraBounds
open _root_.MeasureTheory Set Metric
open scoped Topology
variable {X B : Type*} [PseudoMetricSpace X]

lemma weight_one_le (N : ℕ) {t : ℝ} (ht : 0 < t) (x y : X) :
    1 ≤ weight N t x y := by
  apply one_le_pow₀
  have := div_nonneg (dist_nonneg (x := x) (y := y)) (Real.sqrt_pos.2 ht).le
  linarith

lemma weight_pos (N : ℕ) {t : ℝ} (ht : 0 < t) (x y : X) :
    0 < weight N t x y := lt_of_lt_of_le zero_lt_one (weight_one_le N ht x y)

lemma weight_symm (N : ℕ) (t : ℝ) (x y : X) : weight N t x y = weight N t y x := by
  simp only [weight, dist_comm]

lemma weight_continuous (N : ℕ) (t : ℝ) (x : X) : Continuous (weight N t x) := by
  unfold weight
  fun_prop

end TamingCompatibility.GeometricHilbert.VolterraBounds

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGaussianSchur
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open _root_.MeasureTheory Set

lemma polynomial_bound (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1+x)^n ≤ 2^n*(1+x^(2*n)) := by
  by_cases h : x ≤ 1
  · calc
      _ ≤ (2 : ℝ)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (pow_nonneg hx _))
  · have h1 : 1 ≤ x := (lt_of_not_ge h).le
    calc
      _ ≤ (2*x)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2^n*x^n := mul_pow _ _ _
      _ ≤ 2^n*x^(2*n) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)

lemma weighted_heat_bound (n : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (z : V) :
    (1+‖z‖/Real.sqrt t)^n * heat (a*t) z ≤
      (2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))*heat (2*a*t) z := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h0 := gaussian_weight_absorption (mul_pos ha ht) z 0
  norm_num only [Nat.mul_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,one_mul] at h0
  have hn := gaussian_weight_absorption (mul_pos ha ht) z n
  have he : (‖z‖/Real.sqrt t)^(2*n) = ‖z‖^(2*n)/t^n := by
    rw [div_pow,pow_mul (Real.sqrt t),Real.sq_sqrt ht.le]
  have hh : (‖z‖/Real.sqrt t)^(2*n)*heat (a*t) z ≤
      (4*(8*a)^n*(n.factorial : ℝ))*heat (2*a*t) z := by
    rw [he,div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos ht n)).mpr
    convert hn using 1 <;> first | rfl | (simp only [mul_assoc,mul_pow]; ring)
  calc
    _ ≤ (2^n*(1+(‖z‖/Real.sqrt t)^(2*n)))*heat (a*t) z :=
      mul_le_mul_of_nonneg_right (polynomial_bound n (div_nonneg (norm_nonneg z) hs.le)) (heat_nonneg _ _)
    _ = 2^n*(heat (a*t) z+(‖z‖/Real.sqrt t)^(2*n)*heat (a*t) z) := by ring
    _ ≤ 2^n*(4*heat (2*a*t) z+(4*(8*a)^n*(n.factorial : ℝ))*heat (2*a*t) z) := by
      apply mul_le_mul_of_nonneg_left (add_le_add _ hh) (by positivity)
      simpa only [mul_assoc] using h0
    _ = _ := by ring

end TamingCompatibility.GeometricHilbert.FlatHeat

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma coordinateMatrix_support (p : A.centers) (K : Space × Space → W →L[ℝ] W) :
    Function.support (coordinateMatrix J α ht A D p K) ⊆ Function.support K := by
  intro z hz hK
  apply hz
  simp only [coordinateMatrix,hK,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]

include hD in
lemma coordinateMatrix_joint_smooth (hs : IsSmooth α) (p : A.centers)
    (K : ℝ → Space × Space → W →L[ℝ] W)
    (hKs : ∀ t, Function.support (K t) ⊆ (D p).physicalCompact)
    {t : ℝ} {z : Space × Space}
    (hK : ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => K v.1 v.2) (t,z)) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => coordinateMatrix J α ht A D p (K v.1) v.2) (t,z) := by
  by_cases hz : z ∈ (D p).physicalCompact
  · have hd := (D p).physicalCompact_domain hz
    have he := ((coordinateEncode_smooth J α ht A D hD hs p) _ hd.2).contDiffAt
      ((D p).chart.domain_open.mem_nhds hd.2)
    have hd' := ((coordinateDecode_smooth J α ht A D hD hs p) _ hd.1).contDiffAt
      ((D p).chart.domain_open.mem_nhds hd.1)
    exact ((he.comp (t,z) contDiffAt_snd.snd).clm_comp hK).clm_comp
      (hd'.comp (t,z) contDiffAt_snd.fst)
  · apply contDiffAt_const.congr_of_eventuallyEq
    have hn : {v : ℝ × (Space × Space) | v.2 ∉ (D p).physicalCompact} ∈ 𝓝 (t,z) :=
      (continuous_snd : Continuous (Prod.snd : ℝ × (Space × Space) → Space × Space)).continuousAt (x := (t,z)) |>.preimage_mem_nhds
        ((D p).physicalCompact_compact.isClosed.isOpen_compl.mem_nhds hz)
    filter_upwards [hn] with v hv
    apply Function.notMem_support.mp
    exact fun h => hv (hKs v.1 (coordinateMatrix_support J α ht A D p (K v.1) h))

include hD in
lemma coordinateMatrix_uniform_bound (hs : IsSmooth α) (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : Space × Space → W →L[ℝ] W,
      Function.support K ⊆ (D p).physicalCompact → ∀ z,
      ‖coordinateMatrix J α ht A D p K z‖ ≤ C*‖K z‖ := by
  have he : ContinuousOn (fun z : Space × Space => coordinateEncode J α ht A D p z.2)
      (D p).physicalCompact :=
    (coordinateEncode_smooth J α ht A D hD hs p).continuousOn.comp continuousOn_snd
      (fun z hz => ((D p).physicalCompact_domain hz).2)
  have hd' : ContinuousOn (fun z : Space × Space => coordinateDecode J α ht A D p z.1)
      (D p).physicalCompact :=
    (coordinateDecode_smooth J α ht A D hD hs p).continuousOn.comp continuousOn_fst
      (fun z hz => ((D p).physicalCompact_domain hz).1)
  obtain ⟨Ce,hCe⟩ := (D p).physicalCompact_compact.exists_bound_of_continuousOn he
  obtain ⟨Cd,hCd⟩ := (D p).physicalCompact_compact.exists_bound_of_continuousOn hd'
  refine ⟨max Ce 0*max Cd 0,mul_nonneg (le_max_right _ _) (le_max_right _ _),fun K hK z => ?_⟩
  by_cases hz : z ∈ (D p).physicalCompact
  · have hbE : ‖coordinateEncode J α ht A D p z.2‖ ≤ max Ce 0 := (hCe z hz).trans (le_max_left _ _)
    have hbD : ‖coordinateDecode J α ht A D p z.1‖ ≤ max Cd 0 := (hCd z hz).trans (le_max_left _ _)
    calc
      _ ≤ (‖coordinateEncode J α ht A D p z.2‖*‖K z‖)*‖coordinateDecode J α ht A D p z.1‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ (max Ce 0*‖K z‖)*max Cd 0 := mul_le_mul
        (mul_le_mul_of_nonneg_right hbE (norm_nonneg _)) hbD (norm_nonneg _)
        (mul_nonneg (le_max_right _ _) (norm_nonneg _))
      _ = _ := by ring
  · have hzero : K z = 0 := Function.notMem_support.mp (fun h => hz (hK h))
    simp only [coordinateMatrix,hzero,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp,norm_zero,mul_zero,le_refl]

include hD in
lemma residualMatrix_smooth (hs : IsSmooth α) (p : A.centers) {t : ℝ} (htp : 0 < t) (z : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => residualMatrix J α ht A D p v.1 v.2) (t,z) :=
  coordinateMatrix_joint_smooth J α ht A D hD hs p _
    (fun t => (subset_tsupport _).trans (partitionResidual_tsupport J α ht A D hD p t))
    (partitionResidual_smooth J α ht A D hD hs p htp z)

include hD in
lemma residualFrameMatrix_gaussian (hs : IsSmooth α) (p : A.centers) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 < L ∧ ∀ t : ℝ, 0 < t → ∀ q y : Space,
      ‖residualMatrix J α ht A D p t (q,y)‖ ≤ M*FlatHeat.heat (L*t) (y-q) := by
  obtain ⟨M,L,hM,hL,hb⟩ := partitionResidual_gaussian J α ht A D hD hs p
  obtain ⟨C,hC,hc⟩ := coordinateMatrix_uniform_bound J α ht A D hD hs p
  refine ⟨C*M,L,mul_nonneg hC hM,hL,fun t htpos q y => ?_⟩
  refine (hc _ ((subset_tsupport _).trans (partitionResidual_tsupport J α ht A D hD p t)) (q,y)).trans ?_
  exact (mul_le_mul_of_nonneg_left (hb t htpos q y) hC).trans_eq (by ring)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeManifoldKernelExtension
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldKernelExtension
open Set Filter
open scoped Manifold Topology
variable {E X G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X]
  [NormedAddCommGroup G]
attribute [local instance] Classical.propDecidable
local notation "I" => 𝓘(ℝ,E)

lemma liftSet_source (p : X) (K : Set (E × E))
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target) :
    liftSet p K ⊆ (extChartAt I p).source ×ˢ (extChartAt I p).source := by
  rintro x ⟨z,hz,rfl⟩
  exact ⟨(extChartAt I p).map_target (hK hz).1,(extChartAt I p).map_target (hK hz).2⟩

lemma liftSet_compact (p : X) (K : Set (E × E)) (hc : IsCompact K)
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target) :
    IsCompact (liftSet p K) := by
  apply hc.image_of_continuousOn
  exact ((continuousOn_extChartAt_symm p).comp continuousOn_fst (fun z hz => (hK hz).1)).prodMk
    ((continuousOn_extChartAt_symm p).comp continuousOn_snd (fun z hz => (hK hz).2))

lemma support_push (p : X) (f : E × E → G) (K : Set (E × E))
    (hf : Function.support f ⊆ K) : Function.support (push p f) ⊆ liftSet p K := by
  intro x hx
  have hs : x ∈ (extChartAt I p).source ×ˢ (extChartAt I p).source := by
    by_contra hh
    exact hx (by simp only [push,ite_eq_right hh])
  refine ⟨(extChartAt I p x.1,extChartAt I p x.2), hf ?_,?_⟩
  · simpa only [Function.mem_support,push,ite_eq_left hs] using hx
  · simp only [(extChartAt I p).left_inv hs.1,(extChartAt I p).left_inv hs.2]

variable [T2Space X]

lemma push_joint_continuousAt {P : Type*} [TopologicalSpace P]
    (p : X) (f : P → E × E → G) (K : Set (E × E)) (hc : IsCompact K)
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target)
    (hf : ∀ t, Function.support (f t) ⊆ K) (t : P)
    (hcont : ∀ z, ContinuousAt (fun v : P × (E × E) => f v.1 v.2) (t,z)) (x : X × X) :
    ContinuousAt (fun v : P × (X × X) => push p (f v.1) v.2) (t,x) := by
  by_cases hx : x ∈ liftSet p K
  · have hsrc := liftSet_source p K hK hx
    have hco : ContinuousAt (fun y : X × X => (extChartAt I p y.1,extChartAt I p y.2)) x :=
      ((continuousAt_extChartAt' hsrc.1).comp continuousAt_fst).prodMk
        ((continuousAt_extChartAt' hsrc.2).comp continuousAt_snd)
    have he : (fun v : P × (X × X) => push p (f v.1) v.2) =ᶠ[𝓝 (t,x)]
        fun v => f v.1 (extChartAt I p v.2.1,extChartAt I p v.2.2) := by
      have hn : {v : P × (X × X) | v.2 ∈ (extChartAt I p).source ×ˢ (extChartAt I p).source} ∈ 𝓝 (t,x) :=
        (show ContinuousAt (Prod.snd : P × (X × X) → X × X) (t,x) from continuousAt_snd).preimage_mem_nhds
          (((show IsOpen ((extChartAt I p).source) from isOpen_extChartAt_source p).prod
            (show IsOpen ((extChartAt I p).source) from isOpen_extChartAt_source p)).mem_nhds hsrc)
      filter_upwards [hn] with v hv
      simp only [push,ite_eq_left hv]
    have hprod : ContinuousAt (fun v : P × (X × X) =>
        (v.1,(extChartAt I p v.2.1,extChartAt I p v.2.2))) (t,x) := by
      exact continuousAt_fst.prodMk (ContinuousAt.comp
        (g := fun y : X × X => (extChartAt I p y.1,extChartAt I p y.2))
        (f := Prod.snd) hco continuousAt_snd)
    have hc' : ContinuousAt (fun v : P × (X × X) => f v.1 (extChartAt I p v.2.1,extChartAt I p v.2.2)) (t,x) := by
      exact ContinuousAt.comp (g := fun v : P × (E × E) => f v.1 v.2)
        (f := fun v : P × (X × X) => (v.1,(extChartAt I p v.2.1,extChartAt I p v.2.2)))
        (hcont (extChartAt I p x.1,extChartAt I p x.2)) hprod
    exact hc'.congr_of_eventuallyEq he
  · apply continuousAt_const.congr_of_eventuallyEq
    have hn := (continuous_snd : Continuous (Prod.snd : P × (X × X) → X × X)).continuousAt (x := (t,x)) |>.preimage_mem_nhds
      ((liftSet_compact p K hc hK).isClosed.isOpen_compl.mem_nhds hx)
    filter_upwards [hn] with v hv
    exact Function.notMem_support.mp (fun h => hv (support_push p (f v.1) K (hf v.1) h))

end TamingCompatibility.ManifoldKernelExtension

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalParametrix
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] Classical.propDecidable

omit [T2Space X] [CompactSpace X] in
lemma physicalCompact_target (p : A.centers) :
    (D p).physicalCompact ⊆ (extChartAt Model p.val).target ×ˢ (extChartAt Model p.val).target :=
  fun _ hz => ⟨(D p).chart.domain_subset ((D p).physicalCompact_domain hz).1,
    (D p).chart.domain_subset ((D p).physicalCompact_domain hz).2⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeManifoldPairingInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)

include hs ht in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X] in
lemma chart_density_compact_bound (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ L, chartDensity J α p z ≤ C := by
  obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn ((chartDensity_smooth J α hs ht p).continuousOn.mono hLt)
  exact ⟨max C 0,le_max_right _ _,fun z hz => (le_abs_self _).trans ((hC z hz).trans (le_max_left _ _))⟩

include hs ht in

lemma integral_chart_bound (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (D : ℝ) (hD : 0 ≤ D)
    (hDb : ∀ z ∈ L, chartDensity J α p z ≤ D)
    (f : X → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfs : Function.support f ⊆ (extChartAt Model p).symm '' L)
    (G : Space → ℝ) (hGi : Integrable G) (hG0 : ∀ z, 0 ≤ G z)
    (hGf : ∀ z ∈ (extChartAt Model p).target, f ((extChartAt Model p).symm z) ≤ G z) :
    (∫ x, f x ∂geometricVolume A J α) ≤ D*(∫ z, G z) := by
  have hLc : IsCompact ((extChartAt Model p).symm '' L) :=
    hL.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hLt)
  have hts : tsupport f ⊆ (extChartAt Model p).symm '' L := closure_minimal hfs hLc.isClosed
  have hts' : tsupport f ⊆ (extChartAt Model p).source := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hts hx
    exact (extChartAt Model p).map_target (hLt hz)
  have hcgi := coordinateIntegrand_integrable J α hs ht p f hf hts'
  have hpoint (z : Space) : coordinateIntegrand J α p f z ≤ D*G z := by
    by_cases hzt : z ∈ (extChartAt Model p).target
    · rw [coordinateIntegrand,Set.indicator_of_mem hzt]
      by_cases hz : z ∈ L
      · exact mul_le_mul (hDb z hz) (hGf z hzt) (hf0 _) hD
      · have hfz : f ((extChartAt Model p).symm z) = 0 := by
          apply Function.notMem_support.mp
          intro hh
          obtain ⟨w,hw,he⟩ := hfs hh
          have he' := congrArg (extChartAt Model p) he
          rw [(extChartAt Model p).right_inv (hLt hw),(extChartAt Model p).right_inv hzt] at he'
          exact hz (he' ▸ hw)
        rw [hfz,mul_zero]
        exact mul_nonneg hD (hG0 z)
    · rw [coordinateIntegrand,Set.indicator_of_notMem hzt]
      exact mul_nonneg hD (hG0 z)
  rw [integral_geometricVolume_coordinate A J α hs ht p f hf hts',
    ← integral_indicator (isOpen_extChartAt_target p).measurableSet]
  change (∫ z, coordinateIntegrand J α p f z) ≤ _
  calc
    _ ≤ ∫ z, D*G z := integral_mono hcgi (hGi.const_mul D) hpoint
    _ = _ := integral_const_mul _ _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelChartGaussian
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization ManifoldKernelExtension Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology NNReal

lemma weight_of_dist_bound {Y : Type*} [PseudoMetricSpace Y] (n : ℕ)
    {t C r : ℝ} (ht : 0 < t) (hC : 1 ≤ C) (_hr : 0 ≤ r) (x y : Y)
    (hb : dist x y ≤ C*r) :
    VolterraBounds.weight n t x y ≤ C ^ n*(1+r/Real.sqrt t)^n := by
  unfold VolterraBounds.weight
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hh := div_le_div_of_nonneg_right hb (Real.sqrt_nonneg t)
  rw [mul_div_assoc] at hh
  nlinarith

variable {X B : Type*} [MetricSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [NormedAddCommGroup B]

omit [IsManifold Model ∞ X] in

lemma push_weighted_gaussian (p : X) (L : Set Space)
    (C : ℝ≥0)
    (hLip : LipschitzOnWith C (extChartAt Model p).symm L)
    (K : Space × Space → B) (hsupp : Function.support K ⊆ L ×ˢ L)
    (n : ℕ) {a t M : ℝ} (ha : 0 < a) (ht : 0 < t) (hM : 0 ≤ M)
    (hK : ∀ q y, ‖K (q,y)‖ ≤ M*FlatHeat.heat (a*t) (y-q)) (x y : X) :
    VolterraBounds.weight n t x y * ‖push p K (x,y)‖ ≤
      (max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))*
        FlatHeat.heat (2*a*t) (extChartAt Model p y-extChartAt Model p x) := by
  let e := extChartAt Model p
  have hfactor : 0 ≤ (max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ))) := by positivity
  by_cases hxy : (x,y) ∈ e.source ×ˢ e.source
  · rw [push,ite_eq_left hxy]
    by_cases hz : (e x,e y) ∈ Function.support K
    · have hs := hsupp hz
      have hd : dist x y ≤ (max (C:ℝ) 1)*‖e y-e x‖ := by
        have hb := hLip.dist_le_mul (e x) hs.1 (e y) hs.2
        rw [e.left_inv hxy.1,e.left_inv hxy.2] at hb
        exact hb.trans (by rw [dist_comm,dist_eq_norm]; gcongr; exact le_max_left _ _)
      have hw := weight_of_dist_bound n ht (le_max_right (C:ℝ) 1) (norm_nonneg (e y-e x)) x y hd
      calc
        _ ≤ ((max (C:ℝ) 1)^n*(1+‖e y-e x‖/Real.sqrt t)^n)*(M*FlatHeat.heat (a*t) (e y-e x)) :=
          mul_le_mul hw (hK (e x) (e y)) (norm_nonneg _) (by positivity)
        _ = ((max (C:ℝ) 1)^n*M)*((1+‖e y-e x‖/Real.sqrt t)^n*FlatHeat.heat (a*t) (e y-e x)) := by ring
        _ ≤ _ := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (FlatHeat.weighted_heat_bound n ha ht (e y-e x)) (show 0 ≤ (max (C:ℝ) 1)^n*M by positivity)
    · rw [Function.notMem_support.mp hz,norm_zero,mul_zero]
      exact mul_nonneg hfactor (FlatHeat.heat_nonneg _ _)
  · rw [push,ite_eq_right hxy,norm_zero,mul_zero]
    exact mul_nonneg hfactor (FlatHeat.heat_nonneg _ _)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization ManifoldKernelExtension Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology NNReal
variable {X B : Type*} [MetricSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [NormedAddCommGroup B]

omit [IsManifold Model ∞ X] in
lemma push_continuous (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (K : Space × Space → B)
    (hK : Continuous K) (hsupp : Function.support K ⊆ L ×ˢ L) :
    Continuous (push p K) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hh := push_joint_continuousAt p (fun _ : Unit => K) (L ×ˢ L) (hL.prod hL)
    (fun _ h => ⟨hLt h.1,hLt h.2⟩) (fun _ => hsupp) ()
    (fun w => hK.continuousAt.comp continuousAt_snd) z
  exact hh.comp (continuousAt_const.prodMk continuousAt_id)

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)

include hs ht in

lemma push_gaussian_row (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (C : ℝ≥0)
    (hLip : LipschitzOnWith C (extChartAt Model p).symm L)
    (D : ℝ) (hD : 0 ≤ D) (hDb : ∀ z ∈ L, chartDensity J α p z ≤ D)
    (K : Space × Space → B) (hKc : Continuous K) (hsupp : Function.support K ⊆ L ×ˢ L)
    (n : ℕ) {a t M : ℝ} (ha : 0 < a) (htp : 0 < t) (hM : 0 ≤ M)
    (hK : ∀ q y, ‖K (q,y)‖ ≤ M*FlatHeat.heat (a*t) (y-q)) (x : X) :
    Integrable (fun y => VolterraBounds.weight n t x y*‖push p K (x,y)‖) (geometricVolume A J α) ∧
    (∫ y, VolterraBounds.weight n t x y*‖push p K (x,y)‖ ∂geometricVolume A J α) ≤
      D*((max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))) := by
  let c := (max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))
  have hc0 : 0 ≤ c := by dsimp [c] <;> positivity
  let f := fun y => VolterraBounds.weight n t x y*‖push p K (x,y)‖
  have hf : Continuous f := (VolterraBounds.weight_continuous n t x).mul
    (((push_continuous p L hL hLt K hKc hsupp).comp (continuous_const.prodMk continuous_id)).norm)
  have hf0 (y : X) : 0 ≤ f y := mul_nonneg (VolterraBounds.weight_pos n htp x y).le (norm_nonneg _)
  let := geometricVolume_finite A J α hs ht
  refine ⟨hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),?_⟩
  have hfs : Function.support f ⊆ (extChartAt Model p).symm '' L := by
    intro y hy
    have hk : (x,y) ∈ Function.support (push p K) := by
      intro he
      exact hy (by dsimp [f]; rw [he,norm_zero,mul_zero])
    obtain ⟨z,hz,he⟩ := support_push p K (L ×ˢ L) hsupp hk
    exact ⟨z.2,hz.2,congrArg Prod.snd he⟩
  have hg : Integrable (fun z : Space => c*FlatHeat.heat (2*a*t) (z-extChartAt Model p x)) :=
    ((FlatHeat.heat_integrable (by positivity : 0 < 2*a*t)).comp_sub_right _).const_mul c
  have hb := integral_chart_bound J α hs ht A p L hL hLt D hD hDb f hf hf0 hfs _ hg
    (fun z => mul_nonneg hc0 (FlatHeat.heat_nonneg _ _)) (fun z hz => by
      have hp := push_weighted_gaussian p L C hLip K hsupp n ha htp hM hK x ((extChartAt Model p).symm z)
      simpa only [(extChartAt Model p).right_inv hz] using hp)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  rw [integral_const_mul,integral_sub_right_eq_self,FlatHeat.heat_integral (by positivity),mul_one]

include hs ht in

lemma push_gaussian_col (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (C : ℝ≥0)
    (hLip : LipschitzOnWith C (extChartAt Model p).symm L)
    (D : ℝ) (hD : 0 ≤ D) (hDb : ∀ z ∈ L, chartDensity J α p z ≤ D)
    (K : Space × Space → B) (hKc : Continuous K) (hsupp : Function.support K ⊆ L ×ˢ L)
    (n : ℕ) {a t M : ℝ} (ha : 0 < a) (htp : 0 < t) (hM : 0 ≤ M)
    (hK : ∀ q y, ‖K (q,y)‖ ≤ M*FlatHeat.heat (a*t) (y-q)) (y : X) :
    Integrable (fun x => VolterraBounds.weight n t x y*‖push p K (x,y)‖) (geometricVolume A J α) ∧
    (∫ x, VolterraBounds.weight n t x y*‖push p K (x,y)‖ ∂geometricVolume A J α) ≤
      D*((max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))) := by
  let c := (max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))
  have hc0 : 0 ≤ c := by dsimp [c] <;> positivity
  let f := fun x => VolterraBounds.weight n t x y*‖push p K (x,y)‖
  have hw : Continuous (fun x => VolterraBounds.weight n t x y) := by
    unfold VolterraBounds.weight
    fun_prop
  have hf : Continuous f := hw.mul
    (((push_continuous p L hL hLt K hKc hsupp).comp (continuous_id.prodMk continuous_const)).norm)
  have hf0 (x : X) : 0 ≤ f x := mul_nonneg (VolterraBounds.weight_pos n htp x y).le (norm_nonneg _)
  let := geometricVolume_finite A J α hs ht
  refine ⟨hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),?_⟩
  have hfs : Function.support f ⊆ (extChartAt Model p).symm '' L := by
    intro x hx
    have hk : (x,y) ∈ Function.support (push p K) := by
      intro he
      exact hx (by dsimp [f]; rw [he,norm_zero,mul_zero])
    obtain ⟨z,hz,he⟩ := support_push p K (L ×ˢ L) hsupp hk
    exact ⟨z.1,hz.1,congrArg Prod.fst he⟩
  have hg : Integrable (fun z : Space => c*FlatHeat.heat (2*a*t) (extChartAt Model p y-z)) :=
    ((FlatHeat.heat_integrable (by positivity : 0 < 2*a*t)).comp_sub_left _).const_mul c
  have hb := integral_chart_bound J α hs ht A p L hL hLt D hD hDb f hf hf0 hfs _ hg
    (fun z => mul_nonneg hc0 (FlatHeat.heat_nonneg _ _)) (fun z hz => by
      have hp := push_weighted_gaussian p L C hLip K hsupp n ha htp hM hK ((extChartAt Model p).symm z) y
      simpa only [(extChartAt Model p).right_inv hz] using hp)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  rw [integral_const_mul,integral_sub_left_eq_self,FlatHeat.heat_integral (by positivity),mul_one]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgePushedHeatBound
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
lemma heat_time_bound {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (z : V) :
    heat (a*t) z ≤ ((4*Real.pi*a)⁻¹)^2/t^2 := by
  have he : Real.exp (-‖z‖^2/(4*(a*t))) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  calc
    _ ≤ (4*Real.pi*(a*t))⁻¹^2*1 := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := by simp only [mul_one,← mul_assoc,mul_inv, mul_pow,inv_pow,div_eq_mul_inv]
end TamingCompatibility.GeometricHilbert.FlatHeat

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization ManifoldKernelExtension Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology NNReal
variable {X B : Type*} [MetricSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [NormedRing B]

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [SecondCountableTopology B]

omit [IsManifold Model ∞ X] in
lemma pushedHeatKernel_measurable (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (K : ℝ → Space × Space → B)
    (hsupp : ∀ t, Function.support (K t) ⊆ L ×ˢ L)
    (hKc : ∀ t, 0 < t → ∀ z, ContinuousAt (fun v : ℝ × (Space × Space) => K v.1 v.2) (t,z)) :
    VolterraKernel.MeasurableKernel (pushedHeatKernel p K) := by
  let : MeasurableSpace B := borel B
  let : BorelSpace B := ⟨rfl⟩
  have hc : ContinuousOn (fun v : ℝ × (X × X) => push p (K v.1) (v.2.2,v.2.1)) {v | 0 < v.1} := by
    intro v hv
    have hh := push_joint_continuousAt p K (L ×ˢ L) (hL.prod hL)
      (fun _ h => ⟨hLt h.1,hLt h.2⟩) hsupp v.1 (hKc v.1 hv) (v.2.2,v.2.1)
    exact (hh.comp (f := fun w : ℝ × (X × X) => (w.1,(w.2.2,w.2.1))) (continuousAt_fst.prodMk (continuousAt_snd.snd.prodMk continuousAt_snd.fst))).continuousWithinAt
  have hm := hc.measurable_piecewise (continuousOn_const (c := (0 : B)))
    (isOpen_lt continuous_const continuous_fst).measurableSet
  have he : {v : ℝ × (X × X) | 0 < v.1}.piecewise
      (fun v => push p (K v.1) (v.2.2,v.2.1)) (fun _ => (0 : B)) =
      (fun v => pushedHeatKernel p K v.1 v.2.1 v.2.2) := by
    funext v
    by_cases hv : 0 < v.1
    · simp only [Set.piecewise,Set.mem_ofPred_eq,hv,ite_eq_left,pushedHeatKernel]
    · simp only [Set.piecewise,Set.mem_ofPred_eq,hv,ite_false, if_false,pushedHeatKernel]
  rw [he] at hm
  exact hm.stronglyMeasurable

variable [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)
include hs ht in

lemma pushedHeatKernel_bound (p : X) (L : Set Space) (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt Model p).target) (C : ℝ≥0)
    (hLip : LipschitzOnWith C (extChartAt Model p).symm L)
    (D : ℝ) (hD : 0 ≤ D) (hDb : ∀ z ∈ L, chartDensity J α p z ≤ D)
    (K : ℝ → Space × Space → B) (hsupp : ∀ t, Function.support (K t) ⊆ L ×ˢ L)
    (hKc : ∀ t, 0 < t → ∀ z, ContinuousAt (fun v : ℝ × (Space × Space) => K v.1 v.2) (t,z))
    (n : ℕ) (T : ℝ) {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hK : ∀ t, 0 < t → ∀ q y, ‖K t (q,y)‖ ≤ M*FlatHeat.heat (a*t) (y-q)) :
    ∃ H : ℝ, VolterraKernel.HeatBound (geometricVolume A J α) n T H (pushedHeatKernel p K) := by
  let c := (max (C:ℝ) 1)^n*M*(2^n*(4+4*(8*a)^n*(n.factorial : ℝ)))
  have hc : 0 ≤ c := by dsimp [c] <;> positivity
  let b := ((4*Real.pi*(2*a))⁻¹)^2
  have hb : 0 ≤ b := sq_nonneg _
  let H := c*b+D*c
  have hsup : c*b ≤ H := le_add_of_nonneg_right (mul_nonneg hD hc)
  have hint : D*c ≤ H := le_add_of_nonneg_left (mul_nonneg hc hb)
  have hcont (t : ℝ) (htp : 0 < t) : Continuous (K t) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hKc t htp z).comp (continuousAt_const.prodMk continuousAt_id)
  refine ⟨H,⟨pushedHeatKernel_measurable p L hL hLt K hsupp hKc,add_nonneg (mul_nonneg hc hb) (mul_nonneg hD hc),?_,?_,?_,?_,?_⟩⟩
  · intro t htpos x y
    rw [pushedHeatKernel,ite_eq_left htpos.1,VolterraBounds.weight_symm n t x y]
    have hh := push_weighted_gaussian p L C hLip (K t) (hsupp t) n ha htpos.1 hM (hK t htpos.1) y x
    calc
      _ ≤ c*FlatHeat.heat (2*a*t) (extChartAt Model p x-extChartAt Model p y) := hh
      _ ≤ c*(b/t^2) := mul_le_mul_of_nonneg_left (FlatHeat.heat_time_bound (by positivity : 0 < 2*a) htpos.1 _) hc
      _ = (c*b)/t^2 := by ring
      _ ≤ H/t^2 := div_le_div_of_nonneg_right hsup (sq_nonneg t)
  · intro t htpos x
    have hh := push_gaussian_col J α hs ht A p L hL hLt C hLip D hD hDb (K t) (hcont t htpos.1)
      (hsupp t) n ha htpos.1 hM (hK t htpos.1) x
    simpa only [pushedHeatKernel,ite_eq_left htpos.1,VolterraBounds.weight_symm n t x] using hh.1
  · intro t htpos x
    have hh := push_gaussian_col J α hs ht A p L hL hLt C hLip D hD hDb (K t) (hcont t htpos.1)
      (hsupp t) n ha htpos.1 hM (hK t htpos.1) x
    simpa only [pushedHeatKernel,ite_eq_left htpos.1,VolterraBounds.weight_symm n t x] using hh.2.trans hint
  · intro t htpos y
    have hh := push_gaussian_row J α hs ht A p L hL hLt C hLip D hD hDb (K t) (hcont t htpos.1)
      (hsupp t) n ha htpos.1 hM (hK t htpos.1) y
    simpa only [pushedHeatKernel,ite_eq_left htpos.1,VolterraBounds.weight_symm n t _ y] using hh.1
  · intro t htpos y
    have hh := push_gaussian_row J α hs ht A p L hL hLt C hLip D hD hDb (K t) (hcont t htpos.1)
      (hsupp t) n ha htpos.1 hM (hK t htpos.1) y
    simpa only [pushedHeatKernel,ite_eq_left htpos.1,VolterraBounds.weight_symm n t _ y] using hh.2.trans hint

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open _root_.MeasureTheory Set VolterraBounds
variable {X B : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [NormedRing B]
variable (μ : Measure X)

omit [SecondCountableTopology X] in
lemma HeatBound.finset_sum {ι : Type*} (s : Finset ι) (N : ℕ) (T : ℝ)
    (C : ι → ℝ) (K : ι → Kernel (X := X) (B := B))
    (hK : ∀ i ∈ s, HeatBound μ N T (C i) (K i)) :
    HeatBound μ N T (∑ i ∈ s, C i) (fun t x y => ∑ i ∈ s, K i t x y) := by
  have hm : MeasurableKernel (fun t x y => ∑ i ∈ s, K i t x y) :=
    s.stronglyMeasurable_fun_sum (fun i hi => (hK i hi).measurable)
  have hp (t : ℝ) (ht : 0 < t) (x y : X) :
      weight N t x y*‖∑ i ∈ s, K i t x y‖ ≤ ∑ i ∈ s, weight N t x y*‖K i t x y‖ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (weight_pos N ht x y).le
  have hr (t : ℝ) (ht : t ∈ Ioc 0 T) (x : X) :
      Integrable (fun y => weight N t x y*‖∑ i ∈ s, K i t x y‖) μ := by
    have hint := integrable_finsetSum s (fun i hi => (hK i hi).row_int t ht x)
    apply hint.mono' ((weight_continuous N t x).aestronglyMeasurable.mul
      ((hm.comp_measurable (measurable_const.prodMk (measurable_const.prodMk measurable_id))).norm.aestronglyMeasurable))
    filter_upwards [] with y
    change ‖weight N t x y*‖∑ i ∈ s, K i t x y‖‖ ≤ ∑ i ∈ s, weight N t x y*‖K i t x y‖
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (weight_pos N ht.1 x y).le (norm_nonneg _))]
    exact hp t ht.1 x y
  have hc (t : ℝ) (ht : t ∈ Ioc 0 T) (y : X) :
      Integrable (fun x => weight N t x y*‖∑ i ∈ s, K i t x y‖) μ := by
    have hint := integrable_finsetSum s (fun i hi => (hK i hi).col_int t ht y)
    have hw : Continuous (fun x => weight N t x y) := by unfold weight; fun_prop
    apply hint.mono' (hw.aestronglyMeasurable.mul
      ((hm.comp_measurable (measurable_const.prodMk (measurable_id.prodMk measurable_const))).norm.aestronglyMeasurable))
    filter_upwards [] with x
    change ‖weight N t x y*‖∑ i ∈ s, K i t x y‖‖ ≤ ∑ i ∈ s, weight N t x y*‖K i t x y‖
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (weight_pos N ht.1 x y).le (norm_nonneg _))]
    exact hp t ht.1 x y
  refine ⟨hm,Finset.sum_nonneg (fun i hi => (hK i hi).nonneg),?_,hr,?_,hc,?_⟩
  · intro t ht x y
    calc
      _ ≤ ∑ i ∈ s, weight N t x y*‖K i t x y‖ := hp t ht.1 x y
      _ ≤ ∑ i ∈ s, C i/t^2 := Finset.sum_le_sum (fun i hi => (hK i hi).sup t ht x y)
      _ = _ := by rw [Finset.sum_div]
  · intro t ht x
    calc
      _ ≤ ∫ y, ∑ i ∈ s, weight N t x y*‖K i t x y‖ ∂μ :=
        integral_mono (hr t ht x) (integrable_finsetSum s (fun i hi => (hK i hi).row_int t ht x)) (hp t ht.1 x)
      _ = ∑ i ∈ s, ∫ y, weight N t x y*‖K i t x y‖ ∂μ :=
        integral_finsetSum s (fun i hi => (hK i hi).row_int t ht x)
      _ ≤ _ := Finset.sum_le_sum (fun i hi => (hK i hi).row t ht x)
  · intro t ht y
    calc
      _ ≤ ∫ x, ∑ i ∈ s, weight N t x y*‖K i t x y‖ ∂μ :=
        integral_mono (hc t ht y) (integrable_finsetSum s (fun i hi => (hK i hi).col_int t ht y)) (fun x => hp t ht.1 x y)
      _ = ∑ i ∈ s, ∫ x, weight N t x y*‖K i t x y‖ ∂μ :=
        integral_finsetSum s (fun i hi => (hK i hi).col_int t ht y)
      _ ≤ _ := Finset.sum_le_sum (fun i hi => (hK i hi).col t ht y)

end TamingCompatibility.GeometricHilbert.VolterraKernel

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricDistance
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.RiemannianChartDistance
open Bundle Manifold Set Metric _root_.MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) 1 X]
  [RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ,E) x)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
  ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.TamingCompatibility.RiemannianChartDistance.inverseChartNormedAddCommGroup
lemma chart_segment_bound (p : X) (K : Set E) (hconv : Convex ℝ K)
    (hK : K ⊆ (extChartAt 𝓘(ℝ,E) p).target) (C : ℝ≥0)
    (hC : ∀ z ∈ K, ‖mfderiv[Set.range 𝓘(ℝ,E)] (extChartAt 𝓘(ℝ,E) p).symm z‖ₑ ≤ C)
    {q r : E} (hq : q ∈ K) (hr : r ∈ K) :
    riemannianEDist 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) p).symm q)
      ((extChartAt 𝓘(ℝ,E) p).symm r) ≤ C*edist q r := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) q r
  let γ := (extChartAt 𝓘(ℝ,E) p).symm ∘ η
  have hη : Icc 0 1 ⊆ η ⁻¹' K := by
    rw [← image_subset_iff,ContinuousAffineMap.coe_lineMap_eq,← segment_eq_image_lineMap]
    exact hconv.segment_subset hq hr
  have hηs : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 η (Icc 0 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact η.contDiff.contDiffOn
  have hb : riemannianEDist 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) p).symm q)
      ((extChartAt 𝓘(ℝ,E) p).symm r) ≤ pathELength 𝓘(ℝ,E) γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm p).comp hηs (hη.trans (preimage_mono hK))
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
  apply hb.trans
  rw [← lintegral_fderiv_lineMap_eq_edist,pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have he : mfderiv[Icc 0 1] γ t =
      (mfderiv[Set.range 𝓘(ℝ,E)] (extChartAt 𝓘(ℝ,E) p).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hK (hη ht))
    · exact hηs.mdifferentiableOn one_ne_zero t ht
    · exact (hη.trans (preimage_mono hK)).trans (preimage_mono (extChartAt_target_subset_range p))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hev : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[Set.range 𝓘(ℝ,E)] (extChartAt 𝓘(ℝ,E) p).symm (η t)) (mfderiv[Icc 0 1] η t 1) :=
    congrArg (fun L => L 1) he
  rw [hev]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  apply mul_le_mul (hC (η t) (hη ht))
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl
  · exact bot_le
  · exact bot_le

end TamingCompatibility.RiemannianChartDistance

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle Manifold ManifoldForms ManifoldVolume Set Filter Metric
open scoped Manifold ContDiff Topology NNReal ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
include hs in
lemma chartMetric_norm_continuousOn (p : X) :
    ContinuousOn (fun z => ‖chartMetric J α p z‖) (extChartAt Model p).target := by
  let : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  have hh : ContinuousOn (chartMetric J α p) (extChartAt Model p).target :=
    ((hs.invariantPart J).metricCoords J p).continuousOn
  exact (continuous_norm : Continuous (norm : (Space →L[ℝ] Space →L[ℝ] ℝ) → ℝ)).comp_continuousOn hh

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
  TamingCompatibility.RiemannianChartDistance.inverseChartNormedAddCommGroup

lemma inverseChart_opNorm (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨(hermitianMetric J α hs ht).toRiemannianMetric⟩
    ‖mfderivWithin Model Model (extChartAt Model p).symm (Set.range Model) z‖ ≤ Real.sqrt ‖chartMetric J α p z‖ := by
  dsimp only
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨(hermitianMetric J α hs ht).toRiemannianMetric⟩
  rw [show Set.range Model = univ by simp [Model],mfderivWithin_univ]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  have he : ‖mfderiv Model Model (extChartAt Model p).symm z u‖^2 = chartMetric J α p z u u := by
    exact (real_inner_self_eq_norm_sq _).symm.trans
      (chartMetric_derivative J α p hz u u).symm
  have hb : chartMetric J α p z u u ≤ ‖chartMetric J α p z‖*‖u‖^2 := by
    calc
      _ ≤ ‖chartMetric J α p z u u‖ := le_abs_self _
      _ ≤ ‖chartMetric J α p z‖*‖u‖*‖u‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ = _ := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg u))).mp
  rw [mul_pow,Real.sq_sqrt (norm_nonneg (chartMetric J α p z))]
  exact he.trans_le hb

variable [T2Space X] [CompactSpace X] [ConnectedSpace X]

lemma chartInverse_locallyLipschitz (p : X) :
    let := geometricMetricSpace J α hs ht
    LocallyLipschitzOn (extChartAt Model p).target (extChartAt Model p).symm := by
  dsimp only
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  let := geometricMetricSpace J α hs ht
  intro z hz
  have hc : ContinuousAt (fun y => ‖chartMetric J α p y‖) z :=
    (chartMetric_norm_continuousOn J α hs p).continuousAt
      ((isOpen_extChartAt_target p).mem_nhds hz)
  let C := Real.sqrt (‖chartMetric J α p z‖+1)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hn : {y | ‖chartMetric J α p y‖ < ‖chartMetric J α p z‖+1} ∈ 𝓝 z :=
    hc.preimage_mem_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((isOpen_extChartAt_target p).mem_nhds hz) hn)
  refine ⟨⟨C,hC⟩,Metric.ball z r,mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hr),?_⟩
  intro q hq y hy
  change hermitianEDist J α hs ht _ _ ≤ _
  apply RiemannianChartDistance.chart_segment_bound p _ (convex_ball z r)
    (fun _ h => (hrsub h).1) ⟨C,hC⟩ ?_ hq hy
  intro w hw
  have hb := (inverseChart_opNorm J α hs ht p (hrsub hw).1).trans
    (Real.sqrt_le_sqrt (le_of_lt (hrsub hw).2))
  exact ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp hb)

lemma chartInverse_compact_lipschitz (p : X) (K : Set Space)
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt Model p).target) :
    let := geometricMetricSpace J α hs ht
    ∃ C : ℝ≥0, LipschitzOnWith C (extChartAt Model p).symm K := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
    ((chartInverse_locallyLipschitz J α hs ht p).mono hKt)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeGlobalHeatBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology NNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X)

lemma actual_pushedHeatKernel_bound {B : Type*} [NormedRing B] [SecondCountableTopology B]
    (p : X) (Q : Set (Space × Space)) (hQ : IsCompact Q)
    (hQt : Q ⊆ (extChartAt Model p).target ×ˢ (extChartAt Model p).target)
    (K : ℝ → Space × Space → B) (hsupp : ∀ t, Function.support (K t) ⊆ Q)
    (hKc : ∀ t, 0 < t → ∀ z, ContinuousAt (fun v : ℝ × (Space × Space) => K v.1 v.2) (t,z))
    (n : ℕ) (T : ℝ) {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hK : ∀ t, 0 < t → ∀ q y, ‖K t (q,y)‖ ≤ M*FlatHeat.heat (a*t) (y-q)) :
    let := geometricMetricSpace J α hs ht
    ∃ H : ℝ, VolterraKernel.HeatBound (geometricVolume A J α) n T H (pushedHeatKernel p K) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let L := Prod.fst '' Q ∪ Prod.snd '' Q
  have hL : IsCompact L := (hQ.image continuous_fst).union (hQ.image continuous_snd)
  have hLt : L ⊆ (extChartAt Model p).target := by
    rintro z (⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩)
    · exact (hQt hw).1
    · exact (hQt hw).2
  have hQL : Q ⊆ L ×ˢ L := fun z hz =>
    ⟨Or.inl ⟨z,hz,rfl⟩,Or.inr ⟨z,hz,rfl⟩⟩
  obtain ⟨C,hC⟩ := chartInverse_compact_lipschitz J α hs ht p L hL hLt
  obtain ⟨D,hD,hDb⟩ := chart_density_compact_bound J α hs ht p L hL hLt
  exact pushedHeatKernel_bound J α hs ht A p L hL hLt C hC D hD hDb K
    (fun t => (hsupp t).trans hQL) hKc n T ha hM hK

variable (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

lemma assemble_heatBound
    (K : A.centers → ℝ → Space × Space → FrameSpace A →L[ℝ] FrameSpace A)
    (hsupp : ∀ p t, Function.support (K p t) ⊆ (D p).physicalCompact)
    (hcont : ∀ p t, 0 < t → ∀ z, ContinuousAt (fun v : ℝ × (Space × Space) => K p v.1 v.2) (t,z))
    (hgauss : ∀ p, ∃ M a : ℝ, 0 ≤ M ∧ 0 < a ∧ ∀ t : ℝ, 0 < t → ∀ q y : Space,
      ‖K p t (q,y)‖ ≤ M*FlatHeat.heat (a*t) (y-q)) (n : ℕ) (T : ℝ) :
    let := geometricMetricSpace J α hs ht
    ∃ H : ℝ, VolterraKernel.HeatBound (geometricVolume A J α) n T H (assemble A K) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  have hh (p : A.centers) : ∃ H : ℝ,
      VolterraKernel.HeatBound (geometricVolume A J α) n T H (pushedHeatKernel p.val (K p)) := by
    obtain ⟨M,a,hM,ha,hb⟩ := hgauss p
    exact actual_pushedHeatKernel_bound J α hs ht A p.val (D p).physicalCompact
      (D p).physicalCompact_compact (physicalCompact_target J α ht A D p)
      (K p) (hsupp p) (hcont p) n T ha hM hb
  choose H hH using hh
  have hb := VolterraKernel.HeatBound.finset_sum (geometricVolume A J α) Finset.univ n T H
    (fun p => pushedHeatKernel p.val (K p)) (fun p _ => hH p)
  have he : (fun t x y => ∑ p : A.centers, pushedHeatKernel p.val (K p) t x y) = assemble A K := by
    funext t x y
    by_cases h : 0 < t
    · simp only [pushedHeatKernel,assemble,ite_eq_left h]
    · simp only [pushedHeatKernel,assemble,ite_eq_right h,Finset.sum_const_zero]
  exact ⟨∑ p : A.centers, H p,he ▸ hb⟩

include hD in
lemma globalResidual_heatBound_oai (n : ℕ) (T : ℝ) :
    let := geometricMetricSpace J α hs ht
    ∃ H : ℝ, VolterraKernel.HeatBound (geometricVolume A J α) n T H (globalResidual J α ht A D) :=
  assemble_heatBound J α hs ht A D _
    (fun p t => (coordinateMatrix_support J α ht A D p _).trans
      ((subset_tsupport _).trans (partitionResidual_tsupport J α ht A D hD p t)))
    (fun p _ htpos z => (residualMatrix_smooth J α ht A D hD hs p htpos z).continuousAt)
    (residualFrameMatrix_gaussian J α ht A D hD hs) n T

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalResidual_heatBound_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalResidual_heatBound_oai.{u_1}
