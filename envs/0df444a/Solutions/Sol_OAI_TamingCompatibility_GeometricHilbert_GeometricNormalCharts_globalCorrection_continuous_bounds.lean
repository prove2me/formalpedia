-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCorrection_continuous_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:19:45.504544+00:00
-- url     : https://prove2.me/submissions/d7e5f92d-7541-4965-94e5-a7627b568a85

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc023
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalLeading_heatBound
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalResidual_heatBound
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledB_joint
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixPatch
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
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] normalGauge normalFirst

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixPatchMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixPatchMetricTensorNormedSpace
lemma leadingCoordinate_support (ψ χ : Space → ℝ) (t : ℝ) :
    Function.support (leadingCoordinate J α ht p D g B ψ χ t) ⊆
      Function.support ψ ×ˢ Function.support χ := by
  intro x hx
  constructor
  · intro h
    apply hx
    apply ContinuousLinearMap.ext
    intro u
    simp only [leadingCoordinate,smul_apply,h,zero_apply]
    simp
  · intro h
    apply hx
    apply ContinuousLinearMap.ext
    intro u
    simp only [leadingCoordinate,smul_apply,h,zero_apply]
    simp

lemma leadingCoordinate_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (ψ χ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    {t : ℝ} (htpos : 0 < t) {x : Space × Space}
    (hx : (x.1,0) ∈ normalDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) =>
      leadingCoordinate J α ht p D g B ψ χ v.1 v.2) (t,x) := by
  have hψ' : ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => ψ v.2.1) (t,x) :=
    hψ.contDiffAt.comp (t,x) contDiffAt_snd.fst
  have hχ' : ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => χ v.2.2) (t,x) :=
    hχ.contDiffAt.comp (t,x) contDiffAt_snd.snd
  have hh : ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => FlatHeat.heat v.1 v.2.2) (t,x) :=
    (FlatHeat.heat_joint_contDiffAt (x := (t,x.2)) (ne_of_gt htpos)).comp (t,x)
      (contDiffAt_fst.prodMk contDiffAt_snd.snd)
  exact ((hψ'.mul hχ').mul hh).smul
    ((normalGauge_smooth J α ht p D g B hs hg hB hx).comp (t,x) contDiffAt_snd)

lemma leadingPatch_joint_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (K : Set (Space × Space)) (hK : IsCompact K)
    (hFK : Function.support ψ ×ˢ Function.support χ ⊆ K)
    (O : Set Space) (hKO : K ⊆ parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O)
    {t : ℝ} (htpos : 0 < t) (y : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) =>
      leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ v.1 v.2) (t,y) := by
  apply KernelExtension.push_family_contDiffAt _ _ K hK (fun x hx => (hKO hx).1.1.1)
    (fun s => (leadingCoordinate_support J α ht p D g B ψ χ s).trans hFK)
  · intro x hx
    exact leadingCoordinate_smooth J α ht p D g B hs hg hB ψ χ hψ hχ htpos (hKO hx).1.2.2
  · intro x hx
    have hi := (hKO hx).1.1.2
    exact (inverseRegularDomain_smooth _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq) _ hi).contDiffAt
      ((inverseRegularDomain_open _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq)).mem_nhds hi)

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

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_r42a5af_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_r42a5af_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
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

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_r42a5af_2 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_r42a5af_2 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
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
lemma partitionLeading_smooth (hs : IsSmooth α) (p : A.centers) {t : ℝ} (htp : 0 < t) (y : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => partitionLeading J α ht A D p v.1 v.2) (t,y) :=
  leadingPatch_joint_smooth J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension hs
    (D p).metric_smooth (D p).frame_smooth (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff
    (coordinatePartition_smooth_compact A p).1 (D p).normalCutoff.contDiff
    (D p).normalCompact (D p).normalCompact_compact
    ((Set.prod_mono Set.Subset.rfl (subset_tsupport _)).trans (partition_patch_support J α ht A D hD p))
    (D p).actualDomain (D p).tube htp y

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
lemma partitionLeading_tsupport (p : A.centers) (t : ℝ) :
    tsupport (partitionLeading J α ht A D p t) ⊆ (D p).physicalCompact := by
  apply KernelExtension.tsupport_push_subset _ _ _ (D p).normalCompact_compact (D p).normalCompact_source
  exact (leadingCoordinate_support J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    _ _ t).trans ((Set.prod_mono Set.Subset.rfl (subset_tsupport _)).trans
      (partition_patch_support J α ht A D hD p))

include hD in
lemma partitionResidual_tsupport (p : A.centers) (t : ℝ) :
    tsupport (partitionResidual J α ht A D p t) ⊆ (D p).physicalCompact := by
  apply KernelExtension.tsupport_push_subset _ _ _ (D p).normalCompact_compact (D p).normalCompact_source
  exact (residualCoordinate_support J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    _ _ t).trans (partition_patch_support J α ht A D hD p)

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
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.KernelSeries.clip_of_mem _root_.OAI.TamingCompatibility.GeometricHilbert.KernelSeries.clip_of_not_mem _root_.OAI.TamingCompatibility.GeometricHilbert.KernelSeries.term_outside
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

lemma weight_submultiplicative (N : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (x z y : X) : weight N (t+s) x y ≤ weight N t x z * weight N s z y := by
  rw [weight, weight, weight, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hT : 0 < Real.sqrt (t+s) := Real.sqrt_pos.2 (add_pos ht hs)
  have h1 := div_le_div_of_nonneg_left (dist_nonneg (x := x) (y := z))
    (Real.sqrt_pos.2 ht) (Real.sqrt_le_sqrt (le_add_of_nonneg_right hs.le))
  have h2 := div_le_div_of_nonneg_left (dist_nonneg (x := z) (y := y))
    (Real.sqrt_pos.2 hs) (Real.sqrt_le_sqrt (le_add_of_nonneg_left ht.le))
  have hd := div_le_div_of_nonneg_right (dist_triangle x z y) hT.le
  rw [add_div] at hd
  have hmul : 0 ≤ (dist x z / Real.sqrt t) * (dist z y / Real.sqrt s) := by positivity
  nlinarith

lemma weight_continuous (N : ℕ) (t : ℝ) (x : X) : Continuous (weight N t x) := by
  unfold weight
  fun_prop

variable [MeasurableSpace X] [NormedRing B] [NormedAlgebra ℝ B]

lemma spatial_convolution_bound (μ : Measure X) (N : ℕ) {t s A C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hA : 0 ≤ A)
    (K L : X → X → B) (x y : X)
    (hK : ∀ z, weight N t x z * ‖K x z‖ ≤ A)
    (hL : Integrable (fun z => weight N s z y * ‖L z y‖) μ)
    (hLI : (∫ z, weight N s z y * ‖L z y‖ ∂μ) ≤ C)
    (hprod : AEStronglyMeasurable (fun z => K x z * L z y) μ) :
    Integrable (fun z => K x z * L z y) μ ∧
      weight N (t+s) x y * ‖∫ z, K x z * L z y ∂μ‖ ≤ A*C := by
  have hw := weight_pos N (add_pos ht hs) x y
  have hpoint (z : X) : weight N (t+s) x y * ‖K x z * L z y‖ ≤
      A * (weight N s z y * ‖L z y‖) := by
    calc
      _ ≤ (weight N t x z * weight N s z y) * (‖K x z‖*‖L z y‖) :=
        mul_le_mul (weight_submultiplicative N ht hs x z y) (norm_mul_le _ _)
          (norm_nonneg _) (mul_nonneg (weight_pos N ht x z).le (weight_pos N hs z y).le)
      _ = (weight N t x z * ‖K x z‖) * (weight N s z y * ‖L z y‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hK z)
        (mul_nonneg (weight_pos N hs z y).le (norm_nonneg _))
  have hint : Integrable (fun z => K x z * L z y) μ := by
    apply (hL.const_mul (A / weight N (t+s) x y)).mono' hprod
    filter_upwards [] with z
    have h := (le_div_iff₀ hw).mpr (show ‖K x z * L z y‖ * weight N (t+s) x y ≤
      A * (weight N s z y * ‖L z y‖) by simpa only [mul_comm] using hpoint z)
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  refine ⟨hint, ?_⟩
  calc
    _ ≤ weight N (t+s) x y * (∫ z, ‖K x z * L z y‖ ∂μ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hw.le
    _ = ∫ z, weight N (t+s) x y * ‖K x z * L z y‖ ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ z, A * (weight N s z y * ‖L z y‖) ∂μ :=
      integral_mono (hint.norm.const_mul _) (hL.const_mul _) hpoint
    _ = A * (∫ z, weight N s z y * ‖L z y‖ ∂μ) := integral_const_mul _ _
    _ ≤ A*C := mul_le_mul_of_nonneg_left hLI hA

lemma spatial_convolution_bound_right (μ : Measure X) (N : ℕ) {t s A C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hC : 0 ≤ C)
    (K L : X → X → B) (x y : X)
    (hK : Integrable (fun z => weight N t x z * ‖K x z‖) μ)
    (hKI : (∫ z, weight N t x z * ‖K x z‖ ∂μ) ≤ A)
    (hL : ∀ z, weight N s z y * ‖L z y‖ ≤ C)
    (hprod : AEStronglyMeasurable (fun z => K x z * L z y) μ) :
    Integrable (fun z => K x z * L z y) μ ∧
      weight N (t+s) x y * ‖∫ z, K x z * L z y ∂μ‖ ≤ A*C := by
  have hw := weight_pos N (add_pos ht hs) x y
  have hpoint (z : X) : weight N (t+s) x y * ‖K x z * L z y‖ ≤
      C * (weight N t x z * ‖K x z‖) := by
    calc
      _ ≤ (weight N t x z * weight N s z y) * (‖K x z‖*‖L z y‖) :=
        mul_le_mul (weight_submultiplicative N ht hs x z y) (norm_mul_le _ _)
          (norm_nonneg _) (mul_nonneg (weight_pos N ht x z).le (weight_pos N hs z y).le)
      _ = (weight N s z y * ‖L z y‖) * (weight N t x z * ‖K x z‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hL z)
        (mul_nonneg (weight_pos N ht x z).le (norm_nonneg _))
  have hint : Integrable (fun z => K x z * L z y) μ := by
    apply (hK.const_mul (C / weight N (t+s) x y)).mono' hprod
    filter_upwards [] with z
    have h := (le_div_iff₀ hw).mpr (show ‖K x z * L z y‖ * weight N (t+s) x y ≤
      C * (weight N t x z * ‖K x z‖) by simpa only [mul_comm] using hpoint z)
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  refine ⟨hint, ?_⟩
  calc
    _ ≤ weight N (t+s) x y * (∫ z, ‖K x z * L z y‖ ∂μ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hw.le
    _ = ∫ z, weight N (t+s) x y * ‖K x z * L z y‖ ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ z, C * (weight N t x z * ‖K x z‖) ∂μ :=
      integral_mono (hint.norm.const_mul _) (hK.const_mul _) hpoint
    _ = C * (∫ z, weight N t x z * ‖K x z‖ ∂μ) := integral_const_mul _ _
    _ ≤ C*A := mul_le_mul_of_nonneg_left hKI hC
    _ = A*C := mul_comm _ _

lemma time_integrand_bound (μ : Measure X) (N : ℕ) {t s A C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hst : s < t) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (K L : ℝ → X → X → B) (x y : X)
    (hKsup : ∀ z, weight N (t-s) x z * ‖K (t-s) x z‖ ≤ A/(t-s)^2)
    (hLsup : ∀ z, weight N s z y * ‖L s z y‖ ≤ C/s^2)
    (hK : Integrable (fun z => weight N (t-s) x z * ‖K (t-s) x z‖) μ)
    (hL : Integrable (fun z => weight N s z y * ‖L s z y‖) μ)
    (hKI : (∫ z, weight N (t-s) x z * ‖K (t-s) x z‖ ∂μ) ≤ A)
    (hLI : (∫ z, weight N s z y * ‖L s z y‖ ∂μ) ≤ C)
    (hprod : AEStronglyMeasurable (fun z => K (t-s) x z * L s z y) μ) :
    Integrable (fun z => K (t-s) x z * L s z y) μ ∧
      weight N t x y * ‖∫ z, K (t-s) x z * L s z y ∂μ‖ ≤ 4*A*C/t^2 := by
  have hts : 0 < t-s := sub_pos.mpr hst
  have hleft := spatial_convolution_bound μ N hts hs (by positivity : 0 ≤ A/(t-s)^2)
    (K (t-s)) (L s) x y hKsup hL hLI hprod
  refine ⟨hleft.1, ?_⟩
  by_cases hhalf : s ≤ t/2
  · have hden : t^2/4 ≤ (t-s)^2 := by nlinarith [sq_nonneg (t/2-s)]
    have hdiv : A/(t-s)^2 ≤ 4*A/t^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hts) (sq_pos_of_pos ht)).2
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hden)]
    calc
      _ ≤ (A/(t-s)^2)*C := by simpa using hleft.2
      _ ≤ (4*A/t^2)*C := mul_le_mul_of_nonneg_right hdiv hC
      _ = _ := by ring
  · have hden : t^2/4 ≤ s^2 := by nlinarith [sq_nonneg (s-t/2)]
    have hdiv : C/s^2 ≤ 4*C/t^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos ht)).2
      nlinarith [mul_nonneg hC (sub_nonneg.mpr hden)]
    have hright := spatial_convolution_bound_right μ N hts hs
      (by positivity : 0 ≤ C/s^2) (K (t-s)) (L s) x y hK hKI hLsup hprod
    calc
      _ ≤ A*(C/s^2) := by simpa using hright.2
      _ ≤ A*(4*C/t^2) := mul_le_mul_of_nonneg_left hdiv hA
      _ = _ := by ring

lemma time_convolution_bound (μ : Measure X) (N : ℕ) {t A C : ℝ}
    (ht : 0 < t) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (K L : ℝ → X → X → B) (x y : X)
    (hKsup : ∀ s ∈ Ioo 0 t, ∀ z, weight N (t-s) x z * ‖K (t-s) x z‖ ≤ A/(t-s)^2)
    (hLsup : ∀ s ∈ Ioo 0 t, ∀ z, weight N s z y * ‖L s z y‖ ≤ C/s^2)
    (hK : ∀ s ∈ Ioo 0 t, Integrable (fun z => weight N (t-s) x z * ‖K (t-s) x z‖) μ)
    (hL : ∀ s ∈ Ioo 0 t, Integrable (fun z => weight N s z y * ‖L s z y‖) μ)
    (hKI : ∀ s ∈ Ioo 0 t, (∫ z, weight N (t-s) x z * ‖K (t-s) x z‖ ∂μ) ≤ A)
    (hLI : ∀ s ∈ Ioo 0 t, (∫ z, weight N s z y * ‖L s z y‖ ∂μ) ≤ C)
    (hprod : ∀ s ∈ Ioo 0 t, AEStronglyMeasurable (fun z => K (t-s) x z * L s z y) μ)
    (htime : AEStronglyMeasurable (fun s => ∫ z, K (t-s) x z * L s z y ∂μ)
      (volume.restrict (Ioo 0 t))) :
    IntegrableOn (fun s => ∫ z, K (t-s) x z * L s z y ∂μ) (Ioo 0 t) ∧
      weight N t x y * ‖∫ s in Ioo 0 t, ∫ z, K (t-s) x z * L s z y ∂μ‖ ≤ 4*A*C/t := by
  have hw := weight_pos N ht x y
  have hpoint (s : ℝ) (hs : s ∈ Ioo 0 t) := (time_integrand_bound μ N ht hs.1 hs.2
    hA hC K L x y (hKsup s hs) (hLsup s hs) (hK s hs) (hL s hs)
    (hKI s hs) (hLI s hs) (hprod s hs)).2
  have hi : IntegrableOn (fun s => ∫ z, K (t-s) x z * L s z y ∂μ) (Ioo 0 t) := by
    apply (integrableOn_const (C := 4*A*C/t^2/weight N t x y)
      (hs := measure_Ioo_lt_top.ne)).mono' htime
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    apply (le_div_iff₀ hw).2
    simpa only [mul_comm] using hpoint s hs
  refine ⟨hi, ?_⟩
  calc
    _ ≤ weight N t x y * (∫ s in Ioo 0 t, ‖∫ z, K (t-s) x z * L s z y ∂μ‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hw.le
    _ = ∫ s in Ioo 0 t, weight N t x y * ‖∫ z, K (t-s) x z * L s z y ∂μ‖ :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ _s in Ioo 0 t, 4*A*C/t^2 := by
      apply integral_mono_ae (hi.norm.const_mul _)
        (integrableOn_const (hs := measure_Ioo_lt_top.ne))
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hpoint s hs
    _ = 4*A*C/t := by
      simp only [integral_const, measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le ht.le,
        smul_eq_mul, sub_zero]
      field_simp

end TamingCompatibility.GeometricHilbert.VolterraBounds

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.SchurIntegration
open _root_.MeasureTheory
variable {X Y B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
variable (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]

omit [SFinite μ] in
lemma product_integrable {f : X → ℝ} {g : X → Y → ℝ} {C : ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hg : StronglyMeasurable (Function.uncurry g)) (hg0 : ∀ x y, 0 ≤ g x y)
    (hgi : ∀ x, Integrable (g x) ν) (hC : ∀ x, (∫ y, g x y ∂ν) ≤ C) :
    Integrable (fun p : X × Y => f p.1 * g p.1 p.2) (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : X × Y => f p.1 * g p.1 p.2) (μ.prod ν) :=
    hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => (hgi x).const_mul (f x)), ?_⟩
  have hi (x : X) : (∫ y, ‖f x*g x y‖ ∂ν) = f x * ∫ y, g x y ∂ν := by
    simp_rw [Real.norm_of_nonneg (mul_nonneg (hf0 x) (hg0 x _))]
    exact integral_const_mul _ _
  simp_rw [hi]
  apply (hf.mul_const C).mono'
    (by simpa only [hi] using hm.norm.integral_prod_right')
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (mul_nonneg (hf0 x) (integral_nonneg (hg0 x)))]
    exact mul_le_mul_of_nonneg_left (hC x) (hf0 x)

omit [SFinite μ] in
lemma product_integral_le {f : X → ℝ} {g : X → Y → ℝ} {C : ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hg : StronglyMeasurable (Function.uncurry g)) (hg0 : ∀ x y, 0 ≤ g x y)
    (hgi : ∀ x, Integrable (g x) ν) (hC : ∀ x, (∫ y, g x y ∂ν) ≤ C) :
    (∫ x, ∫ y, f x*g x y ∂ν ∂μ) ≤ C * ∫ x, f x ∂μ := by
  have hi := product_integrable μ ν hf hf0 hg hg0 hgi hC
  rw [mul_comm C, ← integral_mul_const]
  apply integral_mono hi.integral_prod_left (hf.mul_const C)
  intro x
  change (∫ y, f x*g x y ∂ν) ≤ f x*C
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (hf0 x)

lemma norm_integral_row {f : X → ℝ} {g : X → Y → ℝ} {C : ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hg : StronglyMeasurable (Function.uncurry g)) (hg0 : ∀ x y, 0 ≤ g x y)
    (hgi : ∀ x, Integrable (g x) ν) (hC : ∀ x, (∫ y, g x y ∂ν) ≤ C)
    (H : X → Y → B) (hH : StronglyMeasurable (Function.uncurry H))
    (hdom : ∀ x y, ‖H x y‖ ≤ f x*g x y) :
    Integrable (fun y => ∫ x, H x y ∂μ) ν ∧
      (∫ y, ‖∫ x, H x y ∂μ‖ ∂ν) ≤ C * ∫ x, f x ∂μ := by
  have hi := product_integrable μ ν hf hf0 hg hg0 hgi hC
  have hHi : Integrable (Function.uncurry H) (μ.prod ν) :=
    hi.mono' hH.aestronglyMeasurable (Filter.Eventually.of_forall fun p => hdom p.1 p.2)
  refine ⟨hHi.integral_prod_right, ?_⟩
  calc
    _ ≤ ∫ y, ∫ x, f x*g x y ∂μ ∂ν := by
      apply integral_mono_ae hHi.integral_prod_right.norm hi.integral_prod_right
      filter_upwards [hi.prod_left_ae] with y hy
      exact norm_integral_le_of_norm_le hy (Filter.Eventually.of_forall fun x => hdom x y)
    _ = ∫ x, ∫ y, f x*g x y ∂ν ∂μ := (integral_integral_swap hi).symm
    _ ≤ _ := product_integral_le μ ν hf hf0 hg hg0 hgi hC

lemma integral_row_bound {F : X → ℝ} (hF : Integrable F μ)
    (H : X → Y → B) (hH : StronglyMeasurable (Function.uncurry H))
    (hHi : ∀ x, Integrable (H x) ν)
    (hrow : ∀ x, (∫ y, ‖H x y‖ ∂ν) ≤ F x) :
    Integrable (Function.uncurry H) (μ.prod ν) ∧
    Integrable (fun y => ∫ x, H x y ∂μ) ν ∧
    (∫ y, ‖∫ x, H x y ∂μ‖ ∂ν) ≤ ∫ x, F x ∂μ := by
  have hi : Integrable (Function.uncurry H) (μ.prod ν) := by
    apply (integrable_prod_iff hH.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hHi, ?_⟩
    apply hF.mono' hH.aestronglyMeasurable.norm.integral_prod_right'
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hrow x
  refine ⟨hi, hi.integral_prod_right, ?_⟩
  calc
    _ ≤ ∫ y, ∫ x, ‖H x y‖ ∂μ ∂ν := by
      exact integral_mono hi.integral_prod_right.norm hi.norm.integral_prod_right
        (fun y => norm_integral_le_integral_norm _)
    _ = ∫ x, ∫ y, ‖H x y‖ ∂ν ∂μ := (integral_integral_swap hi.norm).symm
    _ ≤ _ := integral_mono hi.norm.integral_prod_left hF hrow

lemma integral_row_bound_ae {F : X → ℝ} (hF : Integrable F μ)
    (H : X → Y → B) (hH : AEStronglyMeasurable (Function.uncurry H) (μ.prod ν))
    (hHi : ∀ᵐ x ∂μ, Integrable (H x) ν)
    (hrow : ∀ᵐ x ∂μ, (∫ y, ‖H x y‖ ∂ν) ≤ F x) :
    Integrable (Function.uncurry H) (μ.prod ν) ∧
    Integrable (fun y => ∫ x, H x y ∂μ) ν ∧
    (∫ y, ‖∫ x, H x y ∂μ‖ ∂ν) ≤ ∫ x, F x ∂μ := by
  have hi : Integrable (Function.uncurry H) (μ.prod ν) := by
    apply (integrable_prod_iff hH).mpr
    refine ⟨hHi, ?_⟩
    apply hF.mono' hH.norm.integral_prod_right'
    filter_upwards [hrow] with x hx
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hx
  refine ⟨hi, hi.integral_prod_right, ?_⟩
  calc
    _ ≤ ∫ y, ∫ x, ‖H x y‖ ∂μ ∂ν := by
      exact integral_mono hi.integral_prod_right.norm hi.norm.integral_prod_right
        (fun y => norm_integral_le_integral_norm _)
    _ = ∫ x, ∫ y, ‖H x y‖ ∂ν ∂μ := (integral_integral_swap hi.norm).symm
    _ ≤ _ := integral_mono_ae hi.norm.integral_prod_left hF hrow

end TamingCompatibility.GeometricHilbert.SchurIntegration

end
end

noncomputable section
namespace TamingCompatibility.GeometricHilbert.SchurKernel
open _root_.MeasureTheory VolterraBounds
variable {X B : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [NormedRing B] [NormedAlgebra ℝ B]
variable (μ : Measure X) [SFinite μ]

lemma convolution_row (N : ℕ) {t s A C : ℝ} (ht : 0 < t) (hs : 0 < s)
    (K L : X → X → B) (x : X)
    (hK : Integrable (fun z => weight N t x z * ‖K x z‖) μ)
    (hKI : (∫ z, weight N t x z * ‖K x z‖ ∂μ) ≤ A)
    (hL : StronglyMeasurable (fun zy : X × X => weight N s zy.1 zy.2 * ‖L zy.1 zy.2‖))
    (hLi : ∀ z, Integrable (fun y => weight N s z y * ‖L z y‖) μ)
    (hLI : ∀ z, (∫ y, weight N s z y * ‖L z y‖ ∂μ) ≤ C)
    (hC : 0 ≤ C)
    (hH : StronglyMeasurable (fun zy : X × X =>
      weight N (t+s) x zy.2 • (K x zy.1 * L zy.1 zy.2))) :
    Integrable (fun y => weight N (t+s) x y * ‖∫ z, K x z * L z y ∂μ‖) μ ∧
    (∫ y, weight N (t+s) x y * ‖∫ z, K x z * L z y ∂μ‖ ∂μ) ≤ A*C := by
  have hb : ∀ z y, ‖weight N (t+s) x y • (K x z * L z y)‖ ≤
      (weight N t x z*‖K x z‖)*(weight N s z y*‖L z y‖) := by
    intro z y
    rw [norm_smul, Real.norm_of_nonneg (weight_pos N (add_pos ht hs) x y).le]
    calc
      _ ≤ weight N (t+s) x y*(‖K x z‖*‖L z y‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (weight_pos N (add_pos ht hs) x y).le
      _ ≤ (weight N t x z*weight N s z y)*(‖K x z‖*‖L z y‖) :=
        mul_le_mul_of_nonneg_right (weight_submultiplicative N ht hs x z y) (by positivity)
      _ = _ := by ring
  have hh := SchurIntegration.norm_integral_row μ μ
    (g := fun z y => weight N s z y*‖L z y‖) hK
    (fun z => mul_nonneg (weight_pos N ht x z).le (norm_nonneg _)) hL
    (fun z y => mul_nonneg (weight_pos N hs z y).le (norm_nonneg _))
    hLi hLI (fun z y => weight N (t+s) x y • (K x z * L z y)) hH hb
  have he (y : X) : ‖∫ z, weight N (t+s) x y • (K x z * L z y) ∂μ‖ =
      weight N (t+s) x y*‖∫ z, K x z * L z y ∂μ‖ := by
    rw [integral_smul, norm_smul, Real.norm_of_nonneg (weight_pos N (add_pos ht hs) x y).le]
  refine ⟨?_, ?_⟩
  · simpa only [he] using hh.1.norm
  · have h := hh.2
    simp_rw [he] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hKI hC])

end TamingCompatibility.GeometricHilbert.SchurKernel

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open _root_.MeasureTheory Set VolterraBounds
variable {X B : Type*} [MeasurableSpace X]
  [NormedRing B] [NormedAlgebra ℝ B]
variable (μ : Measure X) [SFinite μ]

lemma spatial_measurable (K L : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (hL : MeasurableKernel L) :
    StronglyMeasurable (fun p : (ℝ × X × X) × ℝ =>
      spatial μ K L p.1.1 p.2 p.1.2.1 p.1.2.2) := by
  have hKm : Measurable (fun q : ((ℝ × X × X) × ℝ) × X =>
      (q.1.1.1-q.1.2, q.1.1.2.1, q.2)) := by fun_prop
  have hLm : Measurable (fun q : ((ℝ × X × X) × ℝ) × X =>
      (q.1.2, q.2, q.1.1.2.2)) := by fun_prop
  exact ((hK.comp_measurable hKm).mul (hL.comp_measurable hLm)).integral_prod_right

lemma convolution_measurable (K L : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (hL : MeasurableKernel L) :
    MeasurableKernel (convolution μ K L) := by
  have hm := spatial_measurable μ K L hK hL
  have hset : MeasurableSet {p : (ℝ × X × X) × ℝ | p.2 ∈ Ioo 0 p.1.1} := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.fst))
  have hmi : StronglyMeasurable (Function.uncurry (fun (p : ℝ × X × X) (s : ℝ) =>
      (Ioo 0 p.1).indicator (fun s => spatial μ K L p.1 s p.2.1 p.2.2) s)) :=
    hm.indicator hset
  have hi := hmi.integral_prod_right (ν := volume)
  simpa only [MeasurableKernel, convolution, integral_indicator measurableSet_Ioo] using hi

lemma spatial_section (K L : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (hL : MeasurableKernel L) (t x y) :
    StronglyMeasurable (fun s => spatial μ K L t s x y) :=
  (spatial_measurable μ K L hK hL).comp_measurable
    (show Measurable (fun s : ℝ => ((t,x,y),s)) from
      measurable_const.prodMk measurable_id)

omit [NormedAlgebra ℝ B] in
lemma product_section (K L : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (hL : MeasurableKernel L) (t s x y) :
    StronglyMeasurable (fun z => K (t-s) x z * L s z y) := by
  exact (hK.comp_measurable (measurable_const.prodMk
    (measurable_const.prodMk measurable_id))).mul
    (hL.comp_measurable (measurable_const.prodMk (measurable_id.prodMk measurable_const)))

variable [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]

omit [BorelSpace X] [SecondCountableTopology X] in
lemma convolution_sup (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x y : X) :
    IntegrableOn (fun s => spatial μ K L t s x y) (Ioo 0 t) ∧
    weight N t x y*‖convolution μ K L t x y‖ ≤ 4*A*C/t := by
  have ha (s : ℝ) (hs : s ∈ Ioo 0 t) : t-s ∈ Ioc 0 T :=
    ⟨sub_pos.mpr hs.2, (sub_le_self _ hs.1.le).trans ht.2⟩
  have hb (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
  exact time_convolution_bound μ N ht.1 hK.nonneg hL.nonneg K L x y
    (fun s hs z => hK.sup _ (ha s hs) x z)
    (fun s hs z => hL.sup _ (hb s hs) z y)
    (fun s hs => hK.row_int _ (ha s hs) x)
    (fun s hs => hL.col_int _ (hb s hs) y)
    (fun s hs => hK.row _ (ha s hs) x)
    (fun s hs => hL.col _ (hb s hs) y)
    (fun s _ => (product_section K L hK.measurable hL.measurable t s x y).aestronglyMeasurable)
    (spatial_section μ K L hK.measurable hL.measurable t x y).aestronglyMeasurable

omit [NormedAlgebra ℝ B] in
lemma weighted_section (N : ℕ) (K : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (t : ℝ) :
    StronglyMeasurable (fun p : X × X => weight N t p.1 p.2*‖K t p.1 p.2‖) := by
  have hw : Continuous (fun p : X × X => weight N t p.1 p.2) := by
    unfold weight
    fun_prop
  exact hw.stronglyMeasurable.mul (kernel_section K hK t).norm

lemma spatial_row (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t) (x : X) :
    Integrable (fun y => weight N t x y*‖spatial μ K L t s x y‖) μ ∧
    (∫ y, weight N t x y*‖spatial μ K L t s x y‖ ∂μ) ≤ A*C := by
  have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2, (sub_le_self _ hs.1.le).trans ht.2⟩
  have hb : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
  have hweight : StronglyMeasurable (fun zy : X × X => weight N ((t-s)+s) x zy.2) :=
    ((weight_continuous N ((t-s)+s) x).comp continuous_snd).stronglyMeasurable
  have hKm : StronglyMeasurable (fun zy : X × X => K (t-s) x zy.1) :=
    hK.measurable.comp_measurable (measurable_const.prodMk (measurable_const.prodMk measurable_fst))
  have hr := SchurKernel.convolution_row μ N ha.1 hb.1 (K (t-s)) (L s) x
    (hK.row_int _ ha x) (hK.row _ ha x) (weighted_section N L hL.measurable s)
    (hL.row_int _ hb) (hL.row _ hb) hL.nonneg
    (hweight.smul (hKm.mul (kernel_section L hL.measurable s)))
  simpa [spatial] using hr

lemma convolution_row (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : X) :
    Integrable (fun y => weight N t x y*‖convolution μ K L t x y‖) μ ∧
    (∫ y, weight N t x y*‖convolution μ K L t x y‖ ∂μ) ≤ t*A*C := by
  let H : ℝ → X → B := fun s y => weight N t x y • spatial μ K L t s x y
  have he (s : ℝ) (y : X) : ‖H s y‖ = weight N t x y*‖spatial μ K L t s x y‖ := by
    simp only [H, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le]
  have hm : StronglyMeasurable (Function.uncurry H) := by
    have hweight : StronglyMeasurable (fun p : ℝ × X => weight N t x p.2) :=
      ((weight_continuous N t x).comp continuous_snd).stronglyMeasurable
    have hsp := (spatial_measurable μ K L hK.measurable hL.measurable).comp_measurable
      (show Measurable (fun p : ℝ × X => ((t,x,p.2),p.1)) from by fun_prop)
    exact hweight.smul hsp
  have hi : ∀ᵐ s ∂volume.restrict (Ioo 0 t), Integrable (H s) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    apply (integrable_norm_iff (hm.comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mp
    change Integrable (fun y => ‖H s y‖) μ
    simpa only [he] using (spatial_row μ N K L hK hL ht hs x).1
  have hr : ∀ᵐ s ∂volume.restrict (Ioo 0 t), (∫ y, ‖H s y‖ ∂μ) ≤ A*C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simpa only [he] using (spatial_row μ N K L hK hL ht hs x).2
  have hh := SchurIntegration.integral_row_bound_ae (volume.restrict (Ioo 0 t)) μ
    (integrableOn_const (C := A*C) (hs := measure_Ioo_lt_top.ne)) H hm.aestronglyMeasurable hi hr
  have hei (y : X) : ‖∫ s in Ioo 0 t, H s y‖ = weight N t x y*‖convolution μ K L t x y‖ := by
    simp only [H, integral_smul, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le,
      convolution]
  refine ⟨?_, ?_⟩
  · simpa only [hei] using hh.2.1.norm
  · have hb := hh.2.2
    simp only [hei, integral_const, measureReal_restrict_apply_univ,
      Real.volume_real_Ioo_of_le ht.1.le, sub_zero, smul_eq_mul] at hb
    simpa only [mul_assoc] using hb

lemma spatial_col (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t) (y : X) :
    Integrable (fun x => weight N t x y*‖spatial μ K L t s x y‖) μ ∧
    (∫ x, weight N t x y*‖spatial μ K L t s x y‖ ∂μ) ≤ A*C := by
  have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2, (sub_le_self _ hs.1.le).trans ht.2⟩
  have hb : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
  let f : X → ℝ := fun z => weight N s z y*‖L s z y‖
  let g : X → X → ℝ := fun z x => weight N (t-s) x z*‖K (t-s) x z‖
  let H : X → X → B := fun z x => weight N t x y • (K (t-s) x z * L s z y)
  have hdom (z x : X) : ‖H z x‖ ≤ f z*g z x := by
    rw [show ‖H z x‖ = weight N t x y*‖K (t-s) x z * L s z y‖ by
      simp [H, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le]]
    have hw : weight N t x y ≤ weight N (t-s) x z*weight N s z y := by
      simpa using weight_submultiplicative N ha.1 hb.1 x z y
    calc
      _ ≤ (weight N (t-s) x z*weight N s z y)*(‖K (t-s) x z‖*‖L s z y‖) :=
        mul_le_mul hw (norm_mul_le _ _) (norm_nonneg _)
          (mul_nonneg (weight_pos N ha.1 x z).le (weight_pos N hb.1 z y).le)
      _ = _ := by dsimp [f,g] <;> ring
  have hg : StronglyMeasurable (Function.uncurry g) :=
    (weighted_section N K hK.measurable (t-s)).comp_measurable measurable_swap
  have hH : StronglyMeasurable (Function.uncurry H) := by
    have hw : Continuous (fun p : X × X => weight N t p.2 y) := by unfold weight; fun_prop
    have hk := (kernel_section K hK.measurable (t-s)).comp_measurable measurable_swap
    have hl : StronglyMeasurable (fun p : X × X => L s p.1 y) :=
      hL.measurable.comp_measurable (measurable_const.prodMk (measurable_fst.prodMk measurable_const))
    exact hw.stronglyMeasurable.smul (hk.mul hl)
  have hh := SchurIntegration.norm_integral_row μ μ (g := g) (hL.col_int _ hb y)
    (fun z => mul_nonneg (weight_pos N hb.1 z y).le (norm_nonneg _)) hg
    (fun z x => mul_nonneg (weight_pos N ha.1 x z).le (norm_nonneg _))
    (hK.col_int _ ha) (hK.col _ ha) H hH hdom
  have he (x : X) : ‖∫ z, H z x ∂μ‖ = weight N t x y*‖spatial μ K L t s x y‖ := by
    simp only [H, integral_smul, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le, spatial]
  refine ⟨?_, ?_⟩
  · simpa only [he] using hh.1.norm
  · have h := hh.2
    simp only [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hL.col _ hb y) hK.nonneg)

lemma convolution_col (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (y : X) :
    Integrable (fun x => weight N t x y*‖convolution μ K L t x y‖) μ ∧
    (∫ x, weight N t x y*‖convolution μ K L t x y‖ ∂μ) ≤ t*A*C := by
  let H : ℝ → X → B := fun s x => weight N t x y • spatial μ K L t s x y
  have he (s : ℝ) (x : X) : ‖H s x‖ = weight N t x y*‖spatial μ K L t s x y‖ := by
    simp only [H, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le]
  have hm : StronglyMeasurable (Function.uncurry H) := by
    have hw : Continuous (fun p : ℝ × X => weight N t p.2 y) := by unfold weight; fun_prop
    have hsp := (spatial_measurable μ K L hK.measurable hL.measurable).comp_measurable
      (show Measurable (fun p : ℝ × X => ((t,p.2,y),p.1)) from by fun_prop)
    exact hw.stronglyMeasurable.smul hsp
  have hi : ∀ᵐ s ∂volume.restrict (Ioo 0 t), Integrable (H s) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    apply (integrable_norm_iff (hm.comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mp
    change Integrable (fun x => ‖H s x‖) μ
    simpa only [he] using (spatial_col μ N K L hK hL ht hs y).1
  have hr : ∀ᵐ s ∂volume.restrict (Ioo 0 t), (∫ x, ‖H s x‖ ∂μ) ≤ A*C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simpa only [he] using (spatial_col μ N K L hK hL ht hs y).2
  have hh := SchurIntegration.integral_row_bound_ae (volume.restrict (Ioo 0 t)) μ
    (integrableOn_const (C := A*C) (hs := measure_Ioo_lt_top.ne)) H hm.aestronglyMeasurable hi hr
  have hei (x : X) : ‖∫ s in Ioo 0 t, H s x‖ = weight N t x y*‖convolution μ K L t x y‖ := by
    simp only [H, integral_smul, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le,
      convolution]
  refine ⟨?_, ?_⟩
  · simpa only [hei] using hh.2.1.norm
  · have hb := hh.2.2
    simp only [hei, integral_const, measureReal_restrict_apply_univ,
      Real.volume_real_Ioo_of_le ht.1.le, sub_zero, smul_eq_mul] at hb
    simpa only [mul_assoc] using hb

lemma convolution_heatBound (N : ℕ) {T A C : ℝ} (hT : 0 ≤ T)
    (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L) :
    HeatBound μ N T (4*T*A*C) (convolution μ K L) := by
  refine ⟨convolution_measurable μ K L hK.measurable hL.measurable,
    by have hA := hK.nonneg; have hC := hL.nonneg; positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x y
    apply (convolution_sup μ N K L hK hL ht x y).2.trans
    apply (div_le_div_iff₀ ht.1 (sq_pos_of_pos ht.1)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2)
      (mul_nonneg (mul_nonneg hK.nonneg hL.nonneg) ht.1.le)]
  · intro t ht x
    exact (convolution_row μ N K L hK hL ht x).1
  · intro t ht x
    apply (convolution_row μ N K L hK hL ht x).2.trans
    have ht' : t ≤ 4*T := by linarith [ht.2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht' hK.nonneg) hL.nonneg
  · intro t ht y
    exact (convolution_col μ N K L hK hL ht y).1
  · intro t ht y
    apply (convolution_col μ N K L hK hL ht y).2.trans
    have ht' : t ≤ 4*T := by linarith [ht.2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht' hK.nonneg) hL.nonneg

end TamingCompatibility.GeometricHilbert.VolterraKernel

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
lemma leadingMatrix_smooth (hs : IsSmooth α) (p : A.centers) {t : ℝ} (htp : 0 < t) (z : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => leadingMatrix J α ht A D p v.1 v.2) (t,z) :=
  coordinateMatrix_joint_smooth J α ht A D hD hs p _
    (fun t => (subset_tsupport _).trans (partitionLeading_tsupport J α ht A D hD p t))
    (partitionLeading_smooth J α ht A D hD hs p htp z)

include hD in
lemma residualMatrix_smooth (hs : IsSmooth α) (p : A.centers) {t : ℝ} (htp : 0 < t) (z : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => residualMatrix J α ht A D p v.1 v.2) (t,z) :=
  coordinateMatrix_joint_smooth J α ht A D hD hs p _
    (fun t => (subset_tsupport _).trans (partitionResidual_tsupport J α ht A D hD p t))
    (partitionResidual_smooth J α ht A D hD hs p htp z)

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

omit [CompactSpace X] in
lemma assemble_continuousOn
    (K : A.centers → ℝ → Space × Space → FrameSpace A →L[ℝ] FrameSpace A)
    (hsupp : ∀ p t, Function.support (K p t) ⊆ (D p).physicalCompact)
    (hcont : ∀ p t, 0 < t → ∀ z, ContinuousAt (fun v : ℝ × (Space × Space) => K p v.1 v.2) (t,z)) :
    ContinuousOn (fun v : ℝ × (X × X) => assemble A K v.1 v.2.1 v.2.2) {v | 0 < v.1} := by
  intro v hv
  apply ContinuousAt.continuousWithinAt
  have hc : ContinuousAt (fun w : ℝ × (X × X) =>
      ∑ p : A.centers, ManifoldKernelExtension.push p.val (K p w.1) (w.2.2,w.2.1)) v := by
    apply tendsto_finsetSum
    intro p _
    have hh := ManifoldKernelExtension.push_joint_continuousAt p.val (K p) (D p).physicalCompact
      (D p).physicalCompact_compact (physicalCompact_target J α ht A D p) (hsupp p) v.1
      (hcont p v.1 hv) (v.2.2,v.2.1)
    exact hh.comp (f := fun w : ℝ × (X × X) => (w.1,(w.2.2,w.2.1)))
      (continuousAt_fst.prodMk (continuousAt_snd.snd.prodMk continuousAt_snd.fst))
  apply hc.congr_of_eventuallyEq
  have hn : {w : ℝ × (X × X) | 0 < w.1} ∈ 𝓝 v :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hv
  filter_upwards [hn] with w hw
  exact ite_eq_left hw

include hD in
lemma globalLeading_continuousOn (hs : IsSmooth α) :
    ContinuousOn (fun v : ℝ × (X × X) => globalLeading J α ht A D v.1 v.2.1 v.2.2) {v | 0 < v.1} :=
  assemble_continuousOn J α ht A D _
    (fun p t => (coordinateMatrix_support J α ht A D p _).trans
      ((subset_tsupport _).trans (partitionLeading_tsupport J α ht A D hD p t)))
    (fun p _ htpos z => (leadingMatrix_smooth J α ht A D hD hs p htpos z).continuousAt)

include hD in
lemma globalResidual_continuousOn (hs : IsSmooth α) :
    ContinuousOn (fun v : ℝ × (X × X) => globalResidual J α ht A D v.1 v.2.1 v.2.2) {v | 0 < v.1} :=
  assemble_continuousOn J α ht A D _
    (fun p t => (coordinateMatrix_support J α ht A D p _).trans
      ((subset_tsupport _).trans (partitionResidual_tsupport J α ht A D hD p t)))
    (fun p _ htpos z => (residualMatrix_smooth J α ht A D hD hs p htpos z).continuousAt)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalKernelContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] Classical.propDecidable

include hs hE in
lemma globalLeading_continuousAt {t : ℝ} (htp : 0 < t) (x y : X) :
    ContinuousAt (fun v : ℝ × (X × X) => globalLeading J α ht A E v.1 v.2.1 v.2.2) (t,(x,y)) :=
  (globalLeading_continuousOn J α ht A E hE hs).continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds htp)

include hs hE in
lemma globalResidual_continuousAt {t : ℝ} (htp : 0 < t) (x y : X) :
    ContinuousAt (fun v : ℝ × (X × X) => globalResidual J α ht A E v.1 v.2.1 v.2.2) (t,(x,y)) :=
  (globalResidual_continuousOn J α ht A E hE hs).continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds htp)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelSeriesCore
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelSeries
open _root_.MeasureTheory Set Filter VolterraKernel VolterraBounds
open scoped Topology
variable {X B : Type*} [MeasurableSpace X]
  [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
variable (μ : Measure X) [SFinite μ]

lemma integrable_tsum_bound (F : ℕ → X → B) (a : ℕ → ℝ)
    (ha : Summable a) (ha0 : ∀ n, 0 ≤ a n)
    (hF : ∀ n, StronglyMeasurable (F n))
    (hFi : ∀ n, Integrable (F n) μ)
    (hFa : ∀ n, (∫ x, ‖F n x‖ ∂μ) ≤ a n)
    (hFs : ∀ x, Summable (fun n => ‖F n x‖)) :
    Integrable (fun x => ∑' n, F n x) μ ∧
    (∫ x, ‖∑' n, F n x‖ ∂μ) ≤ ∑' n, a n := by
  have hai : Integrable a Measure.count := integrable_count_iff.mpr (by
    simpa only [Real.norm_of_nonneg (ha0 _)] using ha)
  have hm : StronglyMeasurable (Function.uncurry F) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun _ => continuous_of_discreteTopology) hF
  have hb := SchurIntegration.integral_row_bound Measure.count μ hai F hm hFi hFa
  have he (x : X) : (∫ n, F n x ∂Measure.count) = ∑' n, F n x := by
    rw [integral_countable (integrable_count_iff.mpr (hFs x))]
    simp
  have hea : (∫ n, a n ∂Measure.count) = ∑' n, a n := by
    rw [integral_countable hai]
    simp
  simpa only [he, hea] using hb.2

omit [NormedAlgebra ℝ B] [CompleteSpace B] in

lemma tsum_stronglyMeasurable (F : ℕ → X → B)
    (hF : ∀ n, StronglyMeasurable (F n)) (hs : ∀ x, Summable (fun n => F n x)) :
    StronglyMeasurable (fun x => ∑' n, F n x) := by
  refine stronglyMeasurable_of_tendsto (f := fun n : ℕ => fun x => ∑ i ∈ Finset.range n, F i x)
    atTop (fun n => ?_) ?_
  · exact Finset.stronglyMeasurable_fun_sum (Finset.range n) (fun i _ => hF i)
  · exact tendsto_pi_nhds.mpr (fun x => (hs x).hasSum.tendsto_sum_nat)

variable [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]

omit [NormedAlgebra ℝ B] [CompleteSpace B] [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma clip_measurable (T : ℝ) (K : Kernel (X := X) (B := B)) (hK : MeasurableKernel K) :
    MeasurableKernel (clip T K) := by
  exact hK.piecewise (measurableSet_Ioc.preimage measurable_fst) stronglyMeasurable_const

omit [SFinite μ] [CompleteSpace B] [NormedAlgebra ℝ B] [BorelSpace X] [SecondCountableTopology X] in
lemma heatBound_clip (N : ℕ) {T A : ℝ} (K : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) : HeatBound μ N T A (clip T K) := by
  refine ⟨clip_measurable T K hK.measurable, hK.nonneg, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x y; simpa only [clip_of_mem T K ht] using hK.sup t ht x y
  · intro t ht x; simpa only [clip_of_mem T K ht] using hK.row_int t ht x
  · intro t ht x; simpa only [clip_of_mem T K ht] using hK.row t ht x
  · intro t ht y; simpa only [clip_of_mem T K ht] using hK.col_int t ht y
  · intro t ht y; simpa only [clip_of_mem T K ht] using hK.col t ht y

omit [NormedAlgebra ℝ B] [CompleteSpace B] [SFinite μ] [BorelSpace X] [SecondCountableTopology X] in
lemma heatBound_neg (N : ℕ) {T A : ℝ} (K : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) : HeatBound μ N T A (fun t x y => - K t x y) := by
  exact ⟨hK.measurable.neg, hK.nonneg, by simpa only [norm_neg] using hK.sup,
    by simpa only [norm_neg] using hK.row_int, by simpa only [norm_neg] using hK.row,
    by simpa only [norm_neg] using hK.col_int, by simpa only [norm_neg] using hK.col⟩

omit [CompleteSpace B] in
lemma term_heatBound (N : ℕ) {T A : ℝ} (hT : 0 ≤ T)
    (R : Kernel (X := X) (B := B)) (hR : HeatBound μ N T A R) (n : ℕ) :
    HeatBound μ N T (A*(4*T*A)^n) (term μ T R n) := by
  induction n with
  | zero => simpa only [term, pow_zero, mul_one] using
      heatBound_clip μ N _ (heatBound_neg μ N R hR)
  | succ n ih =>
    have h := heatBound_clip μ N _ (heatBound_neg μ N _
      (convolution_heatBound μ N hT R (term μ T R n) hR ih))
    convert h using 1
    · rw [pow_succ]; ring
    · rfl

omit [CompleteSpace B] in
lemma term_norm_summable (N : ℕ) {T A : ℝ} (hT : 0 ≤ T)
    (R : Kernel (X := X) (B := B)) (hR : HeatBound μ N T A R)
    (hq : 4*T*A < 1) (t : ℝ) (x y : X) :
    Summable (fun n => ‖term μ T R n t x y‖) := by
  by_cases ht : t ∈ Ioc 0 T
  · have hq0 : 0 ≤ 4*T*A := by have hA := hR.nonneg; positivity
    have hs : Summable (fun n : ℕ => (A/t^2)*(4*T*A)^n) :=
      (summable_geometric_of_norm_lt_one (x := (4*T*A : ℝ)) (by rwa [Real.norm_of_nonneg hq0])).mul_left _
    apply hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    have hn := (term_heatBound μ N hT R hR n).sup t ht x y
    calc
      _ ≤ weight N t x y*‖term μ T R n t x y‖ :=
        le_mul_of_one_le_left (norm_nonneg _) (weight_one_le N ht.1 x y)
      _ ≤ A*(4*T*A)^n/t^2 := hn
      _ = _ := by ring
  · simp only [term_outside μ T R _ ht, norm_zero, summable_zero]

omit [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma weighted_tsum_L1 (w : X → ℝ) (hw : StronglyMeasurable w) (hw0 : ∀ x, 0 ≤ w x)
    (F : ℕ → X → B) (a : ℕ → ℝ) (ha : Summable a) (ha0 : ∀ n, 0 ≤ a n)
    (hF : ∀ n, StronglyMeasurable (F n))
    (hFi : ∀ n, Integrable (fun x => w x*‖F n x‖) μ)
    (hFa : ∀ n, (∫ x, w x*‖F n x‖ ∂μ) ≤ a n)
    (hFs : ∀ x, Summable (fun n => ‖F n x‖)) :
    Integrable (fun x => w x*‖∑' n, F n x‖) μ ∧
    (∫ x, w x*‖∑' n, F n x‖ ∂μ) ≤ ∑' n, a n := by
  have hn (n : ℕ) (x : X) : ‖w x • F n x‖ = w x*‖F n x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (hw0 x)]
  have hs (x : X) : Summable (fun n => ‖w x • F n x‖) := by
    simpa only [hn] using (hFs x).mul_left (w x)
  have hi (n : ℕ) : Integrable (fun x => w x • F n x) μ :=
    (integrable_norm_iff (hw.smul (hF n)).aestronglyMeasurable).mp (by
      change Integrable (fun x => ‖w x • F n x‖) μ
      simpa only [hn] using hFi n)
  have hb := integrable_tsum_bound μ (fun n x => w x • F n x) a ha ha0
    (fun n => hw.smul (hF n)) hi (by simpa only [hn] using hFa) hs
  have he (x : X) : (∑' n, w x • F n x) = w x • ∑' n, F n x :=
    (hFs x).of_norm.tsum_const_smul _
  have hn' (x : X) : ‖w x • ∑' n, F n x‖ = w x*‖∑' n, F n x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (hw0 x)]
  exact ⟨by simpa only [he, hn'] using hb.1.norm,
    by simpa only [he, hn'] using hb.2⟩

omit [SecondCountableTopology X] in
lemma heatBound_tsum (N : ℕ) {T : ℝ} (K : ℕ → Kernel (X := X) (B := B))
    (a : ℕ → ℝ) (ha : Summable a) (hK : ∀ n, HeatBound μ N T (a n) (K n))
    (hKs : ∀ t x y, Summable (fun n => ‖K n t x y‖)) :
    HeatBound μ N T (∑' n, a n) (fun t x y => ∑' n, K n t x y) := by
  have hm : MeasurableKernel (fun t x y => ∑' n, K n t x y) :=
    tsum_stronglyMeasurable (fun n (p : ℝ × X × X) => K n p.1 p.2.1 p.2.2)
      (fun n => (hK n).measurable) (fun p => (hKs _ _ _).of_norm)
  have hr (t : ℝ) (ht : t ∈ Ioc 0 T) (x : X) :
      Integrable (fun y => weight N t x y*‖∑' n, K n t x y‖) μ ∧
      (∫ y, weight N t x y*‖∑' n, K n t x y‖ ∂μ) ≤ ∑' n, a n := by
    exact weighted_tsum_L1 μ _ (weight_continuous N t x).stronglyMeasurable
      (fun y => (weight_pos N ht.1 x y).le) (fun n y => K n t x y) a ha
      (fun n => (hK n).nonneg)
      (fun n => (kernel_section (K n) (hK n).measurable t).comp_measurable
        (measurable_const.prodMk measurable_id))
      (fun n => (hK n).row_int t ht x) (fun n => (hK n).row t ht x) (hKs t x)
  have hc (t : ℝ) (ht : t ∈ Ioc 0 T) (y : X) :
      Integrable (fun x => weight N t x y*‖∑' n, K n t x y‖) μ ∧
      (∫ x, weight N t x y*‖∑' n, K n t x y‖ ∂μ) ≤ ∑' n, a n := by
    have hw : StronglyMeasurable (fun x => weight N t x y) := by
      simpa only [weight_symm N t] using (weight_continuous N t y).stronglyMeasurable
    exact weighted_tsum_L1 μ _ hw
      (fun x => (weight_pos N ht.1 x y).le) (fun n x => K n t x y) a ha
      (fun n => (hK n).nonneg)
      (fun n => (kernel_section (K n) (hK n).measurable t).comp_measurable
        (measurable_id.prodMk measurable_const))
      (fun n => (hK n).col_int t ht y) (fun n => (hK n).col t ht y) (fun x => hKs t x y)
  refine ⟨hm, tsum_nonneg (fun n => (hK n).nonneg), ?_,
    fun t ht x => (hr t ht x).1, fun t ht x => (hr t ht x).2,
    fun t ht y => (hc t ht y).1, fun t ht y => (hc t ht y).2⟩
  intro t ht x y
  have hn (n : ℕ) : ‖weight N t x y • K n t x y‖ ≤ a n/t^2 := by
    simpa only [norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le] using
      (hK n).sup t ht x y
  have hh := tsum_of_norm_bounded (ha.div_const (t^2)).hasSum hn
  rw [(hKs t x y).of_norm.tsum_const_smul, norm_smul,
    Real.norm_of_nonneg (weight_pos N ht.1 x y).le, tsum_div_const] at hh
  exact hh

lemma correction_heatBound (N : ℕ) {T A : ℝ} (hT : 0 ≤ T)
    (R : Kernel (X := X) (B := B)) (hR : HeatBound μ N T A R) (hq : 4*T*A < 1) :
    HeatBound μ N T (A/(1-4*T*A)) (correction μ T R) := by
  have hq0 : 0 ≤ 4*T*A := by have hA := hR.nonneg; positivity
  have hqabs : ‖(4*T*A : ℝ)‖ < 1 := by rwa [Real.norm_of_nonneg hq0]
  have ha : Summable (fun n : ℕ => A*(4*T*A)^n) :=
    (summable_geometric_of_norm_lt_one hqabs).mul_left A
  have h := heatBound_tsum μ N (term μ T R) _ ha
    (term_heatBound μ N hT R hR) (term_norm_summable μ N hT R hR hq)
  have he : (∑' n : ℕ, A*(4*T*A)^n) = A/(1-4*T*A) := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hqabs, div_eq_mul_inv]
  change HeatBound μ N T (A/(1-4*T*A)) (fun t x y => ∑' n, term μ T R n t x y)
  rw [he] at h
  exact h

omit [NormedAlgebra ℝ B] [CompleteSpace B] [SFinite μ]
  [BorelSpace X] [SecondCountableTopology X] in
lemma heatBound_norm (N : ℕ) {T A : ℝ} (K : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) : HeatBound μ N T A (fun t x y => ‖K t x y‖) := by
  exact ⟨hK.measurable.norm, hK.nonneg, by simpa only [norm_norm] using hK.sup,
    by simpa only [norm_norm] using hK.row_int, by simpa only [norm_norm] using hK.row,
    by simpa only [norm_norm] using hK.col_int, by simpa only [norm_norm] using hK.col⟩

omit [CompleteSpace B] [SFinite μ] [BorelSpace X] [SecondCountableTopology X] in
lemma spatial_product_norm_bound (N : ℕ) {T A C : ℝ}
    (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t) (x y : X) :
    Integrable (fun z => K (t-s) x z * L s z y) μ ∧
    (∫ z, ‖K (t-s) x z * L s z y‖ ∂μ) ≤ 4*A*C/t^2 := by
  have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2, (sub_le_self _ hs.1.le).trans ht.2⟩
  have hb : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
  have hi := time_integrand_bound μ N ht.1 hs.1 hs.2 hK.nonneg hL.nonneg K L x y
    (hK.sup _ ha x) (fun z => hL.sup _ hb z y) (hK.row_int _ ha x)
    (hL.col_int _ hb y) (hK.row _ ha x) (hL.col _ hb y)
    (product_section K L hK.measurable hL.measurable t s x y).aestronglyMeasurable
  have hKn := heatBound_norm μ N K hK
  have hLn := heatBound_norm μ N L hL
  have hn := time_integrand_bound μ N ht.1 hs.1 hs.2 hK.nonneg hL.nonneg
    (fun t x y => ‖K t x y‖) (fun t x y => ‖L t x y‖) x y
    (hKn.sup _ ha x) (fun z => hLn.sup _ hb z y) (hKn.row_int _ ha x)
    (hLn.col_int _ hb y) (hKn.row _ ha x) (hLn.col _ hb y)
    (product_section _ _ hKn.measurable hLn.measurable t s x y).aestronglyMeasurable
  refine ⟨hi.1, ?_⟩
  calc
    _ ≤ ∫ z, ‖K (t-s) x z‖ * ‖L s z y‖ ∂μ := integral_mono hi.1.norm hn.1
      (fun z => norm_mul_le _ _)
    _ ≤ weight N t x y * (∫ z, ‖K (t-s) x z‖ * ‖L s z y‖ ∂μ) :=
      le_mul_of_one_le_left (integral_nonneg (fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        (weight_one_le N ht.1 x y)
    _ ≤ 4*A*C/t^2 := by
      simpa only [Real.norm_of_nonneg (integral_nonneg
        (fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)))] using hn.2

omit [SFinite μ] [BorelSpace X] [SecondCountableTopology X] in
lemma spatial_tsum_right (N : ℕ) {T A : ℝ}
    (K : Kernel (X := X) (B := B)) (L : ℕ → Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (a : ℕ → ℝ) (ha : Summable a)
    (hL : ∀ n, HeatBound μ N T (a n) (L n))
    (hLs : ∀ t x y, Summable (fun n => ‖L n t x y‖))
    {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t) (x y : X) :
    spatial μ K (fun t x y => ∑' n, L n t x y) t s x y =
      ∑' n, spatial μ K (L n) t s x y := by
  have hi (n : ℕ) := spatial_product_norm_bound μ N K (L n) hK (hL n) ht hs x y
  have ha' : Summable (fun n => 4*A*a n/t^2) := by
    convert ha.mul_left (4*A/t^2) using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    ring
  have hsum : Summable (fun n => ∫ z, ‖K (t-s) x z * L n s z y‖ ∂μ) :=
    ha'.of_nonneg_of_le (fun n => integral_nonneg (fun z => norm_nonneg _)) (fun n => (hi n).2)
  unfold spatial
  rw [integral_tsum_of_summable_integral_norm (fun n => (hi n).1) hsum]
  apply integral_congr_ae
  filter_upwards [] with z
  exact ((hLs s z y).of_norm.tsum_mul_left (K (t-s) x z)).symm

omit [BorelSpace X] [SecondCountableTopology X] in
lemma convolution_tsum_right (N : ℕ) {T A : ℝ}
    (K : Kernel (X := X) (B := B)) (L : ℕ → Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (a : ℕ → ℝ) (ha : Summable a)
    (hL : ∀ n, HeatBound μ N T (a n) (L n))
    (hLs : ∀ t x y, Summable (fun n => ‖L n t x y‖))
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x y : X) :
    convolution μ K (fun t x y => ∑' n, L n t x y) t x y =
      ∑' n, convolution μ K (L n) t x y := by
  have hi (n : ℕ) := (convolution_sup μ N K (L n) hK (hL n) ht x y).1
  have hb (n : ℕ) : (∫ s in Ioo 0 t, ‖spatial μ K (L n) t s x y‖) ≤ 4*A*a n/t := by
    have hc : IntegrableOn (fun _ : ℝ => 4*A*a n/t^2) (Ioo 0 t) :=
      integrableOn_const (hs := measure_Ioo_lt_top.ne)
    have hp : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ‖spatial μ K (L n) t s x y‖ ≤ 4*A*a n/t^2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (norm_integral_le_integral_norm _).trans
        (spatial_product_norm_bound μ N K (L n) hK (hL n) ht hs x y).2
    apply (integral_mono_ae (hi n).norm hc hp).trans_eq
    simp only [integral_const, measureReal_restrict_apply_univ,
      Real.volume_real_Ioo_of_le ht.1.le, sub_zero, smul_eq_mul]
    field_simp
  have ha' : Summable (fun n => 4*A*a n/t) := by
    convert ha.mul_left (4*A/t) using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    ring
  have hsum : Summable (fun n => ∫ s in Ioo 0 t, ‖spatial μ K (L n) t s x y‖) :=
    ha'.of_nonneg_of_le (fun n => integral_nonneg (fun s => norm_nonneg _)) hb
  unfold VolterraKernel.convolution
  rw [integral_tsum_of_summable_integral_norm hi hsum]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact spatial_tsum_right μ N K L hK a ha hL hLs ht hs x y

lemma correction_equation (N : ℕ) {T A : ℝ} (hT : 0 ≤ T)
    (R : Kernel (X := X) (B := B)) (hR : HeatBound μ N T A R) (hq : 4*T*A < 1)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x y : X) :
    R t x y + correction μ T R t x y + convolution μ R (correction μ T R) t x y = 0 := by
  have hq0 : 0 ≤ 4*T*A := by have hA := hR.nonneg; positivity
  have ha : Summable (fun n : ℕ => A*(4*T*A)^n) :=
    (summable_geometric_of_norm_lt_one (by rwa [Real.norm_of_nonneg hq0] : ‖(4*T*A:ℝ)‖ < 1)).mul_left A
  have hs := term_norm_summable μ N hT R hR hq t x y
  have he := convolution_tsum_right μ N R (term μ T R) hR _ ha
    (term_heatBound μ N hT R hR) (term_norm_summable μ N hT R hR hq) ht x y
  have h0 : term μ T R 0 t x y = -R t x y := by simp only [term, clip_of_mem T _ ht]
  have hsucc (n : ℕ) : term μ T R (n+1) t x y = - convolution μ R (term μ T R n) t x y := by
    simp only [term, clip_of_mem T _ ht]
  have hh := hs.of_norm.tsum_eq_zero_add
  simp only [h0, hsucc, tsum_neg] at hh
  change (∑' n, term μ T R n t x y) = _ at hh
  change R t x y + (∑' n, term μ T R n t x y) +
    convolution μ R (fun t x y => ∑' n, term μ T R n t x y) t x y = 0
  change convolution μ R (fun t x y => ∑' n, term μ T R n t x y) t x y = _ at he
  rw [he, hh]
  abel

end TamingCompatibility.GeometricHilbert.KernelSeries

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open _root_.MeasureTheory Set
variable {X B : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [NormedRing B]
  (μ : Measure X)
lemma HeatBound.mono_time {N : ℕ} {S T A : ℝ} {K : Kernel (X := X) (B := B)}
    (h : HeatBound μ N T A K) (hST : S ≤ T) : HeatBound μ N S A K := by
  have hsub : Ioc 0 S ⊆ Ioc 0 T := Ioc_subset_Ioc_right hST
  exact ⟨h.measurable,h.nonneg,fun t ht => h.sup t (hsub ht),
    fun t ht => h.row_int t (hsub ht),fun t ht => h.row t (hsub ht),
    fun t ht => h.col_int t (hsub ht),fun t ht => h.col t (hsub ht)⟩
end TamingCompatibility.GeometricHilbert.VolterraKernel

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open _root_.MeasureTheory Set VolterraBounds
variable {X B : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [NormedRing B]
  (μ : Measure X)

lemma HeatBound.weight_zero {N : ℕ} {T A : ℝ} {K : Kernel (X := X) (B := B)}
    (h : HeatBound μ N T A K) : HeatBound μ 0 T A K := by
  have hb (t : ℝ) (ht : t ∈ Ioc 0 T) (x y : X) :
      ‖K t x y‖ ≤ weight N t x y*‖K t x y‖ := by
    exact le_mul_of_one_le_left (norm_nonneg _) (weight_one_le N ht.1 x y)
  have hr (t : ℝ) (ht : t ∈ Ioc 0 T) (x : X) :
      Integrable (fun y => ‖K t x y‖) μ := by
    apply (h.row_int t ht x).mono' (((kernel_section K h.measurable t).comp_measurable
      (measurable_const.prodMk measurable_id)).norm.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun y => by simpa using hb t ht x y
  have hc (t : ℝ) (ht : t ∈ Ioc 0 T) (y : X) :
      Integrable (fun x => ‖K t x y‖) μ := by
    apply (h.col_int t ht y).mono' (((kernel_section K h.measurable t).comp_measurable
      (measurable_id.prodMk measurable_const)).norm.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by simpa using hb t ht x y
  refine ⟨h.measurable,h.nonneg,?_,?_,?_,?_,?_⟩
  · intro t ht x y
    simpa only [weight,pow_zero,one_mul] using (hb t ht x y).trans (h.sup t ht x y)
  · intro t ht x
    simpa only [weight,pow_zero,one_mul] using hr t ht x
  · intro t ht x
    simpa only [weight,pow_zero,one_mul] using
      (integral_mono (hr t ht x) (h.row_int t ht x) (fun y => hb t ht x y)).trans (h.row t ht x)
  · intro t ht y
    simpa only [weight,pow_zero,one_mul] using hc t ht y
  · intro t ht y
    simpa only [weight,pow_zero,one_mul] using
      (integral_mono (hc t ht y) (h.col_int t ht y) (fun x => hb t ht x y)).trans (h.col t ht y)

end TamingCompatibility.GeometricHilbert.VolterraKernel

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePointKernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open _root_.MeasureTheory Set Filter VolterraBounds
variable {X B : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
  [BorelSpace X] [SecondCountableTopology X]
  [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable (K L : Kernel (X := X) (B := B)) {T A C : ℝ}
  (hK : HeatBound μ 0 T A K) (hL : HeatBound μ 0 T C L)
include hK hL

omit [SecondCountableTopology X] [CompleteSpace B] [BorelSpace X] in
lemma spatial_continuous {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t)
    (hKc : Continuous (fun p : X × X => K (t-s) p.1 p.2))
    (hLc : Continuous (fun p : X × X => L s p.1 p.2)) :
    Continuous (fun p : X × X => spatial μ K L t s p.1 p.2) := by
  have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2,(sub_le_self _ hs.1.le).trans ht.2⟩
  have hb : s ∈ Ioc 0 T := ⟨hs.1,hs.2.le.trans ht.2⟩
  change Continuous (fun p : X × X => ∫ z, K (t-s) p.1 z * L s z p.2 ∂μ)
  apply continuous_of_dominated
    (fun p : X × X => (product_section K L hK.measurable hL.measurable t s p.1 p.2).aestronglyMeasurable)
    (bound := fun _ => (A/(t-s)^2)*(C/s^2))
  · intro p
    filter_upwards [] with z
    have hk := hK.sup _ ha p.1 z
    have hl := hL.sup _ hb z p.2
    simp only [weight,pow_zero,one_mul] at hk hl
    exact (norm_mul_le _ _).trans (mul_le_mul hk hl (norm_nonneg _) (by have := hK.nonneg; positivity))
  · exact integrable_const _
  · filter_upwards [] with z
    exact (hKc.comp (continuous_fst.prodMk continuous_const)).mul
      (hLc.comp (continuous_const.prodMk continuous_snd))

omit [SecondCountableTopology X] [CompleteSpace B] [BorelSpace X] in
lemma convolution_continuous {t : ℝ} (ht : t ∈ Ioc 0 T)
    (hKc : ∀ u ∈ Ioc 0 T, Continuous (fun p : X × X => K u p.1 p.2))
    (hLc : ∀ u ∈ Ioc 0 T, Continuous (fun p : X × X => L u p.1 p.2)) :
    Continuous (fun p : X × X => convolution μ K L t p.1 p.2) := by
  have ha (s : ℝ) (hs : s ∈ Ioo 0 t) : t-s ∈ Ioc 0 T :=
    ⟨sub_pos.mpr hs.2,(sub_le_self _ hs.1.le).trans ht.2⟩
  have hb (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Ioc 0 T := ⟨hs.1,hs.2.le.trans ht.2⟩
  change Continuous (fun p : X × X => ∫ s in Ioo 0 t, spatial μ K L t s p.1 p.2)
  apply continuous_of_dominated
    (fun p : X × X => (spatial_section μ K L hK.measurable hL.measurable t p.1 p.2).aestronglyMeasurable)
    (bound := fun _ => 4*A*C/t^2)
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have h := time_integrand_bound μ 0 ht.1 hs.1 hs.2 hK.nonneg hL.nonneg K L p.1 p.2
      (hK.sup _ (ha s hs) p.1) (fun z => hL.sup _ (hb s hs) z p.2)
      (hK.row_int _ (ha s hs) p.1) (hL.col_int _ (hb s hs) p.2)
      (hK.row _ (ha s hs) p.1) (hL.col _ (hb s hs) p.2)
      (product_section K L hK.measurable hL.measurable t s p.1 p.2).aestronglyMeasurable
    simpa only [weight,pow_zero,one_mul,spatial] using h.2
  · exact integrableOn_const (by simp)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact spatial_continuous μ K L hK hL ht hs (hKc _ (ha s hs)) (hLc _ (hb s hs))

end TamingCompatibility.GeometricHilbert.VolterraKernel

namespace TamingCompatibility.GeometricHilbert.KernelSeries
open _root_.MeasureTheory Set Filter VolterraKernel VolterraBounds
variable {X B : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
  [BorelSpace X] [SecondCountableTopology X]
  [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable (R : Kernel (X := X) (B := B)) {T A : ℝ} (hT : 0 ≤ T)
  (hR : HeatBound μ 0 T A R)
  (hRc : ∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => R t p.1 p.2))
include hT hR hRc

omit [CompleteSpace B] in
lemma term_continuous (n : ℕ) :
    ∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => term μ T R n t p.1 p.2) := by
  induction n with
  | zero =>
    intro t ht
    apply (continuous_neg.comp (hRc t ht)).congr
    intro p
    simp only [term,clip_of_mem T _ ht]
    rfl
  | succ n ih =>
    intro t ht
    apply (continuous_neg.comp
      (convolution_continuous μ R (term μ T R n) hR (term_heatBound μ 0 hT R hR n) ht hRc ih)).congr
    intro p
    simp only [term,clip_of_mem T _ ht]
    rfl

lemma correction_continuous (hq : 4*T*A < 1) {t : ℝ} (ht : t ∈ Ioc 0 T) :
    Continuous (fun p : X × X => correction μ T R t p.1 p.2) := by
  have hq0 : 0 ≤ 4*T*A := by have := hR.nonneg; positivity
  have hsum : Summable (fun n : ℕ => (A/t^2)*(4*T*A)^n) :=
    (summable_geometric_of_norm_lt_one (x := (4*T*A : ℝ)) (by rwa [Real.norm_of_nonneg hq0])).mul_left _
  apply continuous_tsum (fun n => term_continuous μ R hT hR hRc n t ht) hsum
  intro n p
  have h := (term_heatBound μ 0 hT R hR n).sup t ht p.1 p.2
  simp only [weight,pow_zero,one_mul] at h
  exact h.trans_eq (by ring)

end TamingCompatibility.GeometricHilbert.KernelSeries

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeContinuousParametrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma globalCorrection_continuous_bounds_oai (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
      (∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => globalCorrection J α ht A E T t p.1 p.2)) ∧
      (∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => globalError J α ht A E T t p.1 p.2)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x y, globalResidual J α ht A E t x y +
        globalCorrection J α ht A E T t x y +
        VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A E)
          (globalCorrection J α ht A E T) t x y = 0) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE n 1
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE n 1
  let T := (8*(R+1))⁻¹
  have hp : 0 < 8*(R+1) := by have := hR.nonneg; positivity
  have hT : 0 < T := inv_pos.mpr hp
  have hT1 : T ≤ 1 := (inv_le_one₀ hp).mpr (by linarith [hR.nonneg])
  have hq : 4*T*R < 1 := by
    dsimp [T]
    rw [show 4*(8*(R+1))⁻¹*R = (4*R)/(8*(R+1)) by ring]
    exact (div_lt_one hp).mpr (by linarith [hR.nonneg])
  have hR' := hR.mono_time _ hT1
  have hC : VolterraKernel.HeatBound (geometricVolume A J α) n T (R/(1-4*T*R))
      (globalCorrection J α ht A E T) :=
    KernelSeries.correction_heatBound (geometricVolume A J α) n hT.le _ hR' hq
  have hRc (t : ℝ) (htp : t ∈ Ioc 0 T) :
      Continuous (fun p : X × X => globalResidual J α ht A E t p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (globalResidual_continuousAt A J α hs ht E hE htp.1 p.1 p.2).comp
      (continuous_const.prodMk continuous_id).continuousAt
  have hCc (t : ℝ) (htp : t ∈ Ioc 0 T) :
      Continuous (fun p : X × X => globalCorrection J α ht A E T t p.1 p.2) :=
    KernelSeries.correction_continuous (geometricVolume A J α) _ hT.le (hR'.weight_zero _) hRc hq htp
  refine ⟨T,L,R/(1-4*T*R),hT,hT1,hL.mono_time _ hT1,hC,hCc,?_,?_⟩
  · intro t htp
    apply VolterraKernel.convolution_continuous (geometricVolume A J α)
      (globalLeading J α ht A E) (globalCorrection J α ht A E T)
      ((hL.mono_time _ hT1).weight_zero _) (hC.weight_zero _) htp ?_ hCc
    intro u hu
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (globalLeading_continuousAt A J α hs ht E hE hu.1 p.1 p.2).comp
      (continuous_const.prodMk continuous_id).continuousAt
  · intro t htp x y
    exact KernelSeries.correction_equation (geometricVolume A J α) n hT.le _ hR' hq htp x y

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCorrection_continuous_bounds_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCorrection_continuous_bounds_oai.{u_1}
