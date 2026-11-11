-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualPatch_joint_smooth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:31.065718+00:00
-- url     : https://prove2.me/submissions/2541458a-3534-4f6e-bb0e-77c3d7f4efbf

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc019
import Definitions.Def_OAIQ239Tc021
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_FlatHeat_heat_joint_contDiffAt
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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeResidualFamily
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
lemma residualPatch_joint_smooth_oai (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
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

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualPatch_joint_smooth_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualPatch_joint_smooth_oai.{u_1}
