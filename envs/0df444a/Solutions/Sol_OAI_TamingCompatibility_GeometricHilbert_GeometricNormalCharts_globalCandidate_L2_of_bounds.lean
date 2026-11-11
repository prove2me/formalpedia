-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_L2_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:19:10.528358+00:00
-- url     : https://prove2.me/submissions/b2ef5e3f-db79-4473-9733-8ca916074b97

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc023
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalLeading_heatBound
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_kernel_leading_pairing_initial
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledB_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalMetricCalculus_volumeDensity_pos

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

end MatrixFamilies
open UniformJets FirstJetGauge OrthogonalJets
open scoped ContDiff
variable {P V W ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

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
lemma normalFirst_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) (j : Fin 4) :
    ContDiffAt ℝ ∞ (normalFirst J α ht p D g B j) x :=
  firstMatrix_joint EuclideanEnergy.e (fun i y => pulledA J α ht p D g B y.1 i y.2)
    (fun y => pulledB J α ht p D g B y.1 y.2) (normalDensity g B)
    (pulledA_joint J α ht p D g B hg hB hx.1)
    (pulledB_joint J α hs ht p D g B hg hB hx.1)
    (normalDensity_smooth g B hg hB hx.2) (ne_of_gt (volumeDensity_pos hx.2)) j

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

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

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

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_r92b77a_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_r92b77a_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
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

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_r92b77a_2 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_r92b77a_2 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
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
lemma partitionLeading_tsupport (p : A.centers) (t : ℝ) :
    tsupport (partitionLeading J α ht A D p t) ⊆ (D p).physicalCompact := by
  apply KernelExtension.tsupport_push_subset _ _ _ (D p).normalCompact_compact (D p).normalCompact_source
  exact (leadingCoordinate_support J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    _ _ t).trans ((Set.prod_mono Set.Subset.rfl (subset_tsupport _)).trans
      (partition_patch_support J α ht A D hD p))

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

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalKernelForms
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
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
lemma framePairing_continuous (a : TwoForm X) (ha : IsSmooth a) :
    Continuous (framePairing A J α ht E a) := by
  unfold framePairing
  apply (squareMass_inv_smooth A).continuous.smul
  apply continuous_finsetSum
  intro p _
  apply continuous_finsetSum
  intro j _
  exact (GeometricAdjoint.pairing_two_smooth J α hs ht ha
    (globalFrame_smooth J α ht A E hE hs p j)).continuous.smul continuous_const

include hs hE in
lemma framePairing_bound (a : TwoForm X) (ha : IsSmooth a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖framePairing A J α ht E a x‖ ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (framePairing_continuous A J α hs ht E hE a ha).continuousOn
  exact ⟨max C 0,le_max_right _ _,fun x => (hC x (mem_univ x)).trans (le_max_left _ _)⟩

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

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelWeakAction
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
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
lemma kernel_pairing_integral_continuousOn
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : ∀ t, 0 < t → ∀ x y, ContinuousAt
      (fun z : ℝ × (X × X) => K z.1 z.2.1 z.2.2) (t,(x,y)))
    (v : X → FrameSpace A) (hv : Continuous v) (a : TwoForm X) (ha : IsSmooth a) :
    ContinuousOn (fun z : ℝ × X => ∫ x, framePairing A J α ht E a x
      (K z.1 x z.2 (v z.2)) ∂geometricVolume A J α) {z | 0 < z.1} := by
  let := geometricVolume_finite A J α hs ht
  apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
  · intro z hz
    have hk := (hK z.1.1 hz.1 z.2 z.1.2).comp
      (f := fun w : (ℝ × X) × X => (w.1.1,(w.2,w.1.2)))
      (continuousAt_fst.fst.prodMk (continuousAt_snd.prodMk continuousAt_fst.snd))
    have hφ : ContinuousAt (fun w : (ℝ × X) × X => framePairing A J α ht E a w.2) z :=
      (framePairing_continuous A J α hs ht E hE a ha).continuousAt.comp
      (f := fun w : (ℝ × X) × X => w.2) continuousAt_snd
    exact (hφ.clm_apply (hk.clm_apply (hv.continuousAt.comp continuousAt_fst.snd))).continuousWithinAt
  · intro _ x _ hx
    exact (hx (mem_univ x)).elim

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeInputInitial
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
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] [BorelSpace X] in
lemma kernel_pairing_integral_bound (a : TwoForm X) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ x, ‖framePairing A J α ht E a x‖ ≤ C)
    (K : X → FrameSpace A →L[ℝ] FrameSpace A) (v : FrameSpace A) {H : ℝ}
    (hKi : Integrable (fun x => ‖K x‖) (geometricVolume A J α))
    (hKb : (∫ x, ‖K x‖ ∂geometricVolume A J α) ≤ H) :
    ‖∫ x, framePairing A J α ht E a x (K x v) ∂geometricVolume A J α‖ ≤ C*‖v‖*H := by
  calc
    _ ≤ ∫ x, (C*‖v‖)*‖K x‖ ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le (hKi.const_mul _) (Filter.Eventually.of_forall _)
      intro x
      calc
        _ ≤ ‖framePairing A J α ht E a x‖*‖K x v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ C*(‖K x‖*‖v‖) := mul_le_mul (hφ x) (ContinuousLinearMap.le_opNorm _ _)
          (norm_nonneg _) hC
        _ = _ := by ring
    _ = (C*‖v‖)*(∫ x, ‖K x‖ ∂geometricVolume A J α) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hKb (mul_nonneg hC (norm_nonneg _))

attribute [local irreducible] framePairing globalLeading globalResidual

variable [ConnectedSpace X] [SecondCountableTopology X]
include hs hE in
lemma kernelWeakAction_leading_initial (v : X → FrameSpace A) (hv : Continuous v)
    (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (kernelWeakAction A J α ht E (globalLeading J α ht A E) v a)
      (𝓝[>] 0) (𝓝 (∫ y, framePairing A J α ht E a y (v y) ∂geometricVolume A J α)) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨C,hC,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  obtain ⟨V,hV⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  obtain ⟨H,hH⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  have hc := kernel_pairing_integral_continuousOn A J α hs ht E hE _
    (fun _ hp x y => globalLeading_continuousAt A J α hs ht E hE hp x y) v hv a ha
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [self_mem_nhdsWithin] with t htpos
    exact (continuousOn_univ.mp (hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => htpos))).aestronglyMeasurable
  · refine ⟨C*(max V 0)*H, ?_⟩
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with t htp ht1
    filter_upwards [] with y
    have hi := hH.col_int t ⟨htp,ht1.le⟩ y
    have hb := hH.col t ⟨htp,ht1.le⟩ y
    simp only [VolterraBounds.weight,pow_zero,one_mul] at hi hb
    exact (kernel_pairing_integral_bound A J α ht E a hC hφ _ (v y) hi hb).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        ((hV y (mem_univ y)).trans (le_max_left _ _)) hC) hH.nonneg)
  · filter_upwards [] with y
    exact kernel_leading_pairing_initial A J α hs ht E hE y (v y) a ha

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelTestTransform
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldLocalization ManifoldVolume _root_.MeasureTheory Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma pointNorm_sq (a : TwoForm X) (x : X) :
    pointNorm J α ht a x ^ 2 = GeometricAdjoint.pairing J α ht a a x :=
  Real.sq_sqrt (MetricForms.pairing_self_nonneg _ _)

lemma pointNorm_integral_sq (a : PreL2 A J α hs ht true) :
    (∫ x, pointNorm J α ht a.val x ^ 2 ∂geometricVolume A J α) = ‖a‖^2 := by
  simp_rw [pointNorm_sq]
  exact (preL2_norm_sq A J α hs ht true a).symm

lemma pointNorm_product_integral (a b : PreL2 A J α hs ht true) :
    (∫ x, pointNorm J α ht a.val x * pointNorm J α ht b.val x ∂geometricVolume A J α) ≤ ‖a‖*‖b‖ := by
  let := geometricVolume_finite A J α hs ht
  have ha := (pointNorm_continuous J α hs ht a.val a.property).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := geometricVolume A J α) (p := ENNReal.ofReal 2)
  have hb := (pointNorm_continuous J α hs ht b.val b.property).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := geometricVolume A J α) (p := ENNReal.ofReal 2)
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := geometricVolume A J α)
    (f := pointNorm J α ht a.val) (g := pointNorm J α ht b.val)
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff])
    (Eventually.of_forall (fun x => Real.sqrt_nonneg _))
    (Eventually.of_forall (fun x => Real.sqrt_nonneg _)) ha hb
  simpa only [Real.rpow_two,show (1:ℝ)/2 = 1/2 from rfl,← Real.sqrt_eq_rpow,
    pointNorm_integral_sq,Real.sqrt_sq_eq_abs,abs_norm] using hh

lemma bounded_pairing_integral_bound (a b : PreL2 A J α hs ht true)
    (f : X → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C) :
    ‖∫ x, f x * GeometricAdjoint.pairing J α ht a.val b.val x ∂geometricVolume A J α‖ ≤ C*‖a‖*‖b‖ := by
  let := geometricVolume_finite A J α hs ht
  have hi := (((pointNorm_continuous J α hs ht a.val a.property).mul
    (pointNorm_continuous J α hs ht b.val b.property)).integrable_of_hasCompactSupport
      (μ := geometricVolume A J α) (HasCompactSupport.of_compactSpace _)).const_mul C
  calc
    _ ≤ ∫ x, C*(pointNorm J α ht a.val x * pointNorm J α ht b.val x) ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [hf] with x hx
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul hx (MetricForms.abs_pairing_le_sqrt _ _ _) (abs_nonneg _) hC
    _ = C*(∫ x, pointNorm J α ht a.val x * pointNorm J α ht b.val x ∂geometricVolume A J α) := integral_const_mul _ _
    _ ≤ C*(‖a‖*‖b‖) := mul_le_mul_of_nonneg_left (pointNorm_product_integral A J α hs ht a b) hC
    _ = _ := by ring

end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeBoundedSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldLocalization ManifoldVolume _root_.MeasureTheory Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

local instance instNormedAddCommGroupTangentSpaceRealSpaceModel_r92b77a_1 (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance instNormedSpaceRealTangentSpaceSpaceModel_r92b77a_1 (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance instFiniteDimensionalRealTangentSpaceSpaceModel_r92b77a_1 (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)
lemma boundedScalarSection_norm (b : PreL2 A J α hs ht true)
    (f : X → ℝ) (hfm : AEStronglyMeasurable f (geometricVolume A J α))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C) :
    ‖boundedScalarSection A J α hs ht b f hfm C hC hf‖ ≤ C*‖b‖ := by
  rw [boundedScalarSection,(InnerProductSpace.toDual ℝ (L2 A J α hs ht true)).symm.norm_map]
  apply LinearMap.opNorm_extendOfNorm_le (smoothL2_dense A J α hs ht true)
    (mul_nonneg hC (norm_nonneg _))
  intro a
  simpa only [scalarSectionFunctional,LinearMap.coe_mk,AddHom.coe_mk,
    LinearIsometry.coe_toLinearMap,LinearIsometry.norm_map,mul_right_comm C] using
      bounded_pairing_integral_bound A J α hs ht a b f hC hf

lemma boundedScalarSection_pairing (b : PreL2 A J α hs ht true)
    (f : X → ℝ) (hfm : AEStronglyMeasurable f (geometricVolume A J α))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C)
    (a : PreL2 A J α hs ht true) :
    ⟪boundedScalarSection A J α hs ht b f hfm C hC hf,smoothL2 A J α hs ht true a⟫ =
      ∫ x, f x * GeometricAdjoint.pairing J α ht a.val b.val x ∂geometricVolume A J α := by
  rw [boundedScalarSection,InnerProductSpace.toDual_symm_apply]
  exact LinearMap.extendOfNorm_eq (smoothL2_dense A J α hs ht true)
    ⟨C*‖b‖,fun v => by
      simpa only [scalarSectionFunctional,LinearMap.coe_mk,AddHom.coe_mk,
        LinearIsometry.coe_toLinearMap,LinearIsometry.norm_map,mul_right_comm C] using
        bounded_pairing_integral_bound A J α hs ht v b f hC hf⟩ a

end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

lemma boundedFrameSection_norm (v : X → FrameSpace A)
    (hvm : AEStronglyMeasurable v (geometricVolume A J α))
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ᵐ x ∂geometricVolume A J α, ‖v x‖ ≤ V) :
    ‖boundedFrameSection A J α hs ht E hE v hvm V hV hv‖ ≤
      (frameMassBound A * ∑ p : A.centers, ∑ j : Fin 6, ‖globalFramePreL2 A J α hs ht E hE p j‖)*V := by
  unfold boundedFrameSection
  calc
    _ ≤ ∑ p : A.centers, ∑ j : Fin 6, (frameMassBound A*V)*‖globalFramePreL2 A J α hs ht E hE p j‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact boundedScalarSection_norm _ _ _ _ _ _ _ _ _ _ _
    _ = _ := by simp_rw [← Finset.mul_sum] <;> ring

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma framePairing_coefficient_sum (a : TwoForm X) (v : X → FrameSpace A) (x : X) :
    framePairing A J α ht E a x (v x) =
      ∑ p : A.centers, ∑ j : Fin 6,
        frameCoefficient A v p j x * GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) x := by
  simp only [framePairing,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold frameCoefficient
  ring

lemma boundedFrameSection_pairing (v : X → FrameSpace A)
    (hvm : AEStronglyMeasurable v (geometricVolume A J α))
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ᵐ x ∂geometricVolume A J α, ‖v x‖ ≤ V)
    (a : PreL2 A J α hs ht true) :
    ⟪boundedFrameSection A J α hs ht E hE v hvm V hV hv,smoothL2 A J α hs ht true a⟫ =
      ∫ x, framePairing A J α ht E a.val x (v x) ∂geometricVolume A J α := by
  have hi (p : A.centers) (j : Fin 6) : Integrable (fun x => frameCoefficient A v p j x *
      GeometricAdjoint.pairing J α ht a.val (globalFrame J α ht A E p j) x) (geometricVolume A J α) :=
    bounded_pairing_integrable A J α hs ht a (globalFramePreL2 A J α hs ht E hE p j) _
      (frameCoefficient_measurable A J α v hvm p j) (mul_nonneg (frameMassBound_nonneg A) hV)
      (frameCoefficient_bound A J α v hv p j)
  simp_rw [framePairing_coefficient_sum]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun j _ => hi p j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  unfold boundedFrameSection
  simp_rw [sum_inner,boundedScalarSection_pairing]
  rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelL2
open Set Filter _root_.MeasureTheory
open scoped Topology
variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma action_test_swap (K : X → X → F →L[ℝ] F)
    (hK : StronglyMeasurable (Function.uncurry K)) (v : X → F) (hvm : StronglyMeasurable v)
    (φ : X → F →L[ℝ] ℝ) (hφm : StronglyMeasurable φ)
    {M V C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hKb : ∀ x y, ‖K x y‖ ≤ M) (hv : ∀ y, ‖v y‖ ≤ V) (hφ : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, φ x (action μ K v x) ∂μ) = ∫ y, ∫ x, φ x (K x y (v y)) ∂μ ∂μ := by
  have hbound (x y : X) : ‖K x y (v y)‖ ≤ M*V :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hKb x y) (hv y) (norm_nonneg _) hM)
  have hm := applied_measurable K hK v hvm
  have htm : StronglyMeasurable (fun p : X × X => φ p.1 (K p.1 p.2 (v p.2))) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hφm.comp_measurable measurable_fst).prodMk hm)
  have hi (x : X) : Integrable (fun y => K x y (v y)) μ := by
    apply (integrable_const (M*V)).mono'
      ((hm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    exact Eventually.of_forall (hbound x)
  have ht : Integrable (fun p : X × X => φ p.1 (K p.1 p.2 (v p.2))) (μ.prod μ) := by
    apply (integrable_const (C*(M*V))).mono' htm.aestronglyMeasurable
    filter_upwards [] with p
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hφ _) (hbound _ _) (norm_nonneg _) hC)
  calc
    _ = ∫ x, ∫ y, φ x (K x y (v y)) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact ((φ x).integral_comp_comm (hi x)).symm
    _ = _ := integral_integral_swap ht

end TamingCompatibility.GeometricHilbert.KernelL2

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

lemma frameNormConstant_nonneg : 0 ≤ frameNormConstant A J α hs ht E hE :=
  mul_nonneg (frameMassBound_nonneg A) (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

lemma kernelSectionL2_norm (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hKm : StronglyMeasurable (Function.uncurry K))
    (H : ℝ) (hH : 0 ≤ H)
    (hKi : ∀ x, Integrable (fun y => ‖K x y‖) (geometricVolume A J α))
    (hKb : ∀ x, (∫ y, ‖K x y‖ ∂geometricVolume A J α) ≤ H)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V) :
    ‖kernelSectionL2 A J α hs ht E hE K hKm H hH hKi hKb v hvm V hV hv‖ ≤
      frameNormConstant A J α hs ht E hE * (H*V) := by
  unfold kernelSectionL2 frameNormConstant
  apply boundedFrameSection_norm

lemma kernelSectionL2_pairing (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hKm : StronglyMeasurable (Function.uncurry K))
    (H : ℝ) (hH : 0 ≤ H)
    (hKi : ∀ x, Integrable (fun y => ‖K x y‖) (geometricVolume A J α))
    (hKb : ∀ x, (∫ y, ‖K x y‖ ∂geometricVolume A J α) ≤ H)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V)
    (M : ℝ) (hM : 0 ≤ M) (hsup : ∀ x y, ‖K x y‖ ≤ M)
    (a : PreL2 A J α hs ht true) :
    ⟪kernelSectionL2 A J α hs ht E hE K hKm H hH hKi hKb v hvm V hV hv,
      smoothL2 A J α hs ht true a⟫ =
      ∫ y, ∫ x, framePairing A J α ht E a.val x (K x y (v y)) ∂geometricVolume A J α ∂geometricVolume A J α := by
  let := geometricVolume_finite A J α hs ht
  obtain ⟨C,hC,hφ⟩ := framePairing_bound A J α hs ht E hE a.val a.property
  rw [kernelSectionL2,boundedFrameSection_pairing]
  exact KernelL2.action_test_swap _ K hKm v hvm _
    (framePairing_continuous A J α hs ht E hE a.val a.property).stronglyMeasurable hM hC hsup hv hφ

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatBoundL2
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
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

lemma heatBoundL2_norm (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (T H : ℝ)
    (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V) (t : ℝ) :
    ‖heatBoundL2 A J α hs ht E hE K T H hK v hvm V hV hv t‖ ≤
      frameNormConstant A J α hs ht E hE * (H*V) := by
  classical
  let := geometricMetricSpace J α hs ht
  unfold heatBoundL2
  split_ifs
  · exact kernelSectionL2_norm A J α hs ht E hE _ _ _ _ _ _ _ _ _ _ _
  · exact (norm_zero.trans_le (mul_nonneg (frameNormConstant_nonneg A J α hs ht E hE)
      (mul_nonneg hK.nonneg hV)))

lemma heatBoundL2_pairing (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (T H : ℝ)
    (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V)
    (a : PreL2 A J α hs ht true) {t : ℝ} (htp : t ∈ Ioc 0 T) :
    ⟪heatBoundL2 A J α hs ht E hE K T H hK v hvm V hV hv t,
      smoothL2 A J α hs ht true a⟫ = kernelWeakAction A J α ht E K v a.val t := by
  classical
  let := geometricMetricSpace J α hs ht
  unfold heatBoundL2
  rw [dite_eq_left htp]
  apply kernelSectionL2_pairing A J α hs ht E hE _ _ _ _ _ _ _ _ _ _ _ (H/t^2)
    (div_nonneg hK.nonneg (sq_nonneg t))
  simpa only [VolterraBounds.weight,pow_zero,one_mul] using hK.sup t htp

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeErrorInitial
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
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs in
omit [T2Space X] [BorelSpace X] in
lemma kernelWeakAction_bound_of_col
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A) (v : X → FrameSpace A)
    (a : TwoForm X) {C V H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hφ : ∀ x, ‖framePairing A J α ht E a x‖ ≤ C) (hv : ∀ y, ‖v y‖ ≤ V)
    (t : ℝ) (hKi : ∀ y, Integrable (fun x => ‖K t x y‖) (geometricVolume A J α))
    (hKb : ∀ y, (∫ x, ‖K t x y‖ ∂geometricVolume A J α) ≤ H) :
    ‖kernelWeakAction A J α ht E K v a t‖ ≤ (geometricVolume A J α).real univ * (C*V*H) := by
  let := geometricVolume_finite A J α hs ht
  unfold kernelWeakAction
  calc
    _ ≤ ∫ _y : X, C*V*H ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le (integrable_const _)
      filter_upwards [] with y
      exact (kernel_pairing_integral_bound A J α ht E a hC hφ _ (v y) (hKi y) (hKb y)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hv y) hC) hH)
    _ = _ := by rw [integral_const]; rfl

attribute [local irreducible] framePairing globalLeading globalResidual globalError

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

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

attribute [local irreducible] framePairing globalLeading globalResidual

include hE in
lemma globalError_weak_initial_of_bounds {T L C : ℝ} (hT : 0 < T)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T L (globalLeading J α ht A E))
    (hC : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C (globalCorrection J α ht A E T))
    (v : X → FrameSpace A) (hv : Continuous v) (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (kernelWeakAction A J α ht E (globalError J α ht A E T) v a) (𝓝[>] 0) (𝓝 0) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  obtain ⟨V,hV⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  have hz := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (geometricVolume A J α).real univ *
    (B*(max V 0)*(L*C))) (𝓝[>] 0) (𝓝 _)).mul
      (nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0))
  simp only [mul_zero] at hz
  apply squeeze_zero_norm' _ hz
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t htp htT
  have hc (y : X) := VolterraKernel.convolution_col (geometricVolume A J α) 0 _ _ hL hC ⟨htp,htT.le⟩ y
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hc
  have hh := kernelWeakAction_bound_of_col A J α hs ht E _ v a hB
    (mul_nonneg (mul_nonneg htp.le hL.nonneg) hC.nonneg) hφ
    (fun y => (hV y (mem_univ y)).trans (le_max_left V 0)) t
    (fun y => (hc y).1) (fun y => (hc y).2)
  exact hh.trans_eq (by ring)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCandidateL2Bounds
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
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

attribute [local irreducible] framePairing globalLeading globalResidual

include hE in
lemma globalCandidate_L2_of_bounds_oai {T L C : ℝ} (hT : 0 < T)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T L (globalLeading J α ht A E))
    (hC : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C (globalCorrection J α ht A E T))
    (v : X → FrameSpace A) (hv : Continuous v) :
    ∃ (f : L2 A J α hs ht true) (U : ℝ → L2 A J α hs ht true) (M : ℝ),
      0 ≤ M ∧ U 0 = f ∧ (∀ t ∈ Icc 0 T, ‖U t‖ ≤ M) ∧
      (∀ a : PreL2 A J α hs ht true,
        ⟪f,smoothL2 A J α hs ht true a⟫ =
          ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
      (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioc 0 T,
        ⟪U t,smoothL2 A J α hs ht true a⟫ =
          kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
          kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t) ∧
      (∀ a : PreL2 A J α hs ht true,
        Tendsto (fun t => ⟪U t,smoothL2 A J α hs ht true a⟫) (𝓝[>] 0)
          (𝓝 ⟪f,smoothL2 A J α hs ht true a⟫)) := by
  classical
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  have hErr := VolterraKernel.convolution_heatBound (geometricVolume A J α) 0 hT.le _ _ hL hC
  obtain ⟨V₀,hV₀⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  let V := max V₀ 0
  have hV : 0 ≤ V := le_max_right _ _
  have hvb (y : X) : ‖v y‖ ≤ V := (hV₀ y (mem_univ y)).trans (le_max_left _ _)
  let f := boundedFrameSection A J α hs ht E hE v hv.aestronglyMeasurable V hV
    (Eventually.of_forall hvb)
  let P := heatBoundL2 A J α hs ht E hE _ T L hL v hv.stronglyMeasurable V hV hvb
  let Q := heatBoundL2 A J α hs ht E hE _ T (4*T*L*C) hErr v hv.stronglyMeasurable V hV hvb
  let U := fun t => if t=0 then f else P t+Q t
  let M := ‖f‖ + frameNormConstant A J α hs ht E hE*(L*V) +
    frameNormConstant A J α hs ht E hE*((4*T*L*C)*V)
  have hLn := mul_nonneg (frameNormConstant_nonneg A J α hs ht E hE) (mul_nonneg hL.nonneg hV)
  have hQn := mul_nonneg (frameNormConstant_nonneg A J α hs ht E hE) (mul_nonneg hErr.nonneg hV)
  have hf (a : PreL2 A J α hs ht true) : ⟪f,smoothL2 A J α hs ht true a⟫ =
      ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α :=
    boundedFrameSection_pairing A J α hs ht E hE v hv.aestronglyMeasurable V hV
      (Eventually.of_forall hvb) a
  have hp (a : PreL2 A J α hs ht true) (t : ℝ) (htp : t ∈ Ioc 0 T) :
      ⟪U t,smoothL2 A J α hs ht true a⟫ =
        kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
        kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t := by
    rw [show U t = P t+Q t by simp [U,htp.1.ne'],inner_add_left]
    rw [heatBoundL2_pairing A J α hs ht E hE _ T L hL v hv.stronglyMeasurable V hV hvb a htp,
      heatBoundL2_pairing A J α hs ht E hE _ T _ hErr v hv.stronglyMeasurable V hV hvb a htp]
    rfl
  refine ⟨f,U,M,by dsimp only [M] <;> positivity,by simp [U],?_,hf,hp,?_⟩
  · intro t _ht
    by_cases hz : t=0
    · simpa [U,hz,M] using (show ‖f‖ ≤ M by dsimp only [M] <;> linarith)
    · rw [show U t = P t+Q t by simp [U,hz]]
      have hP := heatBoundL2_norm A J α hs ht E hE _ T L hL v hv.stronglyMeasurable V hV hvb t
      have hQ := heatBoundL2_norm A J α hs ht E hE _ T _ hErr v hv.stronglyMeasurable V hV hvb t
      exact (norm_add_le _ _).trans (by dsimp only [M] <;> linarith [norm_nonneg f])
  · intro a
    have hh := (kernelWeakAction_leading_initial A J α hs ht E hE v hv a.val a.property).add
      (globalError_weak_initial_of_bounds A J α hs ht E hE hT hL hC v hv a.val a.property)
    rw [add_zero,← hf a] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t htp htT
    exact (hp a t ⟨htp,htT.le⟩).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_L2_of_bounds_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_L2_of_bounds_oai.{u_1}
