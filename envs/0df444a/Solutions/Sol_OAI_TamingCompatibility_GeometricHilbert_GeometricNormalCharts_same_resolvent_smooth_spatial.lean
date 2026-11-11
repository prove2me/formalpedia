-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_smooth_spatial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:30:07.969379+00:00
-- url     : https://prove2.me/submissions/ea22cc61-4553-42be-b3dd-a1b0e1af3755

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc028
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledB_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_same_resolvent_continuous_data
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

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_r0b2f9c_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_r0b2f9c_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
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

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_r0b2f9c_2 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_r0b2f9c_2 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelTestTransform
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

include hs hE in
omit [ConnectedSpace X] [SecondCountableTopology X] in
lemma kernelTestLinear_measurable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : VolterraKernel.MeasurableKernel K) (a : TwoForm X) (ha : IsSmooth a) :
    StronglyMeasurable (Function.uncurry (kernelTestLinear A J α ht E K a)) := by
  let := geometricVolume_finite A J α hs ht
  have hφ := (framePairing_continuous A J α hs ht E hE a ha).stronglyMeasurable
  have hm : StronglyMeasurable (fun p : (ℝ × X) × X =>
      (framePairing A J α ht E a p.2).comp (K p.1.1 p.2 p.1.2)) :=
    (continuous_fst.clm_comp continuous_snd).comp_stronglyMeasurable
      ((hφ.comp_measurable measurable_snd).prodMk
        (hK.comp_measurable (show Measurable (fun p : (ℝ × X) × X =>
          (p.1.1,p.2,p.1.2)) by fun_prop)))
  exact hm.integral_prod_right

include hE in
omit [SecondCountableTopology X] in
lemma kernelTestLinear_integrable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T) (y : X) :
    Integrable (fun x => (framePairing A J α ht E a x).comp (K t x y))
      (geometricVolume A J α) := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨B,_hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  have hi := hK.col_int t htp y
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hi
  have hm : StronglyMeasurable (fun x => (framePairing A J α ht E a x).comp (K t x y)) :=
    (continuous_fst.clm_comp continuous_snd).comp_stronglyMeasurable
    ((framePairing_continuous A J α hs ht E hE a ha).stronglyMeasurable.prodMk
      (hK.measurable.comp_measurable (measurable_const.prodMk (measurable_id.prodMk measurable_const))))
  apply (hi.const_mul B).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun x => (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hφ x) (norm_nonneg _))

include hE in
omit [SecondCountableTopology X] in
lemma kernelTestLinear_apply
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T) (y : X) (v : FrameSpace A) :
    kernelTestLinear A J α ht E K a t y v = kernelTestSlice A J α ht E K y v a t :=
  ContinuousLinearMap.integral_apply (kernelTestLinear_integrable A J α hs ht E hE K hK a ha htp y) v

include hE in
omit [SecondCountableTopology X] [BorelSpace X] in
lemma kernelTestLinear_uniform_bound
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc 0 T, ∀ y, ‖kernelTestLinear A J α ht E K a t y‖ ≤ B := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  refine ⟨B*H,mul_nonneg hB hK.nonneg,?_⟩
  intro t hp y
  have hi := hK.col_int t hp y
  have hb := hK.col t hp y
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hi hb
  calc
    _ ≤ ∫ x, B*‖K t x y‖ ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le (hi.const_mul B)
      exact Eventually.of_forall fun x => (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hφ x) (norm_nonneg _))
    _ = B*(∫ x, ‖K t x y‖ ∂geometricVolume A J α) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hB

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeVolterraPairing
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

include hE in
omit [SecondCountableTopology X] in
lemma kernelInputTest_eq_weakAction
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T)
    (v : X → FrameSpace A) :
    kernelInputTest A J α ht E K a t v = kernelWeakAction A J α ht E K v a t := by
  apply integral_congr_ae
  filter_upwards [] with y
  exact kernelTestLinear_apply A J α hs ht E hE K hK a ha htp y (v y)

include hs hE in
omit [ConnectedSpace X] in
lemma kernelInputTest_shift_measurable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : VolterraKernel.MeasurableKernel K) (a : TwoForm X) (ha : IsSmooth a)
    (W : ℝ → X → FrameSpace A) (hW : StronglyMeasurable (Function.uncurry W)) :
    StronglyMeasurable (fun p : ℝ × ℝ => kernelInputTest A J α ht E K a (p.1-p.2) (W p.2)) := by
  let := geometricVolume_finite A J α hs ht
  have hkm := kernelTestLinear_measurable A J α hs ht E hE K hK a ha
  have hm : StronglyMeasurable (fun p : (ℝ × ℝ) × X =>
      kernelTestLinear A J α ht E K a (p.1.1-p.1.2) p.2 (W p.1.2 p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hkm.comp_measurable (show Measurable (fun p : (ℝ × ℝ) × X => (p.1.1-p.1.2,p.2)) by fun_prop)).prodMk
        (hW.comp_measurable (measurable_fst.snd.prodMk measurable_snd)))
  exact hm.integral_prod_right

include hs in
omit [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [BorelSpace X] in
lemma kernelInputTest_bound
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A) (a : TwoForm X)
    (t : ℝ) (v : X → FrameSpace A) {B V : ℝ} (hB : 0 ≤ B)
    (hφ : ∀ y, ‖kernelTestLinear A J α ht E K a t y‖ ≤ B) (hv : ∀ y, ‖v y‖ ≤ V) :
    ‖kernelInputTest A J α ht E K a t v‖ ≤ (geometricVolume A J α).real univ*(B*V) := by
  let := geometricVolume_finite A J α hs ht
  calc
    _ ≤ ∫ y : X, B*V ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le (integrable_const _)
      exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hφ y) (hv y) (norm_nonneg _) hB)
    _ = _ := by simp [integral_const,smul_eq_mul]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeBoundedInputPrimitive
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

include hE in
omit [SecondCountableTopology X] [BorelSpace X] in
lemma kernelInputTest_uniform_bound
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {V : ℝ} (hV : 0 ≤ V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc 0 T, ∀ v : X → FrameSpace A,
      (∀ y, ‖v y‖ ≤ V) → ‖kernelInputTest A J α ht E K a t v‖ ≤ B := by
  obtain ⟨B,hB,hφ⟩ := kernelTestLinear_uniform_bound A J α hs ht E hE K hK a ha
  refine ⟨(geometricVolume A J α).real univ*(B*V),by positivity,?_⟩
  intro t hp v hv
  exact kernelInputTest_bound A J α hs ht E K a t v hB (hφ t hp) hv

include hs hE in
omit [ConnectedSpace X] in
lemma kernelInputTest_time_measurable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : VolterraKernel.MeasurableKernel K) (a : TwoForm X) (ha : IsSmooth a)
    (v : X → FrameSpace A) (hm : StronglyMeasurable v) :
    StronglyMeasurable (fun t => kernelInputTest A J α ht E K a t v) := by
  have hh := kernelInputTest_shift_measurable A J α hs ht E hE K hK a ha
    (fun _ => v) (hm.comp_measurable measurable_snd)
  simpa [Function.comp_def] using hh.comp_measurable (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelGammaBounds
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open _root_.MeasureTheory Set

lemma moment_integrable (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s^n * Real.exp (-(b*s))) (Ioi 0) := by
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hb)

lemma moment_integral (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ s : ℝ in Ioi 0, s^n * Real.exp (-(b*s))) = moment n b := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1)
    (by positivity) hb
  simp_rw [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  have he : (n:ℝ)+1 = ((n+1:ℕ):ℝ) := by push_cast; rfl
  rw [he, Real.rpow_natCast] at h
  exact h

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open Set _root_.MeasureTheory

lemma polynomialMoment_integrable (q N : ℕ) :
    IntegrableOn (fun s : ℝ => Real.exp (-s)*s^q*(1+s)^N) (Ioi 0) := by
  have hm (n : ℕ) : IntegrableOn (fun s : ℝ => Real.exp (-s)*s^n) (Ioi 0) := by
    simpa only [one_mul,mul_one,mul_comm] using moment_integrable n (by norm_num : (0:ℝ)<1)
  have hb := ((hm q).add (hm (q+N))).const_mul ((2:ℝ)^(N-1))
  apply hb.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 ≤ s := hs.le
  dsimp only [Pi.add_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hh := mul_le_mul_of_nonneg_left (add_pow_le (by norm_num : (0:ℝ)≤1) hs.le N)
    (mul_nonneg (Real.exp_pos (-s)).le (pow_nonneg hs.le q))
  simpa only [Pi.add_apply,one_pow,one_mul,mul_one,pow_add,mul_add,add_mul,mul_assoc,mul_left_comm,mul_comm] using hh

lemma polynomialMoment_bound (q N : ℕ) :
    (∫ s : ℝ in Ioi 0, Real.exp (-s)*s^q*(1+s)^N) ≤
      (2:ℝ)^(N-1)*(moment q 1+moment (q+N) 1) := by
  have hm (n : ℕ) : IntegrableOn (fun s : ℝ => Real.exp (-s)*s^n) (Ioi 0) := by
    simpa only [one_mul,mul_one,mul_comm] using moment_integrable n (by norm_num : (0:ℝ)<1)
  calc
    _ ≤ ∫ s : ℝ in Ioi 0, (2:ℝ)^(N-1)*(Real.exp (-s)*s^q+Real.exp (-s)*s^(q+N)) := by
      apply integral_mono_ae (polynomialMoment_integrable q N) (((hm q).add (hm (q+N))).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hh := mul_le_mul_of_nonneg_left (add_pow_le (by norm_num : (0:ℝ)≤1) hs.le N)
        (mul_nonneg (Real.exp_pos (-s)).le (pow_nonneg hs.le q))
      simpa only [Pi.add_apply,one_pow,one_mul,mul_one,pow_add,mul_add,add_mul,mul_assoc,mul_left_comm,mul_comm] using hh
    _ = _ := by
      rw [integral_const_mul,integral_add (hm q) (hm (q+N))]
      have he (n : ℕ) : (∫ s : ℝ in Ioi 0, Real.exp (-s)*s^n) = moment n 1 := by
        simpa only [one_mul,mul_one,mul_comm] using moment_integral n (by norm_num : (0:ℝ)<1)
      rw [he,he]

variable {X : Type*} [PseudoMetricSpace X]

lemma weight_rescale (N : ℕ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (x y : X) :
    VolterraBounds.weight N (r^2) x y ≤
      (1+s)^N * VolterraBounds.weight N (r^2*s) x y := by
  unfold VolterraBounds.weight
  rw [← mul_pow,Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq_eq_abs,abs_of_pos hr]
  apply pow_le_pow_left₀ (by positivity)
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsr : Real.sqrt s ≤ 1+s := by
    have hh := sq_nonneg (Real.sqrt s-1)
    have he := Real.sq_sqrt hs.le
    nlinarith [Real.sqrt_nonneg s]
  have hb : 1 ≤ (1+s)/Real.sqrt s := (le_div_iff₀ hsqrt).mpr (by simpa using hsr)
  have ha : 0 ≤ dist x y/r := div_nonneg dist_nonneg hr.le
  have hh := mul_le_mul_of_nonneg_right hb ha
  have he : (1+s)*(1+dist x y/(r*Real.sqrt s)) =
      1+s+((1+s)/Real.sqrt s)*(dist x y/r) := by ring
  rw [he]
  nlinarith

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

omit [CompleteSpace B] in
lemma weighted_gamma_integrand (q k N : ℕ) (hqk : q+k=5)
    {r s A : ℝ} (hr : 0 < r) (hs : 0 < s)
    (K : ℝ → X → X → B) (x y : X)
    (hK : VolterraBounds.weight N (r^2*s) x y * ‖K (r^2*s) x y‖ ≤ A/(r^2*s)^k) :
    VolterraBounds.weight N (r^2) x y * ‖hodgeGammaWeight s • K (r^2*s) x y‖ ≤
      A/r^(2*k) * (Real.exp (-s)*s^q*(1+s)^N) := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hodgeGammaWeight_nonneg hs.le)]
  have hh := mul_le_mul_of_nonneg_left hK (pow_nonneg (by linarith : (0:ℝ)≤1+s) N)
  have hb := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_right (weight_rescale N hr hs x y) (norm_nonneg (K (r^2*s) x y))).trans
      (by simpa only [mul_assoc] using hh))
    (hodgeGammaWeight_nonneg hs.le)
  have he : hodgeGammaWeight s*((1+s)^N*(A/(r^2*s)^k)) =
      A/r^(2*k)*(Real.exp (-s)*s^q*(1+s)^N) := by
    unfold hodgeGammaWeight
    rw [← hqk,pow_add,mul_pow,← pow_mul]
    field_simp [ne_of_gt hr,ne_of_gt hs]
  calc
    _ ≤ hodgeGammaWeight s*((1+s)^N*(A/(r^2*s)^k)) := by
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hb
    _ = _ := he

omit [CompleteSpace B] in
lemma gammaKernel_bound (q k N : ℕ) (hqk : q+k=5)
    {T r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A) (K : ℝ → X → X → B) (x y : X)
    (hKm : AEStronglyMeasurable (fun s : ℝ => K (r^2*s) x y) (volume.restrict (Ioc 0 (T/r^2))))
    (hK : ∀ t ∈ Ioc 0 T, VolterraBounds.weight N t x y*‖K t x y‖ ≤ A/t^k) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s • K (r^2*s) x y) (Ioc 0 (T/r^2)) ∧
      VolterraBounds.weight N (r^2) x y*‖gammaKernel K T r x y‖ ≤
        ((1/120:ℝ)*A*(2:ℝ)^(N-1)*(moment q 1+moment (q+N) 1))/r^(2*k) := by
  let W := VolterraBounds.weight N (r^2) x y
  have hW : 0 < W := VolterraBounds.weight_pos N (sq_pos_of_pos hr) x y
  let Φ := fun s : ℝ => Real.exp (-s)*s^q*(1+s)^N
  have hΦ : IntegrableOn Φ (Ioi 0) := polynomialMoment_integrable q N
  have hsub : Ioc 0 (T/r^2) ⊆ Ioi (0:ℝ) := fun _ h => h.1
  have hΦ' := hΦ.mono_set hsub
  have hp (s : ℝ) (hsp : s ∈ Ioc 0 (T/r^2)) :
      W*‖hodgeGammaWeight s • K (r^2*s) x y‖ ≤ A/r^(2*k) * Φ s := by
    apply weighted_gamma_integrand q k N hqk hr hsp.1 K x y
    exact hK _ ⟨mul_pos (sq_pos_of_pos hr) hsp.1,by
      have hh := (le_div_iff₀ (sq_pos_of_pos hr)).mp hsp.2
      simpa only [mul_comm] using hh⟩
  have hi : IntegrableOn (fun s : ℝ => hodgeGammaWeight s • K (r^2*s) x y) (Ioc 0 (T/r^2)) := by
    apply (hΦ'.const_mul (A/r^(2*k)/W)).mono' (hodgeGammaWeight_continuous.aestronglyMeasurable.smul hKm)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hh := (le_div_iff₀ hW).mpr (show ‖hodgeGammaWeight s • K (r^2*s) x y‖*W ≤ A/r^(2*k)*Φ s by
      simpa only [mul_comm] using hp s hs)
    change ‖hodgeGammaWeight s • K (r^2*s) x y‖ ≤ (A/r^(2*k)/W)*Φ s
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  refine ⟨hi,?_⟩
  have hI : W*‖∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s • K (r^2*s) x y‖ ≤
      A/r^(2*k) * ((2:ℝ)^(N-1)*(moment q 1+moment (q+N) 1)) := by
    calc
      _ ≤ W*(∫ s : ℝ in Ioc 0 (T/r^2), ‖hodgeGammaWeight s • K (r^2*s) x y‖) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hW.le
      _ = ∫ s : ℝ in Ioc 0 (T/r^2), W*‖hodgeGammaWeight s • K (r^2*s) x y‖ :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ s : ℝ in Ioc 0 (T/r^2), A/r^(2*k)*Φ s := by
        apply integral_mono_ae (hi.norm.const_mul _) (hΦ'.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hp s hs
      _ = A/r^(2*k) * ∫ s : ℝ in Ioc 0 (T/r^2), Φ s := integral_const_mul _ _
      _ ≤ A/r^(2*k) * ∫ s : ℝ in Ioi 0, Φ s := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hA (pow_nonneg hr.le _))
        apply setIntegral_mono_set hΦ
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          have hs0 : 0 ≤ s := hs.le
          dsimp [Φ] <;> positivity
        · exact Filter.Eventually.of_forall hsub
      _ ≤ _ := mul_le_mul_of_nonneg_left (polynomialMoment_bound q N) (div_nonneg hA (pow_nonneg hr.le _))
  unfold gammaKernel
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/120)]
  have hh := mul_le_mul_of_nonneg_left hI (by norm_num : (0:ℝ)≤1/120)
  dsimp only [W] at hh
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open Set Filter _root_.MeasureTheory
variable {X B : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

omit [CompleteSpace B] [PseudoMetricSpace X] in
lemma gammaKernel_measurable (K : ℝ → X → X → B)
    (hKm : StronglyMeasurable (fun p : ℝ × X × X => K p.1 p.2.1 p.2.2)) (T r : ℝ) :
    StronglyMeasurable (fun p : X × X => gammaKernel K T r p.1 p.2) := by
  have hm : StronglyMeasurable (fun p : (X × X) × ℝ =>
      hodgeGammaWeight p.2 • K (r^2*p.2) p.1.1 p.1.2) :=
    ((hodgeGammaWeight_continuous.stronglyMeasurable.comp_measurable measurable_snd).smul
      (hKm.comp_measurable (show Measurable (fun p : (X × X) × ℝ => (r^2*p.2,p.1.1,p.1.2)) by fun_prop)))
  exact (hm.integral_prod_right (ν := volume.restrict (Ioc 0 (T/r^2)))).const_smul (1/120 : ℝ)

variable (μ : Measure (X × X)) [IsFiniteMeasure μ]

lemma gammaKernel_pairing (q k : ℕ) (hqk : q+k=5) {T r A : ℝ} (hr : 0 < r)
    (K : ℝ → X → X → B)
    (hKm : StronglyMeasurable (fun p : ℝ × X × X => K p.1 p.2.1 p.2.2))
    (hK : ∀ t ∈ Ioc 0 T, ∀ x y, ‖K t x y‖ ≤ A/t^k)
    (Θ : X × X → B →L[ℝ] ℝ) (hΘm : StronglyMeasurable Θ)
    {M : ℝ} (hM : 0 ≤ M) (hΘ : ∀ p, ‖Θ p‖ ≤ M) :
    (∫ p, Θ p (gammaKernel K T r p.1 p.2) ∂μ) =
      (1/120 : ℝ) * ∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s *
        (∫ p, Θ p (K (r^2*s) p.1 p.2) ∂μ) := by
  let ν := volume.restrict (Ioc 0 (T/r^2))
  let G := fun s (p : X × X) => hodgeGammaWeight s • K (r^2*s) p.1 p.2
  let m := fun s : ℝ => A/r^(2*k)*(Real.exp (-s)*s^q)
  have hm : Integrable m ν := by
    have h := polynomialMoment_integrable q 0
    simp only [pow_zero,mul_one] at h
    exact (h.mono_set (fun _ h => h.1)).const_mul _
  have hGm : StronglyMeasurable (Function.uncurry G) :=
    ((hodgeGammaWeight_continuous.stronglyMeasurable.comp_measurable measurable_fst).smul
      (hKm.comp_measurable (show Measurable (fun p : ℝ × X × X => (r^2*p.1,p.2.1,p.2.2)) by fun_prop)))
  have hGb (s : ℝ) (hs : s ∈ Ioc 0 (T/r^2)) (p : X × X) : ‖G s p‖ ≤ m s := by
    have hst : r^2*s ∈ Ioc 0 T := ⟨mul_pos (sq_pos_of_pos hr) hs.1,by
      have h := (le_div_iff₀ (sq_pos_of_pos hr)).mp hs.2
      simpa only [mul_comm] using h⟩
    have hb : VolterraBounds.weight 0 (r^2*s) p.1 p.2 * ‖K (r^2*s) p.1 p.2‖ ≤ A/(r^2*s)^k := by
      simpa only [VolterraBounds.weight,pow_zero,one_mul] using hK _ hst p.1 p.2
    simpa only [VolterraBounds.weight,pow_zero,one_mul,mul_one] using
      weighted_gamma_integrand q k 0 hqk hr hs.1 K p.1 p.2 hb
  have hGi (p : X × X) : Integrable (fun s => G s p) ν := by
    apply hm.mono' ((hGm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hGb s hs p
  have hFm : StronglyMeasurable (fun p : ℝ × X × X => Θ p.2 (G p.1 p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hΘm.comp_measurable measurable_snd).prodMk hGm)
  have hFi : Integrable (fun p : ℝ × X × X => Θ p.2 (G p.1 p.2)) (ν.prod μ) := by
    apply ((hm.const_mul M).comp_fst μ).mono' hFm.aestronglyMeasurable
    have hp : ∀ᵐ p : ℝ × X × X ∂ν.prod μ, p.1 ∈ Ioc 0 (T/r^2) := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact Eventually.of_forall fun _ => hs
    filter_upwards [hp] with p hp
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hΘ p.2) (hGb p.1 hp p.2) (norm_nonneg _) hM)
  calc
    _ = (1/120 : ℝ) * ∫ p, ∫ s, Θ p (G s p) ∂ν ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with p
      unfold gammaKernel
      rw [map_smul,smul_eq_mul,(Θ p).integral_comp_comm (hGi p)]
    _ = (1/120 : ℝ) * ∫ s, ∫ p, Θ p (G s p) ∂μ ∂ν := by
      exact congrArg (fun a : ℝ => (1/120 : ℝ)*a) (integral_integral_swap hFi).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with s
      simp only [G,map_smul,smul_eq_mul,integral_const_mul]

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalGamma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldLocalization ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)

lemma globalGamma_bounds_of (n : ℕ) {T L C : ℝ}
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E))
    (hC : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T))
    {r : ℝ} (hr : 0 < r) :
    let := geometricMetricSpace J α hs ht
    ∀ x y : X,
      (IntegrableOn (fun s : ℝ => hodgeGammaWeight s • globalLeading J α ht A E (r^2*s) x y)
        (Ioc 0 (T/r^2)) ∧
       VolterraBounds.weight n (r^2) x y *
        ‖HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y‖ ≤
          ((1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1))/r^4) ∧
      (IntegrableOn (fun s : ℝ => hodgeGammaWeight s • globalError J α ht A E T (r^2*s) x y)
        (Ioc 0 (T/r^2)) ∧
       VolterraBounds.weight n (r^2) x y *
        ‖HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y‖ ≤
          ((1/120:ℝ)*(4*L*C)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1))/r^2) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  have hEm := VolterraKernel.convolution_measurable (geometricVolume A J α) _ _
    hL.measurable hC.measurable
  intro x y
  constructor
  · exact HodgeKernelBounds.gammaKernel_bound 3 2 n (by norm_num) hr hL.nonneg _ x y
      ((hL.measurable.comp_measurable (show Measurable (fun s : ℝ => (r^2*s,x,y)) by fun_prop)).aestronglyMeasurable)
      (fun t htp => hL.sup t htp x y)
  · apply HodgeKernelBounds.gammaKernel_bound 4 1 n (by norm_num) hr
      (by have := hL.nonneg; have := hC.nonneg; positivity) _ x y
      ((hEm.comp_measurable (show Measurable (fun s : ℝ => (r^2*s,x,y)) by fun_prop)).aestronglyMeasurable)
    intro t htp
    simpa only [pow_one] using
      (VolterraKernel.convolution_sup (geometricVolume A J α) n _ _ hL hC htp x y).2

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open Set Filter _root_.MeasureTheory
variable {X B : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

omit [CompleteSpace B] in
lemma gammaKernel_continuous (q k : ℕ) (hqk : q+k=5) {T r A : ℝ} (hr : 0 < r)
    (K : ℝ → X → X → B)
    (hKm : StronglyMeasurable (fun p : ℝ × X × X => K p.1 p.2.1 p.2.2))
    (hK : ∀ t ∈ Ioc 0 T, ∀ x y, ‖K t x y‖ ≤ A/t^k)
    (hKc : ∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => K t p.1 p.2)) :
    Continuous (fun p : X × X => gammaKernel K T r p.1 p.2) := by
  let ν := volume.restrict (Ioc 0 (T/r^2))
  let G := fun (p : X × X) (s : ℝ) => hodgeGammaWeight s • K (r^2*s) p.1 p.2
  let m := fun s : ℝ => A/r^(2*k)*(Real.exp (-s)*s^q)
  have hm : Integrable m ν := by
    have h := polynomialMoment_integrable q 0
    simp only [pow_zero,mul_one] at h
    exact (h.mono_set (fun _ h => h.1)).const_mul _
  have hst (s : ℝ) (hs : s ∈ Ioc 0 (T/r^2)) : r^2*s ∈ Ioc 0 T :=
    ⟨mul_pos (sq_pos_of_pos hr) hs.1,by
      have h := (le_div_iff₀ (sq_pos_of_pos hr)).mp hs.2
      simpa only [mul_comm] using h⟩
  have hGm (p : X × X) : AEStronglyMeasurable (G p) ν :=
    hodgeGammaWeight_continuous.aestronglyMeasurable.smul
      ((hKm.comp_measurable (show Measurable (fun s : ℝ => (r^2*s,p.1,p.2)) by fun_prop)).aestronglyMeasurable)
  have hGb (p : X × X) : ∀ᵐ s ∂ν, ‖G p s‖ ≤ m s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hb : VolterraBounds.weight 0 (r^2*s) p.1 p.2 * ‖K (r^2*s) p.1 p.2‖ ≤ A/(r^2*s)^k := by
      simpa only [VolterraBounds.weight,pow_zero,one_mul] using hK _ (hst s hs) p.1 p.2
    simpa only [VolterraBounds.weight,pow_zero,one_mul,mul_one] using
      weighted_gamma_integrand q k 0 hqk hr hs.1 K p.1 p.2 hb
  have hGc : ∀ᵐ s ∂ν, Continuous (fun p => G p s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact continuous_const.smul (hKc _ (hst s hs))
  exact (continuous_of_dominated hGm hGb hm hGc).const_smul (1/120 : ℝ)

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldLocalization ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
omit [SecondCountableTopology X] [BorelSpace X] in
lemma globalLeading_gamma_continuous {T L r : ℝ} (hr : 0 < r)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T L (globalLeading J α ht A E)) :
    Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r p.1 p.2) := by
  let := geometricMetricSpace J α hs ht
  apply HodgeKernelBounds.gammaKernel_continuous 3 2 (by norm_num) hr _ hL.measurable
  · intro t htp x y
    simpa only [VolterraBounds.weight,pow_zero,one_mul] using hL.sup t htp x y
  · intro t htp
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (globalLeading_continuousAt A J α hs ht E hE htp.1 p.1 p.2).comp
      (continuous_const.prodMk continuous_id).continuousAt

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

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
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open Set Filter _root_.MeasureTheory
variable {X B : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

lemma gammaKernel_pairing_iterated (μ : Measure X) [IsFiniteMeasure μ]
    (q k : ℕ) (hqk : q+k=5) {T r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    (K : ℝ → X → X → B)
    (hKm : StronglyMeasurable (fun p : ℝ × X × X => K p.1 p.2.1 p.2.2))
    (hK : ∀ t ∈ Ioc 0 T, ∀ x y, ‖K t x y‖ ≤ A/t^k)
    (Θ : X × X → B →L[ℝ] ℝ) (hΘm : StronglyMeasurable Θ)
    {M : ℝ} (hM : 0 ≤ M) (hΘ : ∀ p, ‖Θ p‖ ≤ M) :
    (∫ x, ∫ y, Θ (x,y) (gammaKernel K T r x y) ∂μ ∂μ) =
      (1/120 : ℝ) * ∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s *
        (∫ x, ∫ y, Θ (x,y) (K (r^2*s) x y) ∂μ ∂μ) := by
  have hg : ∃ C : ℝ, ∀ x y, ‖gammaKernel K T r x y‖ ≤ C := by
    refine ⟨((1/120:ℝ)*A*2^(0-1)*(moment q 1+moment (q+0) 1))/r^(2*k),?_⟩
    intro x y
    have hb := gammaKernel_bound q k 0 hqk hr hA K x y
      ((hKm.comp_measurable (show Measurable (fun s : ℝ => (r^2*s,x,y)) by fun_prop)).aestronglyMeasurable)
      (fun t ht => by simpa only [VolterraBounds.weight,pow_zero,one_mul] using hK t ht x y)
    simpa only [VolterraBounds.weight,pow_zero,one_mul] using hb.2
  obtain ⟨C,hC⟩ := hg
  have higm : StronglyMeasurable (fun p : X × X => Θ p (gammaKernel K T r p.1 p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (hΘm.prodMk (gammaKernel_measurable K hKm T r))
  have hig : Integrable (fun p : X × X => Θ p (gammaKernel K T r p.1 p.2)) (μ.prod μ) := by
    apply Integrable.of_bound higm.aestronglyMeasurable (M*C)
    exact Eventually.of_forall fun p => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hΘ p) (hC p.1 p.2) (norm_nonneg _) hM)
  rw [integral_integral hig,gammaKernel_pairing (μ.prod μ) q k hqk hr K hKm hK Θ hΘm hM hΘ]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hst : r^2*s ∈ Ioc 0 T := ⟨mul_pos (sq_pos_of_pos hr) hs.1,by
    have h := (le_div_iff₀ (sq_pos_of_pos hr)).mp hs.2
    simpa only [mul_comm] using h⟩
  congr 1
  apply integral_prod
  apply Integrable.of_bound
    ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (hΘm.prodMk (hKm.comp_measurable (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
    (M*(A/(r^2*s)^k))
  exact Eventually.of_forall fun p => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (hΘ p) (hK _ hst p.1 p.2) (norm_nonneg _) hM)

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaWeakAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian
include hs hE in
lemma gammaKernel_weakAction (q k : ℕ) (hqk : q+k=5) {T r H : ℝ} (hr : 0 < r) (hH : 0 ≤ H)
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hKm : VolterraKernel.MeasurableKernel K)
    (hK : ∀ t ∈ Ioc 0 T, ∀ x y, ‖K t x y‖ ≤ H/t^k)
    (v : X → FrameSpace A) (hv : Continuous v) (a : TwoForm X) (ha : IsSmooth a) :
    (∫ y, ∫ x, framePairing A J α ht E a x
      (HodgeKernelBounds.gammaKernel K T r x y (v y))
        ∂geometricVolume A J α ∂geometricVolume A J α) =
      (1/120:ℝ) * ∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s *
        kernelWeakAction A J α ht E K v a (r^2*s) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  obtain ⟨V₀,hV₀⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  let V := max V₀ 0
  have hV : 0 ≤ V := le_max_right _ _
  have hvB (y : X) : ‖v y‖ ≤ V := (hV₀ y (mem_univ y)).trans (le_max_left _ _)
  let Θ : X × X → (FrameSpace A →L[ℝ] FrameSpace A) →L[ℝ] ℝ := fun p =>
    (framePairing A J α ht E a p.2).comp ((ContinuousLinearMap.apply ℝ (FrameSpace A)) (v p.1))
  have hΘc : Continuous Θ :=
    ((framePairing_continuous A J α hs ht E hE a ha).comp continuous_snd).clm_comp
      ((ContinuousLinearMap.apply ℝ (FrameSpace A)).continuous.comp (hv.comp continuous_fst))
  have hΘb (p : X × X) : ‖Θ p‖ ≤ B*V := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB hV)
    intro L
    calc
      _ ≤ ‖framePairing A J α ht E a p.2‖ * ‖L (v p.1)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ B*(‖L‖*V) := mul_le_mul (hφ p.2)
        ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hvB p.1) (norm_nonneg _)))
        (norm_nonneg _) hB
      _ = _ := by ring
  have hh := HodgeKernelBounds.gammaKernel_pairing_iterated (geometricVolume A J α) q k hqk hr hH
    (fun t x y => K t y x)
    (hKm.comp_measurable (show Measurable (fun p : ℝ × X × X => (p.1,p.2.2,p.2.1)) by fun_prop))
    (fun t ht x y => hK t ht y x) Θ hΘc.stronglyMeasurable (mul_nonneg hB hV) hΘb
  exact hh

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

include hE in
lemma kernelWeakAction_gamma_integrable {T H r : ℝ} (hr : 0 < r)
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (v : X → FrameSpace A) (hv : Continuous v) (a : TwoForm X) (ha : IsSmooth a) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s * kernelWeakAction A J α ht E K v a (r^2*s))
      (Ioc 0 (T/r^2)) := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨V₀,hV₀⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  let V := max V₀ 0
  have hV : 0 ≤ V := le_max_right _ _
  have hvB (y : X) : ‖v y‖ ≤ V := (hV₀ y (mem_univ y)).trans (le_max_left _ _)
  obtain ⟨B,_hB,hb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE K hK a ha hV
  have hst (s : ℝ) (hs : s ∈ Ioc 0 (T/r^2)) : r^2*s ∈ Ioc 0 T :=
    ⟨mul_pos (sq_pos_of_pos hr) hs.1,by
      have h := (le_div_iff₀ (sq_pos_of_pos hr)).mp hs.2
      simpa only [mul_comm] using h⟩
  have hm := (kernelInputTest_time_measurable A J α hs ht E hE K hK.measurable a ha v
    hv.stronglyMeasurable).comp_measurable (show Measurable (fun s : ℝ => r^2*s) by fun_prop)
  have hi : IntegrableOn (fun s : ℝ => hodgeGammaWeight s * kernelInputTest A J α ht E K a (r^2*s) v)
      (Ioc 0 (T/r^2)) := by
    apply ((hodgeGammaWeight_integrable.mono_set (fun _ hx => hx.1)).mul_const B).mono'
      (hodgeGammaWeight_continuous.stronglyMeasurable.mul hm).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsp
    change ‖hodgeGammaWeight s * kernelInputTest A J α ht E K a (r^2*s) v‖ ≤ hodgeGammaWeight s * B
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hodgeGammaWeight_nonneg hsp.1.le)]
    exact mul_le_mul_of_nonneg_left (hb _ (hst s hsp) v hvB) (hodgeGammaWeight_nonneg hsp.1.le)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsp
  rw [kernelInputTest_eq_weakAction A J α hs ht E hE K hK a ha (hst s hsp) v]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeContinuousResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

section
section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE D hD in
lemma same_resolvent_continuous_spatial (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
      (∀ r : ℝ, 0 < r →
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r p.1 p.2) ∧
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r p.1 p.2)) ∧
      (∀ r : ℝ, 0 < r → ∀ x y : X,
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y‖ ≤
            ((1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1))/r^4 ∧
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y‖ ≤
            ((1/120:ℝ)*(4*L*C)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1))/r^2) ∧
      ∀ v : X → FrameSpace A, Continuous v → ∃ f : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪f,smoothL2 A J α hs ht true a⟫ =
            ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
        ∀ r : ℝ, 0 < r → ∀ a : PreL2 A J α hs ht true,
          ⟪(hodgeRegularization A J α hs ht r ^ 2) f,smoothL2 A J α hs ht true a⟫ =
            (∫ y, ∫ x, framePairing A J α ht E a.val x
              (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y (v y))
                ∂geometricVolume A J α ∂geometricVolume A J α) +
            (∫ y, ∫ x, framePairing A J α ht E a.val x
              (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y (v y))
                ∂geometricVolume A J α ∂geometricVolume A J α) +
            ⟪hodgeGammaTailAction A J α hs ht D hD T r f,smoothL2 A J α hs ht true a⟫ := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨T,L,C,hT,hT1,hL,hC,hEc,hpair⟩ := same_resolvent_continuous_data A J α hs ht E hE D hD n
  have hL0 := hL.weight_zero (geometricVolume A J α)
  have hC0 := hC.weight_zero (geometricVolume A J α)
  have hErr : VolterraKernel.HeatBound (geometricVolume A J α) 0 T (4*T*L*C)
      (globalError J α ht A E T) := by
    simpa only [globalError] using VolterraKernel.convolution_heatBound (geometricVolume A J α) 0 hT.le _ _ hL0 hC0
  have hEm : VolterraKernel.MeasurableKernel (globalError J α ht A E T) := by
    simpa only [globalError] using VolterraKernel.convolution_measurable (geometricVolume A J α) _ _ hL.measurable hC.measurable
  have hLsup (t : ℝ) (htp : t ∈ Ioc 0 T) (x y : X) :
      ‖globalLeading J α ht A E t x y‖ ≤ L/t^2 := by
    simpa only [VolterraBounds.weight,pow_zero,one_mul] using hL0.sup t htp x y
  have hEsup (t : ℝ) (htp : t ∈ Ioc 0 T) (x y : X) :
      ‖globalError J α ht A E T t x y‖ ≤ (4*L*C)/t^1 := by
    simpa only [globalError,VolterraBounds.weight,pow_zero,one_mul,pow_one] using
      (VolterraKernel.convolution_sup (geometricVolume A J α) 0 _ _ hL0 hC0 htp x y).2
  refine ⟨T,L,C,hT,hT1,hL,hC,?_,?_,?_⟩
  · intro r hr
    refine ⟨globalLeading_gamma_continuous A J α hs ht E hE hr hL0,?_⟩
    exact HodgeKernelBounds.gammaKernel_continuous 4 1 (by norm_num) hr _ hEm hEsup hEc
  · intro r hr x y
    have h := globalGamma_bounds_of A J α hs ht E n hL hC hr x y
    exact ⟨h.1.2,h.2.2⟩
  · intro v hv
    obtain ⟨f,hf,hfr,_htail⟩ := hpair v hv
    refine ⟨f,hf,?_⟩
    intro r hr a
    rw [hfr r hr a,
      gammaKernel_weakAction A J α hs ht E hE 3 2 (by norm_num) hr hL.nonneg _ hL.measurable hLsup v hv a.val a.property,
      gammaKernel_weakAction A J α hs ht E hE 4 1 (by norm_num) hr
        (by have := hL.nonneg; have := hC.nonneg; positivity) _ hEm hEsup v hv a.val a.property]
    simp_rw [mul_add]
    rw [integral_add (kernelWeakAction_gamma_integrable A J α hs ht E hE hr _ hL0 v hv a.val a.property)
      (kernelWeakAction_gamma_integrable A J α hs ht E hE hr _ hErr v hv a.val a.property)]
    ring

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothSpatial
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
omit [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] in
lemma smoothL2_eq_of_framePairings (f : L2 A J α hs ht true)
    (b : PreL2 A J α hs ht true)
    (hf : ∀ a : PreL2 A J α hs ht true,
      ⟪f,smoothL2 A J α hs ht true a⟫ = ∫ y, framePairing A J α ht E a.val y
        (frameEncode J α ht A E y (b.val y)) ∂geometricVolume A J α) :
    f = smoothL2 A J α hs ht true b := by
  apply ext_inner_right ℝ
  intro v
  refine (smoothL2_dense A J α hs ht true).induction_on v
    (_root_.isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)) ?_
  intro a
  rw [hf a,(smoothL2 A J α hs ht true).inner_map_map,preL2_inner]
  unfold l2Pairing
  apply integral_congr_ae
  filter_upwards [] with y
  rw [framePairing_encode A J α ht E hE]
  exact MetricForms.pairing_symm _ _ _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeSmoothResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE D hD in
lemma same_resolvent_smooth_spatial_oai (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
      (∀ r : ℝ, 0 < r →
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r p.1 p.2) ∧
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r p.1 p.2)) ∧
      (∀ r : ℝ, 0 < r → ∀ x y : X,
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y‖ ≤
            ((1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1))/r^4 ∧
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y‖ ≤
            ((1/120:ℝ)*(4*L*C)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1))/r^2) ∧
      ∀ b : PreL2 A J α hs ht true,
        ∀ r : ℝ, 0 < r → ∀ a : PreL2 A J α hs ht true,
          ⟪(hodgeRegularization A J α hs ht r ^ 2) (smoothL2 A J α hs ht true b),smoothL2 A J α hs ht true a⟫ =
            (∫ y, ∫ x, framePairing A J α ht E a.val x
              (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y (frameEncode J α ht A E y (b.val y)))
                ∂geometricVolume A J α ∂geometricVolume A J α) +
            (∫ y, ∫ x, framePairing A J α ht E a.val x
              (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y (frameEncode J α ht A E y (b.val y)))
                ∂geometricVolume A J α ∂geometricVolume A J α) +
            ⟪hodgeGammaTailAction A J α hs ht D hD T r (smoothL2 A J α hs ht true b),smoothL2 A J α hs ht true a⟫ := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,L,C,hT,hT1,hL,hC,hcont,hbound,hpair⟩ :=
    same_resolvent_continuous_spatial A J α hs ht E hE D hD n
  refine ⟨T,L,C,hT,hT1,hL,hC,hcont,hbound,?_⟩
  intro b
  obtain ⟨f,hf,hfr⟩ := hpair (fun y => frameEncode J α ht A E y (b.val y))
    (frameEncode_section_smooth J α ht A E hE hs b.val b.property).continuous
  have he := smoothL2_eq_of_framePairings A J α hs ht E hE f b hf
  subst f
  exact hfr

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_smooth_spatial_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_smooth_spatial_oai.{u_1}
