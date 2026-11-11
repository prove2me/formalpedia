-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral_local
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:53:17.748858+00:00
-- url     : https://prove2.me/submissions/a3d55014-1873-4e48-b3bc-e9c4914fc25f

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc018
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_actual_cutoff_time_integral

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open Set Filter
open scoped Manifold ContDiff Topology
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma exists_compact_smooth_extension {U K : Set V} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : V → W} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : V → W, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨O,hO,hKO,hOU,hOc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  have hKi : K ⊆ interior (closure O) := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hO.mem_nhds (hKO hx)) subset_closure)
  obtain ⟨φ,hφone,hφzero,_⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,V)) hK.isClosed hKi (n := ⊤)
  have hφsupp : tsupport (φ : V → ℝ) ⊆ closure O := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (hφzero x hn)
  have hgsub : tsupport (fun x => φ x • f x) ⊆ closure O := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (by simp [hφzero x hn])
  refine ⟨fun x => φ x • f x,SchwartzCutoff.smooth hU hf
    (contMDiff_iff_contDiff.mp φ.contMDiff) (hφsupp.trans hOU),
    hOc.of_isClosed_subset (isClosed_tsupport _) hgsub,hgsub.trans hOU,?_⟩
  intro x hx
  filter_upwards [hφone.filter_mono (nhds_le_nhdsSet hx)] with y hy
  simp [hy]

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactTimeIntegral
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
attribute [local irreducible] normalGauge normalFirst

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.compactTimeIntegralPatchMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.compactTimeIntegralPatchMetricTensorNormedSpace
lemma actual_cutoff_time_integral_local_oai (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q : Space) (χ : Space → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    {U : Set Space} (hU : IsOpen U) (hχU : tsupport χ ⊆ U)
    {t : ℝ} (htpos : 0 < t) (u : W)
    (η : Space → W) (hη : ContDiffOn ℝ ∞ η U) :
    HasDerivAt (fun s => ∫ z, normalDensity g B (q,z) * ⟪η z,
      normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫)
      (∫ z, normalDensity g B (q,z) * ⟪η z,
        deriv (fun s => normalGauge J α ht p D g B (q,z)
          (χ z • NormalHeatResidual.modelSection s u z)) t⟫) t := by
  obtain ⟨η',hη',hc,_,he⟩ := exists_compact_smooth_extension hU hχc hχU hη
  have hi := actual_cutoff_time_integral J α ht p D g B hg hB q χ hχ htpos u η' hη'.continuous hc
  have hpair (s : ℝ) (z : Space) :
      ⟪η' z,normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫ =
      ⟪η z,normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)⟫ := by
    by_cases hz : z ∈ tsupport χ
    · rw [(he z hz).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hd (z : Space) :
      ⟪η' z,deriv (fun s => normalGauge J α ht p D g B (q,z)
        (χ z • NormalHeatResidual.modelSection s u z)) t⟫ =
      ⟪η z,deriv (fun s => normalGauge J α ht p D g B (q,z)
        (χ z • NormalHeatResidual.modelSection s u z)) t⟫ := by
    by_cases hz : z ∈ tsupport χ
    · rw [(he z hz).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  simpa only [hpair,hd] using hi

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral_local_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_time_integral_local_oai.{u_1}
