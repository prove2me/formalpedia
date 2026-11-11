-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.actual_complement_packing_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:24.272726+00:00
-- url     : https://prove2.me/submissions/f16101bd-0573-43b3-ab6d-40cc792592f7

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_actual_large_normal_packing_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_actual_radial_primitive_family_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_quadric_exact_affine_moser_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_largeCouplingPrimitive_invertible_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_exact_fibre_embedding_into_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCovectorPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem staticPullbackOneForm_fderiv {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) (u v : F) :
    fderiv ℝ (staticPullbackOneForm α g) x u v =
      fderiv ℝ α (g x) (fderiv ℝ g x u) (fderiv ℝ g x v) +
        α (g x) (fderiv ℝ (fderiv ℝ g) x u v) := by
  have hd := ((ha.differentiableAt (by simp)).hasFDerivAt.comp x
    (hg.differentiableAt (by simp)).hasFDerivAt).clm_comp
      ((hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  rw [show fderiv ℝ (staticPullbackOneForm α g) x = _ from hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem staticPullbackOneForm_exterior {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    euclideanExteriorOneForm (staticPullbackOneForm α g) x =
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.bilinearComp_apply,staticPullbackOneForm_fderiv ha hg]
  have hs := hg.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hs.eq u v]
  ring


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_SpatialOneForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_add _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_inside _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_outside _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_vertical _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartDifferential_inverse {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    (chartDifferential (E := E) c ((extChartAt 𝓘(ℝ,E) c).symm y)).inverse =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c).symm y := by
  apply ContinuousLinearMap.inverse_eq
  · simpa only [mfld_simps,chartDifferential] using!
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ,E)) hy)
  · simpa only [mfld_simps,chartDifferential] using!
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hy)


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem euclideanPullbackOneForm_chart {α : ℝ → ManifoldOneForm E M} {g : F → M}
    {p : ℝ × F} {c : M} (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
    (hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    euclideanPullbackOneForm α g p =
      (chartOneForm (α p.1) c (extChartAt 𝓘(ℝ,E) c (g p.2))).comp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2) := by
  have hd := ((mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)).hasMFDerivAt.comp p.2 hg.hasMFDerivAt)
  let A : F →L[ℝ] E :=
    (chartDifferential c (g p.2)).comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ g) A p.2 :=
    hasMFDerivAt_iff_hasFDerivAt.mp hd
  have hdf := hf.fderiv
  dsimp only [A,chartDifferential] at hdf
  rw [hdf]
  have hC : (chartDifferential (E := E) c (g p.2)).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hc using 1
    all_goals try with_reducible_and_instances rfl
  ext v
  change α p.1 (g p.2) _ = α p.1 ((extChartAt 𝓘(ℝ,E) c).symm
    (extChartAt 𝓘(ℝ,E) c (g p.2))) _
  rw [(extChartAt 𝓘(ℝ,E) c).left_inv hc]
  change _ = α p.1 (g p.2) ((chartDifferential c (g p.2)).inverse
    (chartDifferential c (g p.2) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2 v)))
  erw [hC.inverse_apply_self]
  rfl

theorem euclideanPullbackOneForm_contDiffAt
    {α : ℝ → ManifoldOneForm E M} {g : F → M} {p : ℝ × F}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) :
    ContDiffAt ℝ ∞ (euclideanPullbackOneForm α g) p := by
  let c := g p.2
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2 := hch.contDiffAt
  have hcoord : ContDiffAt ℝ ∞ (fun q : ℝ × F => (q.1,extChartAt 𝓘(ℝ,E) c (g q.2))) p :=
    contDiffAt_fst.prodMk (hs.comp p contDiffAt_snd)
  have hform := ((hα c).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) c).map_source hc⟩)).comp p hcoord
  have hder := (hs.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp p contDiffAt_snd
  have hsm := hform.clm_comp hder
  apply hsm.congr_of_eventuallyEq
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
    continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
  exact euclideanPullbackOneForm_chart (hq.mdifferentiableAt (by simp)) hqc


end

open scoped ContDiff Manifold Topology
open MeasureTheory Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_FixedSpatialIntegral
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem euclideanExteriorOneForm_add {α β : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    euclideanExteriorOneForm (α+β) x =
      euclideanExteriorOneForm α x + euclideanExteriorOneForm β x := by
  rw [euclideanExteriorOneForm,fderiv_add hα hβ]
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,add_apply]
  ring



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ChartSupportedDensity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem SmoothOneFormFamily.spatial_smooth {α : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) (p : P) (c : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    ContDiffAt ℝ ∞ (chartOneForm (α p) c) y :=
  ((hα c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds ⟨mem_univ p,hy⟩)).comp y
    (contDiffAt_const.prodMk contDiffAt_id)


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology ENNReal
open Set Function MeasureTheory
open Filter
open scoped Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,E) hK.isClosed hKL (n := ⊤)
  have hs : tsupport (χ : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  exact ⟨χ,χ.contMDiff.contDiff,hL.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hLU,hχ1,hχrange⟩

theorem exists_smooth_compact_extension {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ x, χ x ∈ Icc 0 1) ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧
      ContDiff ℝ ∞ (fun x => χ x • f x) ∧
      HasCompactSupport (fun x => χ x • f x) ∧
      (∀ᶠ x in 𝓝ˢ K, χ x • f x = f x) := by
  obtain ⟨χ,hχ,hχc,hχU,hχ1,hχrange⟩ := exists_smooth_cutoff hK hU hKU
  have hg : ContDiff ℝ ∞ (fun x => χ x • f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul ((hf x hx).contDiffAt (hU.mem_nhds hx))
    · have hn : x ∉ tsupport χ := fun h => hx (hχU h)
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hn)
      apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp only [hy,zero_smul,Pi.zero_apply]
  have hs : tsupport (fun x => χ x • f x) ⊆ tsupport χ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    apply hx
    change χ x • f x = 0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
  refine ⟨χ,hχ,hχc,hχU,hχrange,hχ1,hg,
    hχc.of_isClosed_subset (isClosed_tsupport _) hs,?_⟩
  filter_upwards [hχ1] with x hx
  rw [hx,one_smul]

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Kahler_PhaseArea
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Topology
section
variable {ι : Type*} [Fintype ι]

theorem phaseArea_apply (v w : PlanePhase ι) :
    phaseArea v w = ∑ i, ((v i).1*(w i).2-(v i).2*(w i).1) := by
  simp [phaseArea]

theorem phaseArea_skew (v w : PlanePhase ι) : phaseArea v w = -phaseArea w v := by
  simp only [phaseArea_apply,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [DecidableEq ι]

@[simp] theorem phaseArea_single_right (v : PlanePhase ι) (i : ι) (w : Plane) :
    phaseArea v (Pi.single i w) = planarArea (v i) w := by
  classical
  rw [phaseArea_apply,Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [hbi]
  · simp

@[simp] theorem phaseArea_single_left (i : ι) (v : Plane) (w : PlanePhase ι) :
    phaseArea (Pi.single i v) w = planarArea v (w i) := by
  classical
  rw [phaseArea_apply,Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [hbi]
  · simp

end
section

variable {ι : Type*} [Fintype ι]

theorem phaseDot_symm (z v : PlanePhase ι) : phaseDot z v = phaseDot v z := by
  simp only [phaseDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem phaseSq_hasFDerivAt (z : PlanePhase ι) :
    HasFDerivAt phaseSq ((2:ℝ) • phaseDot z) z := by
  have h := phaseDot.hasFDerivAt.clm_apply (hasFDerivAt_id z)
  apply h.congr_fderiv
  ext v
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.flip_apply,id_eq,
    smul_apply,smul_eq_mul]
  rw [phaseDot_symm v z]
  ring

@[simp] theorem phaseSq_fderiv (z v : PlanePhase ι) :
    fderiv ℝ phaseSq z v = 2 * phaseDot z v := by
  rw [(phaseSq_hasFDerivAt z).fderiv]
  rfl

theorem phaseArea_self (z : PlanePhase ι) : phaseArea z z = 0 := by
  have h := phaseArea_skew z z
  linarith

end
section

variable {ι : Type*} [Fintype ι]

theorem fsBallDifferential_apply (a : ℝ) (z v : PlanePhase ι) :
    fsBallDifferential a z v = (Real.sqrt a / Real.sqrt (1+phaseSq z)) •
      (v-(phaseDot z v/(1+phaseSq z)) • z) := by
  simp only [fsBallDifferential,smul_apply,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  simp only [div_eq_mul_inv]
  rw [mul_comm ((1+phaseSq z)⁻¹) (phaseDot z v)]

theorem fsBallMap_hasFDerivAt (a : ℝ) (z : PlanePhase ι) :
    HasFDerivAt (fsBallMap a) (fsBallDifferential a z) z := by
  have hs : HasFDerivAt (fun y : PlanePhase ι => 1+phaseSq y)
      ((2:ℝ) • phaseDot z) z := by
    exact (phaseSq_hasFDerivAt z).const_add 1
  have ht := hs.sqrt (fs_den_pos z).ne'
  have hc := ((hasDerivAt_inv (Real.sqrt_pos.2 (fs_den_pos z)).ne').comp_hasFDerivAt z ht).const_mul (Real.sqrt a)
  have hc' : HasFDerivAt (fun y : PlanePhase ι => Real.sqrt a/Real.sqrt (1+phaseSq y))
      ((-(Real.sqrt a / Real.sqrt (1+phaseSq z))/(1+phaseSq z)) • phaseDot z) z := by
    change HasFDerivAt (fun y : PlanePhase ι => Real.sqrt a*(Real.sqrt (1+phaseSq y))⁻¹) _ z
    apply hc.congr_fderiv
    ext v
    simp only [smul_apply,smul_eq_mul,smul_smul]
    have hq := Real.sq_sqrt (fs_den_pos z).le
    field_simp [(Real.sqrt_pos.2 (fs_den_pos z)).ne',(fs_den_pos z).ne']
    rw [hq]
  apply (hc'.smul (hasFDerivAt_id z)).congr_fderiv
  ext v i <;>
    simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,id_eq,fsBallDifferential_apply,
      Pi.add_apply,Pi.smul_apply,Pi.sub_apply,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,Prod.fst_sub,Prod.snd_sub,smul_eq_mul] <;> ring

@[simp] theorem fsBallMap_fderiv (a : ℝ) (z v : PlanePhase ι) :
    fderiv ℝ (fsBallMap a) z v = (Real.sqrt a / Real.sqrt (1+phaseSq z)) •
      (v-(phaseDot z v/(1+phaseSq z)) • z) := by
  rw [(fsBallMap_hasFDerivAt a z).fderiv,fsBallDifferential_apply]

theorem affineFSPrimitive_smooth (a : ℝ) :
    ContDiff ℝ ∞ (affineFSPrimitive a : PlanePhase ι → _) := by
  have hc : ContDiff ℝ ∞ (fun z : PlanePhase ι => a/(2*(1+phaseSq z))) :=
    contDiff_const.div (contDiff_const.mul (contDiff_const.add phaseSq_smooth))
      (fun z => mul_ne_zero (by norm_num) (fs_den_pos z).ne')
  exact hc.smul (phaseArea (ι := ι)).contDiff

@[simp] theorem phaseDot_J_right (z v : PlanePhase ι) :
    phaseDot z (phaseJ v) = -phaseArea z v := by
  simp only [phaseDot_apply,phaseArea_apply,phaseJ_apply,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem phaseDot_J_left (z v : PlanePhase ι) :
    phaseDot (phaseJ z) v = phaseArea z v := by
  rw [phaseDot_symm,phaseDot_J_right,phaseArea_skew v z,neg_neg]

@[simp] theorem phaseArea_J_right (z v : PlanePhase ι) :
    phaseArea z (phaseJ v) = phaseDot z v := by
  simp only [phaseDot_apply,phaseArea_apply,phaseJ_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem phaseArea_J_left (z v : PlanePhase ι) :
    phaseArea (phaseJ z) v = -phaseDot z v := by
  rw [phaseArea_skew,phaseArea_J_right,phaseDot_symm]

@[simp] theorem phaseDot_J_J (z v : PlanePhase ι) :
    phaseDot (phaseJ z) (phaseJ v) = phaseDot z v := by
  rw [phaseDot_J_left,phaseArea_J_right]

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldMapDifferential
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_inside _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_outside _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_vertical _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped Manifold
open scoped ContDiff Topology
open Set Function Manifold
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartOneForm_manifoldPullback {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target) :
    chartOneForm (manifoldPullbackOneForm α e p.1) b p.2 =
      euclideanPullbackOneForm α (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := ((he.mdifferentiable (by simp) _).hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackOneForm,hd,chartOneForm,manifoldPullbackOneForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v
  rfl

theorem manifoldPullbackOneForm_smooth {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (b : N) :
    ContDiffOn ℝ ∞ (fun q : ℝ × F => chartOneForm (manifoldPullbackOneForm α e q.1) b q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,F) b).target) := by
  intro p hp
  have hg := he.contMDiffAt.comp p.2 ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2))
  apply ((euclideanPullbackOneForm_contDiffAt hα hg).congr_of_eventuallyEq _).contDiffWithinAt
  have hh := continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2)
  filter_upwards [hh] with q hq
  exact chartOneForm_manifoldPullback he hq

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem euclidean_manifold_pullback_germ {α : ManifoldOneForm E M}
    {g : F → M} {x : F} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x)
    {c : M} (hc : g x ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    (fun y => euclideanPullbackOneForm (fun _ => α) g (0,y)) =ᶠ[𝓝 x]
      staticPullbackOneForm (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c ∘ g) := by
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  filter_upwards [hg',hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)] with y hy hcy
  exact euclideanPullbackOneForm_chart (α := fun _ => α) (p := (0,y))
    (hy.mdifferentiableAt (by simp)) hcy

theorem euclidean_manifold_pullback_chart_exterior {α : ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    {g : F → M} {x : F} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x)
    {c : M} (hc : g x ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    euclideanExteriorOneForm (fun y => euclideanPullbackOneForm (fun _ => α) g (0,y)) x =
      (euclideanExteriorOneForm (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c (g x))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) x) (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) x) := by
  have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
    (by simpa only [extChartAt_source] using hc)
  have hgc : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) x := (ho.comp x hg).contDiffAt
  have ha := (hα c).contDiffAt ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds
    ((extChartAt 𝓘(ℝ,E) c).map_source hc))
  have he := euclidean_manifold_pullback_germ (α := α) hg hc
  calc
    _ = euclideanExteriorOneForm
        (staticPullbackOneForm (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c ∘ g)) x := by
      unfold euclideanExteriorOneForm
      rw [he.fderiv_eq]
    _ = _ := staticPullbackOneForm_exterior ha hgc

theorem euclidean_manifold_pullback_exterior {α : ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    {g : F → M} {x : F} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x) :
    euclideanExteriorOneForm (fun y => euclideanPullbackOneForm (fun _ => α) g (0,y)) x =
      (manifoldExteriorOneForm α (g x)).bilinearComp
        (manifoldMapDifferential (E := E) (F := F) g x)
        (manifoldMapDifferential (E := E) (F := F) g x) := by
  let c := g x
  have hc : g x ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have ho := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)
  let A : F →L[ℝ] E := (chartDifferential c (g x)).comp
    (manifoldMapDifferential (E := E) (F := F) g x)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ g) A x :=
    hasMFDerivAt_iff_hasFDerivAt.mp
      (ho.hasMFDerivAt.comp x (hg.mdifferentiableAt (by simp)).hasMFDerivAt)
  have hd := hf.fderiv
  have hfd : fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) x =
      (chartDifferential (E := E) c (g x)).comp
        (manifoldMapDifferential (E := E) (F := F) g x) := hd
  rw [euclidean_manifold_pullback_chart_exterior hα hg hc,hfd]
  rfl

variable {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem manifold_pullback_exterior {α : ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    {g : N → M} (hg : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g) (b : N) :
    manifoldExteriorOneForm (E := F) (M := N)
      (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =
      manifoldPullbackTwoForm (E := E) (F := F) (fun _ => manifoldExteriorOneForm α) g 0 b := by
  let y := extChartAt 𝓘(ℝ,F) b b
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy : y ∈ (extChartAt 𝓘(ℝ,F) b).target := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he : (extChartAt 𝓘(ℝ,F) b).symm y=b := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hc : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y :=
    hg.contMDiffAt.comp y hi
  have hh : chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =ᶠ[𝓝 y]
      fun z => euclideanPullbackOneForm (fun _ => α) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (0,z) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy] with z hz
    exact chartOneForm_manifoldPullback (α := fun _ => α) (b := b) (p := (0,z)) hg hz
  have hder : euclideanExteriorOneForm
      (chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b) y =
      (manifoldExteriorOneForm α (g b)).bilinearComp
        (manifoldMapDifferential (E := E) (F := F) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)
        (manifoldMapDifferential (E := E) (F := F) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y) := by
    calc
      _ = euclideanExteriorOneForm
          (fun z => euclideanPullbackOneForm (fun _ => α) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (0,z)) y := by
        unfold euclideanExteriorOneForm
        rw [hh.fderiv_eq]
      _ = _ := by simpa only [Function.comp_apply,he] using euclidean_manifold_pullback_exterior hα hc
  have hd := mfderiv_comp y ((hg.mdifferentiable (by simp)) _)
    (hi.mdifferentiableAt (by simp))
  have hD : manifoldMapDifferential (E := E) (F := F)
      (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y =
      (manifoldMapDifferential (E := E) (F := F) g b).comp
        (chartDifferential (E := F) b b).inverse := by
    change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y = _
    rw [hd]
    rw [← chartDifferential_inverse hy]
    change (manifoldMapDifferential (E := E) (F := F) g
      ((extChartAt 𝓘(ℝ,F) b).symm y)).comp
      (chartDifferential (E := F) b ((extChartAt 𝓘(ℝ,F) b).symm y)).inverse = _
    rw [he]
  have H : (chartDifferential (E := F) b b).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,F)) hb using 1
    all_goals try with_reducible_and_instances rfl
  change (euclideanExteriorOneForm
    (chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b) y).bilinearComp
      (chartDifferential (E := F) b b) (chartDifferential (E := F) b b)=_
  rw [hder,hD]
  ext u v
  change manifoldExteriorOneForm α (g b)
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g b ((chartDifferential (E := F) b b).inverse (chartDifferential (E := F) b b u)))
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g b ((chartDifferential (E := F) b b).inverse (chartDifferential (E := F) b b v)))=_
  rw [H.inverse_apply_self,H.inverse_apply_self]
  rfl

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vector_chartOneForm (α : E → E →L[ℝ] ℝ) (c y : E) :
    chartOneForm α c y=α y := by
  simp only [chartOneForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,ContinuousLinearMap.comp_id,id_eq]

theorem vector_exteriorOneForm (α : E → E →L[ℝ] ℝ) :
    manifoldExteriorOneForm α=euclideanExteriorOneForm α := by
  funext y
  simp only [manifoldExteriorOneForm,
    chartDifferential,extChartAt_model_space_eq_id,PartialEquiv.refl_coe,
    mfderiv_eq_fderiv,fderiv_id,id_eq]
  rw [show chartOneForm α y=α from funext (vector_chartOneForm α y)]
  ext v w
  rfl

theorem vector_oneForm_smooth {α : E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α) :
    SmoothOneFormFamily (fun _ : ℝ => α) := by
  intro c
  simpa only [vector_chartOneForm,Function.comp_def] using
    (hα.comp contDiff_snd).contDiffOn

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem phaseInclusion_smooth :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin m))) ∞ (phaseInclusion a) :=
  (affinePhase m).contDiff.contMDiff.comp (real_inclusion_contMDiff a)

theorem curveFSPrimitive_smooth (c : ℝ) :
    SmoothOneFormFamily (fun _ : ℝ => curveFSPrimitive a c) := by
  have hα : SmoothOneFormFamily (fun _ : ℝ =>
      (affineFSPrimitive c : PlanePhase (Option (Fin m)) → _)) :=
    vector_oneForm_smooth (affineFSPrimitive_smooth c)
  intro b
  exact manifoldPullbackOneForm_smooth (α := fun _ : ℝ =>
    (affineFSPrimitive c : PlanePhase (Option (Fin m)) → _))
    (phaseInclusion_smooth a) hα b

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldFormTransport
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_inside _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_outside _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold
open scoped ContDiff Manifold Topology

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartOneForm_manifoldPullback_at {α : ℝ → ManifoldOneForm E M} {e : N → M}
    {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target)
    (he : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) e ((extChartAt 𝓘(ℝ,F) b).symm p.2)) :
    chartOneForm (manifoldPullbackOneForm α e p.1) b p.2 =
      euclideanPullbackOneForm α (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := (he.hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackOneForm,hd,chartOneForm,manifoldPullbackOneForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v
  rfl

end

section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem parameterEuclideanPullbackOneForm_contDiffAt
    {α : P → ManifoldOneForm E M} {g : F → M} {p : P × F}
    (hα : ContDiffAt ℝ ∞
      (fun q : P × E => chartOneForm (α q.1) (g p.2) q.2)
      (p.1,extChartAt 𝓘(ℝ,E) (g p.2) (g p.2)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) :
    ContDiffAt ℝ ∞ (parameterEuclideanPullbackOneForm α g) p := by
  let c := g p.2
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2 := hch.contDiffAt
  have hcoord : ContDiffAt ℝ ∞ (fun q : P × F => (q.1,extChartAt 𝓘(ℝ,E) c (g q.2))) p :=
    contDiffAt_fst.prodMk (hs.comp p contDiffAt_snd)
  have hform := hα.comp p hcoord
  have hder := (hs.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp p contDiffAt_snd
  apply (hform.clm_comp hder).congr_of_eventuallyEq
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
    continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
  exact euclideanPullbackOneForm_chart (α := fun _ => α q.1) (p := (0,q.2))
    (hq.mdifferentiableAt (by simp)) hqc

end

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem euclidean_manifold_pullback_exterior_at {α : ManifoldOneForm E M}
    {g : F → M} {x : F} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x)
    (hα : ContDiffAt ℝ ∞ (chartOneForm α (g x)) (extChartAt 𝓘(ℝ,E) (g x) (g x))) :
    euclideanExteriorOneForm (fun y => euclideanPullbackOneForm (fun _ => α) g (0,y)) x =
      (manifoldExteriorOneForm α (g x)).bilinearComp
        (manifoldMapDifferential (E := E) (F := F) g x)
        (manifoldMapDifferential (E := E) (F := F) g x) := by
  let c := g x
  have hc : g x ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
    (by simpa only [extChartAt_source] using hc)
  have hgc : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) x := (ho.comp x hg).contDiffAt
  have he := euclidean_manifold_pullback_germ (α := α) hg hc
  let A : F →L[ℝ] E := (chartDifferential c (g x)).comp
    (manifoldMapDifferential (E := E) (F := F) g x)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ g) A x :=
    hasMFDerivAt_iff_hasFDerivAt.mp
      ((ho.mdifferentiableAt (by simp)).hasMFDerivAt.comp x
        (hg.mdifferentiableAt (by simp)).hasMFDerivAt)
  have hd := hf.fderiv
  have hfd : fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) x =
      (chartDifferential (E := E) c (g x)).comp
        (manifoldMapDifferential (E := E) (F := F) g x) := hd
  calc
    _ = euclideanExteriorOneForm
        (staticPullbackOneForm (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c ∘ g)) x := by
      unfold euclideanExteriorOneForm
      rw [he.fderiv_eq]
    _ = _ := by
      rw [staticPullbackOneForm_exterior
        (g := extChartAt 𝓘(ℝ,E) c ∘ g) hα hgc,hfd]
      rfl

end

section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem manifold_pullback_exterior_at {α : ManifoldOneForm E M}
    {g : N → M} {b : N}
    (hα : ContDiffAt ℝ ∞ (chartOneForm α (g b))
      (extChartAt 𝓘(ℝ,E) (g b) (g b)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g b) :
    manifoldExteriorOneForm (E := F) (M := N)
      (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =
      manifoldPullbackTwoForm (E := E) (F := F) (fun _ => manifoldExteriorOneForm α) g 0 b := by
  let y := extChartAt 𝓘(ℝ,F) b b
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy : y ∈ (extChartAt 𝓘(ℝ,F) b).target := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he : (extChartAt 𝓘(ℝ,F) b).symm y=b := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hgy : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g ((extChartAt 𝓘(ℝ,F) b).symm y) := by
    rw [he]
    exact hg
  have hc : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y :=
    hgy.comp y hi
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hgy.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hu := hi.continuousAt.preimage_mem_nhds hn
  have hh : chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =ᶠ[𝓝 y]
      fun z => euclideanPullbackOneForm (fun _ => α) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (0,z) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy,hu] with z hz hzU
    exact chartOneForm_manifoldPullback_at (α := fun _ => α) (b := b) (p := (0,z)) hz
      (hzU.mdifferentiableAt (by simp))
  have hder : euclideanExteriorOneForm
      (chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b) y =
      (manifoldExteriorOneForm α (g b)).bilinearComp
        (manifoldMapDifferential (E := E) (F := F) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)
        (manifoldMapDifferential (E := E) (F := F) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y) := by
    calc
      _ = euclideanExteriorOneForm
          (fun z => euclideanPullbackOneForm (fun _ => α) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (0,z)) y := by
        unfold euclideanExteriorOneForm
        rw [hh.fderiv_eq]
      _ = _ := by
        have hα' : ContDiffAt ℝ ∞
            (chartOneForm α ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y))
            (extChartAt 𝓘(ℝ,E) ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)
              ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)) := by
          simpa only [Function.comp_apply,he] using hα
        simpa only [Function.comp_apply,he] using euclidean_manifold_pullback_exterior_at hc hα'
  have hd := mfderiv_comp y (hgy.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  have hD : manifoldMapDifferential (E := E) (F := F)
      (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y =
      (manifoldMapDifferential (E := E) (F := F) g b).comp
        (chartDifferential (E := F) b b).inverse := by
    change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y = _
    rw [hd,← chartDifferential_inverse hy]
    change (manifoldMapDifferential (E := E) (F := F) g
      ((extChartAt 𝓘(ℝ,F) b).symm y)).comp
      (chartDifferential (E := F) b ((extChartAt 𝓘(ℝ,F) b).symm y)).inverse = _
    rw [he]
  have H : (chartDifferential (E := F) b b).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,F)) hb using 1
    all_goals try with_reducible_and_instances rfl
  change (euclideanExteriorOneForm
    (chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b) y).bilinearComp
      (chartDifferential (E := F) b b) (chartDifferential (E := F) b b)=_
  rw [hder,hD]
  ext u v
  change manifoldExteriorOneForm α (g b)
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g b ((chartDifferential (E := F) b b).inverse (chartDifferential (E := F) b b u)))
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g b ((chartDifferential (E := F) b b).inverse (chartDifferential (E := F) b b v)))=_
  rw [H.inverse_apply_self,H.inverse_apply_self]
  rfl

end

section

variable {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem flatProduct_fst_smooth : ContMDiff 𝓘(ℝ,E × V) 𝓘(ℝ,E) ∞
    (Prod.fst : M × V → M) := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact contMDiff_fst

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem flatProduct_snd_smooth : ContMDiff 𝓘(ℝ,E × V) 𝓘(ℝ,V) ∞
    (Prod.snd : M × V → V) := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact contMDiff_snd

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem flatProduct_fst_derivative (z : M × V) :
    mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,E) (Prod.fst : M × V → M) z=
      ContinuousLinearMap.fst ℝ E V := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact mfderiv_fst

variable [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem productHorizontalLift_chart (Γ : V → ManifoldOneForm E M) (c : M × V)
    {y : E × V} (hy : y∈(extChartAt 𝓘(ℝ,E × V) c).target) :
    chartOneForm (productHorizontalLift Γ) c y=
      parameterEuclideanPullbackOneForm Γ
        (Prod.fst ∘ (extChartAt 𝓘(ℝ,E × V) c).symm)
        (((extChartAt 𝓘(ℝ,E × V) c).symm y).2,y) := by
  let v := ((extChartAt 𝓘(ℝ,E × V) c).symm y).2
  have he : chartOneForm (productHorizontalLift Γ) c y=
      chartOneForm (manifoldPullbackOneForm (E := E) (F := E × V)
        (fun _ => Γ v) (Prod.fst : M × V → M) 0) c y := by
    simp only [chartOneForm,productHorizontalLift,manifoldPullbackOneForm,
      manifoldMapDifferential,flatProduct_fst_derivative]
    rfl
  exact he.trans (chartOneForm_manifoldPullback (α := fun _ => Γ v)
    (p := (0,y)) flatProduct_fst_smooth hy)

theorem productHorizontalLift_smooth {Γ : P × V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (fun p => productHorizontalLift (fun v => Γ (p,v))) := by
  intro c q hq
  let g : E × V → M := Prod.fst ∘ (extChartAt 𝓘(ℝ,E × V) c).symm
  let v : E × V → V := Prod.snd ∘ (extChartAt 𝓘(ℝ,E × V) c).symm
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E × V)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hq.2)
  have hg : ContMDiffAt 𝓘(ℝ,E × V) 𝓘(ℝ,E) ∞ g q.2 :=
    flatProduct_fst_smooth.contMDiffAt.comp q.2 hi
  have hv : ContDiffAt ℝ ∞ v q.2 :=
    (flatProduct_snd_smooth.contMDiffAt.comp q.2 hi).contDiffAt
  have hx : ((q.1,v q.2),extChartAt 𝓘(ℝ,E) (g q.2) (g q.2))∈
      univ ×ˢ (extChartAt 𝓘(ℝ,E) (g q.2)).target :=
    ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) (g q.2)).map_source (mem_extChartAt_source _)⟩
  have hs := parameterEuclideanPullbackOneForm_contDiffAt
    (α := Γ) (p := ((q.1,v q.2),q.2))
    ((hΓ (g q.2)).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target _)).mem_nhds hx)) hg
  have hc := hs.comp q ((contDiffAt_fst.prodMk (hv.comp q contDiffAt_snd)).prodMk contDiffAt_snd)
  apply (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E × V)) c).mem_nhds hq.2)] with z hz
  exact productHorizontalLift_chart (fun w => Γ (z.1,w)) c hz

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_CubicFubiniStudy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped Manifold ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N] [TopologicalSpace P] [ChartedSpace G P]

 theorem manifoldMapDifferential_comp {g : N → M} {f : P → N} {x : P}
    (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g (f x))
    (hf : MDifferentiableAt 𝓘(ℝ,G) 𝓘(ℝ,F) f x) :
    manifoldMapDifferential (E := E) (F := G) (g ∘ f) x=
      (manifoldMapDifferential (E := E) (F := F) g (f x)).comp (manifoldMapDifferential (E := F) (F := G) f x) :=
  (hg.hasMFDerivAt.comp x hf.hasMFDerivAt).mfderiv

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_QuadricInfinityPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem SmoothOneFormFamily.add {α β : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) (hβ : SmoothOneFormFamily β) :
    SmoothOneFormFamily (fun p => α p+β p) := by
  intro c
  simpa only [chartOneForm_add] using (hα c).add (hβ c)

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem SmoothOneFormFamily.smul {α : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) {f : P → ℝ} (hf : ContDiff ℝ ∞ f) :
    SmoothOneFormFamily (fun p => f p • α p) := by
  intro c
  simpa only [chartOneForm_smul,Function.comp_apply,Pi.smul_def'] using
    (hf.comp contDiff_fst).contDiffOn.smul (hα c)

theorem SmoothOneFormFamily.comp {α : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) {f : Q → P} (hf : ContDiff ℝ ∞ f) :
    SmoothOneFormFamily (α ∘ f) := by
  intro c
  have hm : ContDiffOn ℝ ∞ (fun q : Q × E => (f q.1,q.2))
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
    ((hf.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
  exact (hα c).comp hm (fun _ hq => ⟨mem_univ _,hq.2⟩)

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_AnnularChartHelpers
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators

section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_add_at {α β : ManifoldOneForm E M} {x : M}
    (hα : ContDiffAt ℝ ∞ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x))
    (hβ : ContDiffAt ℝ ∞ (chartOneForm β x) (extChartAt 𝓘(ℝ,E) x x)) :
    manifoldExteriorOneForm (α+β) x=manifoldExteriorOneForm α x+manifoldExteriorOneForm β x := by
  have he : chartOneForm (α+β) x=chartOneForm α x+chartOneForm β x :=
    funext (chartOneForm_add α β x)
  simp only [manifoldExteriorOneForm,he,euclideanExteriorOneForm_add
    (hα.differentiableAt (by simp)) (hβ.differentiableAt (by simp))]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rfl

end

section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem chartOneForm_model (α : V → V →L[ℝ] ℝ) (c y : V) : chartOneForm α c y=α y := by
  simp only [chartOneForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,ContinuousLinearMap.comp_id,id_eq]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem manifoldExteriorOneForm_model (α : V → V →L[ℝ] ℝ) (x : V) :
    manifoldExteriorOneForm α x=euclideanExteriorOneForm α x := by
  rw [manifoldExteriorOneForm,show chartOneForm α x=α from funext (chartOneForm_model α x)]
  simp only [chartDifferential,
    extChartAt_model_space_eq_id,PartialEquiv.refl_coe,mfderiv_eq_fderiv,fderiv_id,id_eq]
  ext u v
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem linearLiouville_smooth (Ω : V →L[ℝ] V →L[ℝ] ℝ) : ContDiff ℝ ∞ (linearLiouville Ω) :=
  Ω.contDiff.const_smul _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem linearLiouville_exterior (Ω : V →L[ℝ] V →L[ℝ] ℝ) (hs : ∀ u v,Ω u v= -Ω v u) (x : V) :
    manifoldExteriorOneForm (linearLiouville Ω) x=Ω := by
  rw [manifoldExteriorOneForm_model]
  have hd : fderiv ℝ (linearLiouville Ω) x=(1/2:ℝ) • Ω :=
    ((Ω.hasFDerivAt).const_smul (1/2:ℝ)).fderiv
  simp only [euclideanExteriorOneForm,hd]
  ext u v
  change (1/2:ℝ)*Ω u v-(1/2:ℝ)*Ω v u=Ω u v
  rw [hs v u]
  ring

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem flatProduct_snd_derivative (z : M × V) :
    mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,V) (Prod.snd : M × V → V) z=
      ContinuousLinearMap.snd ℝ E V := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact mfderiv_snd

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem productVerticalLiouville_apply (Ω : V →L[ℝ] V →L[ℝ] ℝ) (z : M × V) (v : E × V) :
    productVerticalLiouville Ω z v=(1/2:ℝ)*Ω z.2 v.2 := by
  simp only [productVerticalLiouville,manifoldPullbackOneForm,manifoldMapDifferential,
    flatProduct_snd_derivative,ContinuousLinearMap.comp_apply]
  rfl

 theorem productVerticalLiouville_smooth (Ω : V →L[ℝ] V →L[ℝ] ℝ) :
    SmoothOneFormFamily (fun _ : ℝ => (productVerticalLiouville Ω : ManifoldOneForm (E × V) (M × V))) := by
  exact manifoldPullbackOneForm_smooth (α := fun _ => linearLiouville Ω)
    (e := (Prod.snd : M × V → V)) flatProduct_snd_smooth (fun c => by
    simpa only [chartOneForm_model,Function.comp_def] using
      ((linearLiouville_smooth Ω).comp (contDiff_snd (E := ℝ))).contDiffOn)

 theorem productVerticalLiouville_exterior (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    (hs : ∀ u v,Ω u v= -Ω v u) (z : M × V) :
    manifoldExteriorOneForm (productVerticalLiouville Ω) z=
      Ω.bilinearComp (ContinuousLinearMap.snd ℝ E V) (ContinuousLinearMap.snd ℝ E V) := by
  have ha : ContDiffAt ℝ ∞ (chartOneForm (linearLiouville Ω) z.2)
      (extChartAt 𝓘(ℝ,V) z.2 z.2) := by
    rw [show chartOneForm (linearLiouville Ω) z.2=linearLiouville Ω from
      funext (chartOneForm_model (linearLiouville Ω) z.2)]
    exact (linearLiouville_smooth Ω).contDiffAt
  rw [productVerticalLiouville,manifold_pullback_exterior_at ha flatProduct_snd_smooth.contMDiffAt]
  simp only [manifoldPullbackTwoForm,linearLiouville_exterior Ω hs,manifoldMapDifferential,
    flatProduct_snd_derivative]

 theorem productCouplingPrimitive_smooth (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (fun t => productCouplingPrimitive Ω (fun v => Γ (t,v))) :=
  (productVerticalLiouville_smooth Ω).add (productHorizontalLift_smooth hΓ)

 theorem productCouplingPrimitive_exterior (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    (hs : ∀ u v,Ω u v= -Ω v u) {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (z : M × V) :
    manifoldExteriorOneForm (productCouplingPrimitive Ω Γ) z=globalHorizontalCoupling Ω Γ z := by
  have hg : SmoothOneFormFamily (fun q : ℝ × V => Γ q.2) := hΓ.comp contDiff_snd
  have hh := productHorizontalLift_smooth hg
  rw [productCouplingPrimitive,manifoldExteriorOneForm_add_at
    ((productVerticalLiouville_smooth Ω).spatial_smooth 0 z (mem_extChartAt_target z))
    (hh.spatial_smooth 0 z (mem_extChartAt_target z)),productVerticalLiouville_exterior Ω hs]
  rfl

end

section
variable {ι : Type*} [Fintype ι]

theorem standardLiouville_smooth : ContDiff ℝ ∞ (standardLiouville (ι := ι)) :=
  (phaseArea (ι := ι)).contDiff.const_smul _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem verticalLiouville_apply (z : M × PlanePhase ι) (v : E × PlanePhase ι) :
    verticalLiouville z v=(1/2:ℝ)*phaseArea z.2 v.2 := by
  change standardLiouville z.2 (mfderiv 𝓘(ℝ,E × PlanePhase ι) 𝓘(ℝ,PlanePhase ι) Prod.snd z v)=_
  rw [flatProduct_snd_derivative]
  rfl

end

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem primitivePullback_smooth {α : F → F →L[ℝ] ℝ} {g : E → F}
    (hα : ContDiff ℝ ∞ α) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (primitivePullback α g) :=
  (hα.comp hg).clm_comp (hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

theorem primitivePullback_exterior {α : F → F →L[ℝ] ℝ} {g : E → F}
    (hα : ContDiff ℝ ∞ α) (hg : ContDiff ℝ ∞ g) (x : E) :
    euclideanExteriorOneForm (primitivePullback α g) x=
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  have hh := manifold_pullback_exterior (α := α) (g := g)
    (fun c => by
      rw [show chartOneForm α c=α from funext (vector_chartOneForm α c)]
      exact hα.contDiffOn)
    hg.contMDiff x
  have he : manifoldPullbackOneForm (fun _ => α) g 0=primitivePullback α g := by
    funext z
    simp [manifoldPullbackOneForm,manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback]
  rw [he] at hh
  simpa only [vector_exteriorOneForm,manifoldPullbackOneForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback] using hh

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_CubicEndCoordinates
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators

variable {ι : Type*} [Fintype ι]

theorem veronese_contDiff : ContDiff ℂ ∞ (veronese : (ι → ℂ) → _) := by
  apply contDiff_pi.mpr
  rintro (⟨b,i⟩|⟨i,j⟩)
  · exact contDiff_apply ℂ ℂ i
  · exact (contDiff_apply ℂ ℂ i).mul (contDiff_apply ℂ ℂ j)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

theorem normalPolynomial_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℂ ∞ (normalPolynomial a t) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact (contDiff_apply ℂ ℂ i).comp (veronese_contDiff.comp (affineComplex m).contDiff)
  | inr j => exact contDiff_const.mul ((contDiff_apply ℂ ℂ j).comp (equations_contDiff a))

theorem normalPolynomialCartesian_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℝ ∞ (fun z => complexCartesian (normalPolynomial a t z)) :=
  (complexCartesian (ι := NormalPolynomialIndex m)).contDiff.comp
    ((normalPolynomial_smooth a t).restrict_scalars ℝ)

theorem ambientFSPrimitive_smooth (c : ℝ) :
    ContDiff ℝ ∞ (ambientFSPrimitive (m := m) c) :=
  ((affineFSPrimitive_smooth c).comp (affinePhase m).contDiff).clm_comp contDiff_const

theorem normalAmbientPrimitive_smooth (a : Fin m → ℂ) (c d t : ℝ) :
    ContDiff ℝ ∞ (normalAmbientPrimitive a c d t) :=
  ((ambientFSPrimitive_smooth c).const_smul (1-2*d)).add
    ((primitivePullback_smooth (affineFSPrimitive_smooth c)
      (normalPolynomialCartesian_smooth a t)).const_smul d)

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialFamilyExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold MeasureTheory

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
 theorem manifoldExteriorOneForm_congr_germ {α β : ManifoldOneForm E M} {x : M}
    (h : α =ᶠ[𝓝 x] β) : manifoldExteriorOneForm α x=manifoldExteriorOneForm β x := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have ht := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) x).contMDiffAt
    ((isOpen_extChartAt_target x).mem_nhds ht)).continuousAt
  change Filter.Tendsto _ _ (𝓝 ((extChartAt 𝓘(ℝ,E) x).symm (extChartAt 𝓘(ℝ,E) x x))) at hi
  rw [(extChartAt 𝓘(ℝ,E) x).left_inv hx] at hi
  have he : chartOneForm α x =ᶠ[𝓝 (extChartAt 𝓘(ℝ,E) x x)] chartOneForm β x := by
    filter_upwards [hi.eventually h] with y hy
    exact congrArg (fun L : E →L[ℝ] ℝ => L.comp
      (chartDifferential x ((extChartAt 𝓘(ℝ,E) x).symm y)).inverse) hy
  simp only [manifoldExteriorOneForm,euclideanExteriorOneForm,he.fderiv_eq]

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_BallVolume
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical

namespace PackingSufficiencySupport

theorem closedBall_isClosed (n : ℕ) (R : ℝ) : IsClosed (closedBall n R) :=
  isClosed_le (continuous_capacity n) continuous_const

theorem closedBall_isCompact (n : ℕ) (R : ℝ) : IsCompact (closedBall n R) := by
  apply (isCompact_closedBall (0 : Ambient n) (max R 0 + 1)).of_isClosed_subset
    (closedBall_isClosed n R)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ max R 0 + 1)).mpr
  intro j
  have hj : Complex.normSq (z j) ≤ ∑ k, Complex.normSq (z k) :=
    Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (z k)) (Finset.mem_univ j)
  have hj' := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
  have hq : 0 ≤ Complex.normSq (z j) := Complex.normSq_nonneg (z j)
  have hs : (∑ k, Complex.normSq (z k)) * Real.pi ≤ R := by
    simpa [closedBall, capacity, mul_comm] using hz
  have hb : Complex.normSq (z j) ≤ max R 0 := by
    nlinarith [Real.pi_gt_three, le_max_left R 0]
  rw [Complex.normSq_eq_norm_sq] at hb
  have hm := le_max_right R 0
  nlinarith [sq_nonneg (‖z j‖ - 1)]

open MeasureTheory

end PackingSufficiencySupport
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_LayerBallEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology BigOperators
open Set Function

theorem complexSplitPhase_form (m : ℕ) (v w : Ambient (m+1)) :
    productForm phaseArea (complexSplitPhase m v) (complexSplitPhase m w)=standardForm v w := by
  simp only [productForm_apply,phaseArea_apply,complexSplitPhase_apply,standardForm,Fin.sum_univ_succ]
  rfl


end

open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_NonautonomousManifoldFlow
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N] [TopologicalSpace P] [ChartedSpace G P]

theorem FormNeighborhoodEmbedding.postcompose {K : Set N}
    {σ : ManifoldTwoForm F N} {Ω₀ : ManifoldTwoForm E M} {Ω₁ : ManifoldTwoForm G P}
    {f : N → M} (hf : FormNeighborhoodEmbedding K σ Ω₀ f)
    {T : Set M} (hT : IsOpen T) {g : M → P}
    (hg : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ g T)
    (hemb : Topology.IsEmbedding (fun x : T => g x.val))
    (hform : ∀ x ∈ T, ∀ v w, Ω₁ (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x w) = Ω₀ x v w)
    (him : MapsTo f K T) : FormNeighborhoodEmbedding K σ Ω₁ (g ∘ f) := by
  obtain ⟨U,hU,hKU,hs,he,hσ⟩ := hf
  let W := U ∩ f ⁻¹' T
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage hU hT
  have hWU : W ⊆ U := inter_subset_left
  have hWT : MapsTo f W T := inter_subset_right
  refine ⟨W,hW,fun x hx => ⟨hKU hx,him hx⟩,hg.comp (hs.mono hWU) hWT,?_,?_⟩
  · have he' := (he.comp (Topology.IsEmbedding.inclusion hWU)).codRestrict T
      (fun x : W => show f x.val ∈ T from x.property.2)
    exact hemb.comp he'
  · intro x hx v w
    have hd := mfderiv_comp x ((hg.contMDiffAt (hT.mem_nhds hx.2)).mdifferentiableAt (by simp))
      ((hs.contMDiffAt (hU.mem_nhds hx.1)).mdifferentiableAt (by simp))
    rw [hd]
    exact (hform (f x) hx.2 _ _).trans (hσ x hx.1 v w)

theorem postcompose_form_packing {ι : Type*} (K : ι → Set N)
    (σ : ManifoldTwoForm F N) (Ω₀ : ManifoldTwoForm E M) (Ω₁ : ManifoldTwoForm G P)
    {T : Set M} (hT : IsOpen T) (g : M → P)
    (hg : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ g T)
    (hemb : Topology.IsEmbedding (fun x : T => g x.val))
    (hform : ∀ x ∈ T, ∀ v w, Ω₁ (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x w) = Ω₀ x v w)
    (f : ι → N → M) (hf : ∀ i, FormNeighborhoodEmbedding (K i) σ Ω₀ (f i))
    (him : ∀ i, MapsTo (f i) (K i) T)
    (hd : Pairwise (fun i j => Disjoint (f i '' K i) (f j '' K j))) :
    (∀ i, FormNeighborhoodEmbedding (K i) σ Ω₁ (g ∘ f i)) ∧
      Pairwise (fun i j => Disjoint ((g ∘ f i) '' K i) ((g ∘ f j) '' K j)) := by
  refine ⟨fun i => (hf i).postcompose hT hg hemb hform (him i),?_⟩
  have hinj : InjOn g T := by
    intro x hx y hy heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) heq)
  intro i j hij
  rw [Set.image_comp,Set.image_comp]
  exact (hd hij).image hinj (image_subset_iff.mpr (him i)) (image_subset_iff.mpr (him j))

end

@[simp] theorem successorStandardForm_apply (m : ℕ) (v w : Ambient (m+1)) :
    successorStandardForm m v w = standardForm v w := complexSplitPhase_form m v w

 theorem isBallEmbedding_iff_formNeighborhoodEmbedding {m : ℕ} {r : ℝ}
    {f : Ambient (m+1) → Ambient (m+1)} :
    IsBallEmbedding r f ↔ FormNeighborhoodEmbedding (closedBall (m+1) r)
      (fun _ => successorStandardForm m) (fun _ => successorStandardForm m) f := by
  constructor
  · rintro ⟨U,hU,hBU,hs,he,hform⟩
    refine ⟨U,hU,hBU,hs.contMDiffOn,he,?_⟩
    intro x hx v w
    rw [mfderiv_eq_fderiv]
    change successorStandardForm m (fderiv ℝ f x v) (fderiv ℝ f x w) = successorStandardForm m v w
    erw [successorStandardForm_apply, successorStandardForm_apply]
    exact hform x hx v w
  · rintro ⟨U,hU,hBU,hs,he,hform⟩
    refine ⟨U,hU,hBU,hs.contDiffOn,he,?_⟩
    intro x hx v w
    have hh := hform x hx v w
    rw [mfderiv_eq_fderiv] at hh
    change successorStandardForm m (fderiv ℝ f x v) (fderiv ℝ f x w) = successorStandardForm m v w at hh
    erw [successorStandardForm_apply, successorStandardForm_apply] at hh
    exact hh

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_SphereCartesianDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
section

theorem optionPhaseAmbient_capacity (m : ℕ) (z : PlanePhase (Option (Fin m))) :
    capacity (optionPhaseAmbient m z)=Real.pi*phaseSq z := by
  obtain ⟨z,rfl⟩ := complexCartesian.surjective z
  simp only [optionPhaseAmbient,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply,capacity,complexCartesian_sq]
  congr 1
  simp only [Fin.sum_univ_succ,Fintype.sum_option]
  rfl

theorem optionPhaseAmbient_form (m : ℕ) (v w : PlanePhase (Option (Fin m))) :
    standardForm (optionPhaseAmbient m v) (optionPhaseAmbient m w)=phaseArea v w := by
  obtain ⟨v,rfl⟩ := complexCartesian.surjective v
  obtain ⟨w,rfl⟩ := complexCartesian.surjective w
  simp only [optionPhaseAmbient,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply,standardForm,phaseArea_apply]
  simp only [Fin.sum_univ_succ,Fintype.sum_option]
  rfl

variable {ι : Type*} [Fintype ι]

theorem fsBallMap_isEmbedding {a : ℝ} (ha : 0<a) :
    Topology.IsEmbedding (fsBallMap (ι := ι) a) :=
  Topology.IsEmbedding.subtypeVal.comp (fsBallHomeomorph (ι := ι) ha).isEmbedding

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_CubicBubbleSeparated
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open scoped Topology
open Set Function MeasureTheory
open scoped Manifold
open Manifold
section

 theorem planeRotate_fderiv (θ a : ℝ) (z v : Plane) :
    fderiv ℝ (fun p : ℝ × Plane => planeRotate p.1 p.2) (θ,z) (a,v)=
      planeRotate θ v+a • (-(planeRotate θ z).2,(planeRotate θ z).1) := by
  have hθ := hasFDerivAt_fst (𝕜 := ℝ) (p := (θ,z))
  have hz := hasFDerivAt_snd (𝕜 := ℝ) (p := (θ,z))
  have hc := (Real.hasDerivAt_cos θ).comp_hasFDerivAt (θ,z) hθ
  have hs := (Real.hasDerivAt_sin θ).comp_hasFDerivAt (θ,z) hθ
  have h1 := (hc.mul hz.fst).sub (hs.mul hz.snd)
  have h2 := (hs.mul hz.fst).add (hc.mul hz.snd)
  have he := congrArg (fun L => L (a,v)) (h1.prodMk h2).fderiv
  change fderiv ℝ (fun p : ℝ × Plane => planeRotate p.1 p.2) (θ,z) (a,v)=_ at he
  rw [he]
  ext <;> simp [planeRotate,smul_eq_mul] <;> ring

 theorem planarLiouville_rotation (θ a : ℝ) (z v : Plane) :
    linearLiouville planarArea (planeRotate θ z)
      (planeRotate θ v+a • (-(planeRotate θ z).2,(planeRotate θ z).1))=
        linearLiouville planarArea z v+a*(radialArea z/(2*Real.pi)) := by
  change (1/2:ℝ)*planarArea (planeRotate θ z)
    (planeRotate θ v+a • (-(planeRotate θ z).2,(planeRotate θ z).1))=_
  have he : planarArea (planeRotate θ z) (planeRotate θ v)=planarArea z v := by
    calc
      _=(Real.sin θ^2+Real.cos θ^2)*planarArea z v := by
        simp only [planarArea_apply,planeRotate]
        ring
      _=_ := by rw [Real.sin_sq_add_cos_sq,one_mul]
  have hr : planarArea (planeRotate θ z) (-(planeRotate θ z).2,(planeRotate θ z).1)=radiusSq z := by
    rw [← radiusSq_planeRotate θ z]
    simp only [planarArea_apply,radiusSq]
    ring
  rw [map_add,map_smul,he,hr]
  change (1/2:ℝ)*(planarArea z v+a*radiusSq z)=
    (1/2:ℝ)*planarArea z v+a*(Real.pi*radiusSq z/(2*Real.pi))
  field_simp [Real.pi_ne_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 theorem planarLiouville_gauge {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u : E × Plane) :
    linearLiouville planarArea (planeRotate (2*Real.pi*f x.1) x.2)
      (fderiv ℝ (fun y : E × Plane => planeRotate (2*Real.pi*f y.1) y.2) x u)=
        linearLiouville planarArea x.2 u.2+radialArea x.2*fderiv ℝ f x.1 u.1 := by
  have h₁ : HasFDerivAt (fun y : E × Plane => 2*Real.pi*f y.1)
      ((2*Real.pi) • (fderiv ℝ f x.1).comp (ContinuousLinearMap.fst ℝ E Plane)) x :=
    ((hf.differentiable (by simp) x.1).hasFDerivAt.comp x
      (hasFDerivAt_fst (𝕜 := ℝ) (p := x))).const_mul _
  have hpair := h₁.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := x))
  have hc := (planeRotate_smooth.differentiable (by simp) _).hasFDerivAt.comp x hpair
  change HasFDerivAt (fun y : E × Plane => planeRotate (2*Real.pi*f y.1) y.2) _ x at hc
  rw [hc.fderiv]
  change linearLiouville planarArea (planeRotate (2*Real.pi*f x.1) x.2)
    (fderiv ℝ (fun p : ℝ × Plane => planeRotate p.1 p.2) (2*Real.pi*f x.1,x.2)
      (2*Real.pi*fderiv ℝ f x.1 u.1,u.2))=_
  rw [planeRotate_fderiv,planarLiouville_rotation]
  field_simp [Real.pi_ne_zero]

end
section

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem euclideanExteriorOneForm_df {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    euclideanExteriorOneForm (fderiv ℝ f) x=0 := by
  ext v w
  change fderiv ℝ (fderiv ℝ f) x v w-fderiv ℝ (fderiv ℝ f) x w v=0
  have hs := hf.contDiffAt.isSymmSndFDerivAt (x := x) (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  exact sub_eq_zero.mpr (hs.eq v w)

end
section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem firstLinePrimitive_apply (α : ManifoldOneForm E M) (x : M × Plane) (u : E × Plane) :
    firstLinePrimitive α x u=linearLiouville planarArea x.2 u.2+(1-radialArea x.2)*α x.1 u.1 := by
  simp only [firstLinePrimitive,productCouplingPrimitive,Pi.add_apply,add_apply,
    productVerticalLiouville_apply,productHorizontalLift_apply,Pi.smul_apply,smul_apply,smul_eq_mul]
  rfl

 theorem firstLinePrimitive_family_smooth {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (fun t => firstLinePrimitive (Γ t)) := by
  have hs : ContDiff ℝ ∞ (fun p : ℝ × Plane => 1-radialArea p.2) :=
    contDiff_const.sub (radialArea_smooth.comp contDiff_snd)
  have hb : SmoothOneFormFamily (fun p : ℝ × Plane => Γ p.1) :=
    SmoothOneFormFamily.comp (P := ℝ) (Q := ℝ × Plane) (E := E) (M := M) hΓ contDiff_fst
  change SmoothOneFormFamily (fun t => productCouplingPrimitive planarArea
    (fun z => (1-radialArea z) • Γ t))
  exact productCouplingPrimitive_smooth (E := E) (M := M) (V := Plane) planarArea
    (Γ := fun p : ℝ × Plane => (1-radialArea p.2) • Γ p.1)
    (SmoothOneFormFamily.smul (P := ℝ × Plane) (E := E) (M := M) hb hs)

 theorem firstLinePrimitive_smooth {α : E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α) :
    ContDiff ℝ ∞ (firstLinePrimitive α) := by
  have he : firstLinePrimitive α=(fun x : E × Plane =>
      (linearLiouville planarArea x.2).comp (ContinuousLinearMap.snd ℝ E Plane)+
        (1-radialArea x.2) • (α x.1).comp (ContinuousLinearMap.fst ℝ E Plane)) := by
    funext x
    apply ContinuousLinearMap.ext
    intro u
    exact firstLinePrimitive_apply α x u
  rw [he]
  exact (((linearLiouville_smooth planarArea).comp contDiff_snd).clm_comp contDiff_const).add
    ((contDiff_const.sub (radialArea_smooth.comp contDiff_snd)).smul
      ((hα.comp contDiff_fst).clm_comp contDiff_const))

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem gaugeRotation_smooth {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun y : E × Plane => planeRotate (2*Real.pi*f y.1) y.2) := by
  have hf' : ContDiff ℝ ∞ (fun y : E × Plane => f y.1) := hf.comp contDiff_fst
  have hθ : ContDiff ℝ ∞ (fun y : E × Plane => 2*Real.pi*f y.1) := contDiff_const.mul hf'
  have hp : ContDiff ℝ ∞ (fun y : E × Plane => (2*Real.pi*f y.1,y.2)) := hθ.prodMk contDiff_snd
  convert! planeRotate_smooth.comp hp using 1
  all_goals try with_reducible_and_instances rfl

 theorem firstLineLift_smooth {g : E → F} {f : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (firstLineLift g f) :=
  (hg.comp contDiff_fst).prodMk (gaugeRotation_smooth hf)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
 theorem firstLineLift_inverse {g : E → F} {h : F → E} (hgh : LeftInverse h g) (hhg : RightInverse h g)
    (f : E → ℝ) : LeftInverse (firstLineLift h (fun y => -f (h y))) (firstLineLift g f) ∧
      RightInverse (firstLineLift h (fun y => -f (h y))) (firstLineLift g f) := by
  constructor <;> intro x <;> apply Prod.ext
  · exact hgh x.1
  · simp only [firstLineLift,planeRotate_comp]
    rw [hgh x.1]
    rw [show 2*Real.pi*(-f x.1)+2*Real.pi*f x.1=0 by ring,planeRotate_zero]
  · exact hhg x.1
  · simp only [firstLineLift,planeRotate_comp]
    rw [show 2*Real.pi*f (h x.1)+2*Real.pi*(-f (h x.1))=0 by ring,planeRotate_zero]

 theorem firstLineLift_isEmbedding {g : E → F} {h : F → E} {f : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (hf : ContDiff ℝ ∞ f)
    (hgh : LeftInverse h g) (hhg : RightInverse h g) : Topology.IsEmbedding (firstLineLift g f) := by
  let e : E × Plane ≃ₜ F × Plane :=
    { toEquiv := ⟨firstLineLift g f,firstLineLift h (fun y => -f (h y)),
        (firstLineLift_inverse hgh hhg f).1,(firstLineLift_inverse hgh hhg f).2⟩
      continuous_toFun := (firstLineLift_smooth hg hf).continuous
      continuous_invFun := (firstLineLift_smooth hh (hf.comp hh).neg).continuous }
  exact e.isEmbedding

 theorem firstLineLift_primitive {α : F → F →L[ℝ] ℝ} {β : E → E →L[ℝ] ℝ}
    {g : E → F} {f : E → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x,primitivePullback α g x=β x+fderiv ℝ f x) :
    primitivePullback (firstLinePrimitive α) (firstLineLift g f)=
      firstLinePrimitive β+fderiv ℝ (f ∘ Prod.fst) := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  have hrot : ContDiff ℝ ∞ (fun y : E × Plane => planeRotate (2*Real.pi*f y.1) y.2) :=
    gaugeRotation_smooth hf
  have hD := (((hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x.1).hasFDerivAt.comp x
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x))).prodMk (hrot.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasFDerivAt).fderiv
  change fderiv ℝ (firstLineLift g f) x=_ at hD
  change firstLinePrimitive α (firstLineLift g f x) (fderiv ℝ (firstLineLift g f) x u)=_
  rw [firstLinePrimitive_apply,hD]
  change linearLiouville planarArea (planeRotate (2*Real.pi*f x.1) x.2)
    (fderiv ℝ (fun y : E × Plane => planeRotate (2*Real.pi*f y.1) y.2) x u)+
    (1-radialArea (planeRotate (2*Real.pi*f x.1) x.2))*α (g x.1) (fderiv ℝ g x.1 u.1)=_
  rw [planarLiouville_gauge hf,radialArea_planeRotate]
  have he' := congrArg (fun L : E →L[ℝ] ℝ => L u.1) (he x.1)
  change α (g x.1) (fderiv ℝ g x.1 u.1)=β x.1 u.1+fderiv ℝ f x.1 u.1 at he'
  rw [he']
  have hdf := ((hf.differentiable (by simp) x.1).hasFDerivAt.comp x
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x))).fderiv
  simp only [Pi.add_apply,add_apply,firstLinePrimitive_apply,hdf,ContinuousLinearMap.comp_apply,
    ]
  change _=linearLiouville planarArea x.2 u.2+(1-radialArea x.2)*β x.1 u.1+fderiv ℝ f x.1 u.1
  ring

 theorem firstLineLift_exterior {α : F → F →L[ℝ] ℝ} {β : E → E →L[ℝ] ℝ}
    {g : E → F} {f : E → ℝ} (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x,primitivePullback α g x=β x+fderiv ℝ f x) (x : E × Plane) :
    (euclideanExteriorOneForm (firstLinePrimitive α) (firstLineLift g f x)).bilinearComp
      (fderiv ℝ (firstLineLift g f) x) (fderiv ℝ (firstLineLift g f) x)=
        euclideanExteriorOneForm (firstLinePrimitive β) x := by
  have hdf : ContDiff ℝ ∞ (f ∘ (Prod.fst : E × Plane → E)) := hf.comp contDiff_fst
  have hz := euclideanExteriorOneForm_df hdf x
  rw [← primitivePullback_exterior (firstLinePrimitive_smooth hα) (firstLineLift_smooth hg hf),
    firstLineLift_primitive hg hf he,euclideanExteriorOneForm_add
      ((firstLinePrimitive_smooth hβ).differentiable (by simp) x)
      ((hdf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x),hz]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change euclideanExteriorOneForm (firstLinePrimitive β) x u v+(0:ℝ)=_
  exact add_zero _

end

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

 theorem firstLineBaseMap_smooth {g : M → N} (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g) :
    ContMDiff 𝓘(ℝ,E × Plane) 𝓘(ℝ,F × Plane) ∞ (firstLineBaseMap g) := by
  rw [show 𝓘(ℝ,F × Plane)=(𝓘(ℝ,F)).prod 𝓘(ℝ,Plane) from modelWithCornersSelf_prod]
  exact (hg.comp flatProduct_fst_smooth).prodMk flatProduct_snd_smooth

 theorem firstLineBaseMap_derivative {g : M → N} (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g)
    (x : M × Plane) :
    manifoldMapDifferential (E := F × Plane) (F := E × Plane) (firstLineBaseMap g) x=
      (manifoldMapDifferential (E := F) (F := E) g x.1).prodMap
        (ContinuousLinearMap.id ℝ Plane) := by
  have hf := ((hg.comp flatProduct_fst_smooth).mdifferentiable (by simp) x).hasMFDerivAt
  have hs := ((flatProduct_snd_smooth (E := E) (M := M) (V := Plane)).mdifferentiable (by simp) x).hasMFDerivAt
  have hd : HasMFDerivAt 𝓘(ℝ,E × Plane) 𝓘(ℝ,F × Plane) (firstLineBaseMap g) x
      ((mfderiv 𝓘(ℝ,E × Plane) 𝓘(ℝ,F) (g ∘ Prod.fst) x).prod
        (mfderiv 𝓘(ℝ,E × Plane) 𝓘(ℝ,Plane) Prod.snd x)) := by
    rw [show 𝓘(ℝ,F × Plane)=(𝓘(ℝ,F)).prod 𝓘(ℝ,Plane) from modelWithCornersSelf_prod]
    exact hf.prodMk hs
  apply hd.mfderiv.trans
  erw [mfderiv_comp x (hg.mdifferentiable (by simp) x.1)
    (flatProduct_fst_smooth.mdifferentiable (by simp) x),flatProduct_fst_derivative,flatProduct_snd_derivative]
  rfl

 theorem firstLineBaseMap_primitive {g : M → N} (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g)
    (α : ManifoldOneForm F N) (x : M × Plane) :
    manifoldPullbackOneForm (fun _ => firstLinePrimitive α) (firstLineBaseMap g) 0 x=
      firstLinePrimitive (manifoldPullbackOneForm (E := F) (F := E) (fun _ => α) g 0) x := by
  apply ContinuousLinearMap.ext
  intro v
  change firstLinePrimitive α (firstLineBaseMap g x)
    (manifoldMapDifferential (E := F × Plane) (F := E × Plane) (firstLineBaseMap g) x v)=_
  rw [firstLineBaseMap_derivative hg,firstLinePrimitive_apply,firstLinePrimitive_apply]
  rfl

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_LiouvilleRadialCalculus
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

 theorem linearLiouville_variable_smul (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    (hΩ : ∀ z,Ω z z=0) {s : E → ℝ} {w : E → V} {x : E}
    (hs : DifferentiableAt ℝ s x) (hw : DifferentiableAt ℝ w x) (u : E) :
    linearLiouville Ω (s x • w x) (fderiv ℝ (fun y => s y • w y) x u)=
      (s x)^2*linearLiouville Ω (w x) (fderiv ℝ w x u) := by
  change linearLiouville Ω (s x • w x) (fderiv ℝ (s • w) x u)=_
  rw [fderiv_smul hs hw]
  simp only [linearLiouville,smul_apply,smul_eq_mul,add_apply,
    ContinuousLinearMap.smulRight_apply,map_smul,map_add,hΩ,mul_zero,add_zero]
  ring

variable {ι : Type*} [Fintype ι]
 theorem fsBallMap_primitive {c : ℝ} (hc : 0 ≤ c) (z v : PlanePhase ι) :
    standardLiouville (fsBallMap c z) (fderiv ℝ (fsBallMap c) z v)=affineFSPrimitive c z v := by
  rw [fsBallMap_fderiv]
  simp only [standardLiouville,affineFSPrimitive,fsBallMap,smul_apply,smul_eq_mul,
    map_smul,map_sub,phaseArea_self,mul_zero,sub_zero]
  have he : (Real.sqrt c/Real.sqrt (1+phaseSq z))^2=c/(1+phaseSq z) := by
    rw [div_pow,Real.sq_sqrt hc,Real.sq_sqrt (fs_den_pos z).le]
  calc
    _=(Real.sqrt c/Real.sqrt (1+phaseSq z))^2/2*phaseArea z v := by ring
    _=_ := by rw [he]; field_simp

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open Hamiltonian MomentPolytope

 theorem largeNormalCoefficient_smooth (q : ℕ) : ContDiff ℝ ∞ (largeNormalCoefficient q) := by
  unfold largeNormalCoefficient
  fun_prop

 variable {m q : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 attribute [local instance] OAI.PackingSufficiencySupport.DiagonalQuadrics.liouvilleRadialSigmaCompact
theorem largeHorizontalPrimitive_smooth : SmoothOneFormFamily (largeHorizontalPrimitive (q := q) a) :=
  ((curveFSPrimitive_smooth a (1/Real.pi)).comp
    (f := fun _ : Fin (q+1) → ℝ => (0:ℝ)) contDiff_const).smul (largeNormalCoefficient_smooth q)

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_TailLineCoordinates
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold

 theorem normalSplit_liouville (q : ℕ) (z v : PlanePhase (Fin (q+1))) :
    standardLiouville z v=standardLiouville (normalTail q z) (normalTail q v)+
      linearLiouville planarArea (normalHead q z) (normalHead q v) := by
  simp only [standardLiouville,linearLiouville,smul_apply,smul_eq_mul,
    phaseArea_apply,Fin.sum_univ_succ,normalTail,normalHead,ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply,planarArea_apply]
  ring

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] {q : ℕ}

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem firstTailMap_smooth {s : PlanePhase (Fin (q+1)) → ℝ} (hs : ContDiff ℝ ∞ s) :
    ContMDiff 𝓘(ℝ,E × PlanePhase (Fin (q+1))) 𝓘(ℝ,(E × PlanePhase (Fin q)) × Plane) ∞
      (firstTailMap (M := M) s) := by
  have ht := ((hs.smul (normalTail q).contDiff).contMDiff.comp
    (flatProduct_snd_smooth (E := E) (M := M)))
  have hb : ContMDiff 𝓘(ℝ,E × PlanePhase (Fin (q+1))) 𝓘(ℝ,E × PlanePhase (Fin q)) ∞
      (fun x : M × PlanePhase (Fin (q+1)) => (x.1,s x.2 • normalTail q x.2)) := by
    rw [show 𝓘(ℝ,E × PlanePhase (Fin q))=(𝓘(ℝ,E)).prod 𝓘(ℝ,PlanePhase (Fin q)) from modelWithCornersSelf_prod]
    exact flatProduct_fst_smooth.prodMk ht
  rw [show 𝓘(ℝ,(E × PlanePhase (Fin q)) × Plane)=
    (𝓘(ℝ,E × PlanePhase (Fin q))).prod 𝓘(ℝ,Plane) from modelWithCornersSelf_prod]
  exact hb.prodMk ((normalHead q).contDiff.contMDiff.comp flatProduct_snd_smooth)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem firstTailMap_derivative {s : PlanePhase (Fin (q+1)) → ℝ} (hs : ContDiff ℝ ∞ s)
    (x : M × PlanePhase (Fin (q+1))) (v : E × PlanePhase (Fin (q+1))) :
    manifoldMapDifferential (E := (E × PlanePhase (Fin q)) × Plane)
      (F := E × PlanePhase (Fin (q+1))) (firstTailMap s) x v=
      ((v.1,fderiv ℝ (fun z => s z • normalTail q z) x.2 v.2),normalHead q v.2) := by
  have hb := (flatProduct_fst_smooth (E := E) (M := M) (V := PlanePhase (Fin (q+1)))).mdifferentiable (by simp) x
  have ht := ((hs.smul (normalTail q).contDiff).contMDiff.comp
    (flatProduct_snd_smooth (E := E) (M := M))).mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  have hh := ((normalHead q).contDiff.contMDiff.comp
    (flatProduct_snd_smooth (E := E) (M := M))).mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  have hd : HasMFDerivAt 𝓘(ℝ,E × PlanePhase (Fin (q+1)))
      𝓘(ℝ,(E × PlanePhase (Fin q)) × Plane) (firstTailMap s) x
      ((mfderiv 𝓘(ℝ,E × PlanePhase (Fin (q+1))) 𝓘(ℝ,E) Prod.fst x).prod
        (mfderiv 𝓘(ℝ,E × PlanePhase (Fin (q+1))) 𝓘(ℝ,PlanePhase (Fin q))
          (fun y : M × PlanePhase (Fin (q+1)) => s y.2 • normalTail q y.2) x) |>.prod
        (mfderiv 𝓘(ℝ,E × PlanePhase (Fin (q+1))) 𝓘(ℝ,Plane)
          (fun y : M × PlanePhase (Fin (q+1)) => normalHead q y.2) x)) := by
    rw [show 𝓘(ℝ,(E × PlanePhase (Fin q)) × Plane)=
      (𝓘(ℝ,E × PlanePhase (Fin q))).prod 𝓘(ℝ,Plane) from modelWithCornersSelf_prod]
    apply HasMFDerivAt.prodMk ?_ hh.hasMFDerivAt
    rw [show 𝓘(ℝ,E × PlanePhase (Fin q))=(𝓘(ℝ,E)).prod 𝓘(ℝ,PlanePhase (Fin q)) from modelWithCornersSelf_prod]
    exact hb.hasMFDerivAt.prodMk ht.hasMFDerivAt
  change mfderiv _ _ _ x v=_
  rw [hd.mfderiv,flatProduct_fst_derivative]
  have htD := mfderiv_comp x ((hs.smul (normalTail q).contDiff).contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x.2)
    ((flatProduct_snd_smooth (E := E) (M := M)).mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)
  have hhD := mfderiv_comp x ((normalHead q).contDiff (n := ∞) |>.contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x.2)
    ((flatProduct_snd_smooth (E := E) (M := M)).mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)
  erw [htD,hhD,flatProduct_snd_derivative,mfderiv_eq_fderiv,mfderiv_eq_fderiv,(normalHead q).fderiv]
  rfl

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_QuadricMovingCone
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian
open scoped BigOperators
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 theorem largeCouplingPrimitive_exterior (x : LargeNormalSpace a) :
    manifoldExteriorOneForm (largeCouplingPrimitive a) x=
      globalHorizontalCoupling phaseArea (largeHorizontalPrimitive (q := m) a ∘ planeMoments) x :=
  productCouplingPrimitive_exterior (E := RealModel) (M := locus a)
    (V := PlanePhase (Fin (m+1))) phaseArea phaseArea_skew
    ((largeHorizontalPrimitive_smooth (q := m) a).comp planeMoments_smooth) x

 theorem phaseMoments_sum {q : ℕ} (z : PlanePhase (Fin q)) :
    (∑ j,planeMoments z j)=Real.pi*phaseSq z := by
  simp only [planeMoments,radialArea,radiusSq,phaseSq,phaseDot_apply,pow_two,← Finset.mul_sum]

 theorem normalCouplingPrimitive_apply (x : NormalSpace a) (v : NormalModel m) :
    normalCouplingPrimitive a x v=standardLiouville x.2 v.2+
      (1-2*Real.pi*phaseSq x.2)*curveFSPrimitive a (1/Real.pi) x.1 v.1 := by
  simp only [normalCouplingPrimitive,Pi.add_apply,add_apply,productHorizontalLift_apply,
    Function.comp_apply,normalHorizontalPrimitive,Pi.smul_apply,smul_apply,smul_eq_mul,
    equalNormalCoefficient,phaseMoments_sum,verticalLiouville_apply,standardLiouville]
  ring

 theorem largeCouplingPrimitive_apply (x : LargeNormalSpace a) (v : LargeNormalModel m) :
    largeCouplingPrimitive a x v=standardLiouville x.2 v.2+
      (1-radialArea (normalHead m x.2)-2*Real.pi*phaseSq (normalTail m x.2))*
        curveFSPrimitive a (1/Real.pi) x.1 v.1 := by
  simp only [largeCouplingPrimitive,productCouplingPrimitive,Pi.add_apply,add_apply,
    productVerticalLiouville_apply,productHorizontalLift_apply,Function.comp_apply,
    largeHorizontalPrimitive,largeNormalCoefficient,Pi.smul_apply,smul_apply,smul_eq_mul]
  have he : (∑ j : Fin m,planeMoments x.2 j.succ)=Real.pi*phaseSq (normalTail m x.2) :=
    phaseMoments_sum (normalTail m x.2)
  rw [he]
  change (1/2:ℝ)*phaseArea x.2 v.2+(1-radialArea (normalHead m x.2)-2*(Real.pi*phaseSq (normalTail m x.2)))*
    curveFSPrimitive a (1/Real.pi) x.1 v.1=_
  simp only [standardLiouville,smul_apply,smul_eq_mul]
  ring

 theorem firstTailMap_primitive {s : PlanePhase (Fin (m+1)) → ℝ} (hs : ContDiff ℝ ∞ s)
    (x : LargeNormalSpace a) (hc : (1-radialArea (normalHead m x.2))*(s x.2)^2=1) :
    manifoldPullbackOneForm (fun _ => firstLinePrimitive (normalCouplingPrimitive a))
      (firstTailMap s) 0 x=largeCouplingPrimitive a x := by
  apply ContinuousLinearMap.ext
  intro v
  change firstLinePrimitive (normalCouplingPrimitive a) (firstTailMap s x)
    (manifoldMapDifferential (E := NormalModel m × Plane) (F := LargeNormalModel m) (firstTailMap s) x v)=_
  rw [firstTailMap_derivative hs,firstLinePrimitive_apply,normalCouplingPrimitive_apply,
    largeCouplingPrimitive_apply]
  change linearLiouville planarArea (normalHead m x.2) (normalHead m v.2)+
    (1-radialArea (normalHead m x.2))*(standardLiouville (s x.2 • normalTail m x.2)
      (fderiv ℝ (fun z => s z • normalTail m z) x.2 v.2)+
      (1-2*Real.pi*phaseSq (s x.2 • normalTail m x.2))*curveFSPrimitive a (1/Real.pi) x.1 v.1)=_
  have hL := linearLiouville_variable_smul phaseArea phaseArea_self (hs.differentiable (by simp) x.2)
    (normalTail m).differentiableAt v.2
  change standardLiouville (s x.2 • normalTail m x.2)
      (fderiv ℝ (fun z => s z • normalTail m z) x.2 v.2)=_ at hL
  rw [(normalTail m).fderiv] at hL
  change standardLiouville (s x.2 • normalTail m x.2)
      (fderiv ℝ (fun z => s z • normalTail m z) x.2 v.2)=
        (s x.2)^2*standardLiouville (normalTail m x.2) (normalTail m v.2) at hL
  rw [hL,phaseSq_smul,normalSplit_liouville]
  change _=standardLiouville (normalTail m x.2) (normalTail m v.2)+
    linearLiouville planarArea (normalHead m x.2) (normalHead m v.2)+_
  linear_combination
    (standardLiouville (normalTail m x.2) (normalTail m v.2)-
      2*Real.pi*phaseSq (normalTail m x.2)*curveFSPrimitive a (1/Real.pi) x.1 v.1)*hc

end

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 theorem exists_compact_first_tail_bridge {b d : ℝ} (hb : b<1)
    {K : Set (LargeNormalSpace a)} (hK : IsCompact K)
    (hKb : ∀ x∈K,radialArea (normalHead m x.2)<b)
    (hKd : ∀ x∈K,Real.pi*phaseSq (normalTail m x.2)<d*(1-radialArea (normalHead m x.2))) :
    ∃ H : LargeNormalSpace a → NormalSpace a × Plane,
      ContMDiff 𝓘(ℝ,LargeNormalModel m) 𝓘(ℝ,NormalModel m × Plane) ∞ H ∧
      ∃ D : Set (LargeNormalSpace a),IsOpen D ∧ K⊆D ∧
        Topology.IsEmbedding (fun x : D => H x.val) ∧
        (∀ x,radialArea (H x).2=radialArea (normalHead m x.2)) ∧
        (∀ x∈D,radialArea (H x).2<b ∧ phaseSq (H x).1.2<d/Real.pi) ∧
        (∀ x∈D,manifoldPullbackOneForm (fun _ => firstLinePrimitive (normalCouplingPrimitive a)) H 0 x=
          largeCouplingPrimitive a x) := by
  let U : Set (PlanePhase (Fin (m+1))) := {z | radialArea (normalHead m z)<b ∧
    Real.pi*phaseSq (normalTail m z)<d*(1-radialArea (normalHead m z))}
  have hU : IsOpen U :=
    (isOpen_lt (radialArea_smooth.continuous.comp (normalHead m).continuous) continuous_const).inter
      (isOpen_lt (continuous_const.mul (phaseSq_smooth.continuous.comp (normalTail m).continuous))
        (continuous_const.mul (continuous_const.sub (radialArea_smooth.continuous.comp (normalHead m).continuous))))
  let σ : PlanePhase (Fin (m+1)) → ℝ := fun z => (Real.sqrt (1-radialArea (normalHead m z)))⁻¹
  have hσ : ContDiffOn ℝ ∞ σ U :=
    (((contDiffOn_const.sub ((radialArea_smooth.comp (normalHead m).contDiff).contDiffOn)).sqrt
      (fun z hz => (sub_pos.mpr (hz.1.trans hb)).ne')).inv
        (fun z hz => (Real.sqrt_pos.mpr (sub_pos.mpr (hz.1.trans hb))).ne'))
  obtain ⟨χ,_hχ,_hχc,_hχU,_hχr,_hχ1,hs,_hsc,hse⟩ := exists_smooth_compact_extension
    (hK.image continuous_snd) hU (by rintro z ⟨x,hx,rfl⟩; exact ⟨hKb x hx,hKd x hx⟩) hσ
  let s : PlanePhase (Fin (m+1)) → ℝ := fun z => χ z • σ z
  obtain ⟨O,hO,hKO,hOs⟩ := mem_nhdsSet_iff_exists.mp hse
  let D : Set (LargeNormalSpace a) := Prod.snd ⁻¹' (O∩U)
  have hD : IsOpen D := (hO.inter hU).preimage continuous_snd
  let H : LargeNormalSpace a → NormalSpace a × Plane := firstTailMap s
  have hH := firstTailMap_smooth (M := locus a) (E := RealModel) hs
  have hratio (x : LargeNormalSpace a) (hx : x∈D) :
      (1-radialArea (normalHead m x.2))*(s x.2)^2=1 := by
    have he : s x.2=σ x.2 := hOs hx.1
    rw [he]
    change (1-radialArea (normalHead m x.2))*((Real.sqrt (1-radialArea (normalHead m x.2)))⁻¹)^2=1
    rw [inv_pow,Real.sq_sqrt (sub_pos.mpr (hx.2.1.trans hb)).le,
      mul_inv_cancel₀ (sub_pos.mpr (hx.2.1.trans hb)).ne']
  let G : NormalSpace a × Plane → LargeNormalSpace a := fun y =>
    (y.1.1,(normalSplit m).symm (Real.sqrt (1-radialArea y.2) • y.1.2,y.2))
  have hG : Continuous G := by
    exact continuous_fst.fst.prodMk ((normalSplit m).symm.continuous.comp
      (((Real.continuous_sqrt.comp (continuous_const.sub (radialArea_smooth.continuous.comp continuous_snd))).smul
        continuous_fst.snd).prodMk continuous_snd))
  have hGH (x : LargeNormalSpace a) (hx : x∈D) : G (H x)=x := by
    apply Prod.ext
    · rfl
    have he : s x.2=σ x.2 := hOs hx.1
    change (normalSplit m).symm
      (Real.sqrt (1-radialArea (normalHead m x.2)) • (s x.2 • normalTail m x.2),normalHead m x.2)=x.2
    rw [he,smul_smul]
    change (normalSplit m).symm
      ((Real.sqrt (1-radialArea (normalHead m x.2))*
        (Real.sqrt (1-radialArea (normalHead m x.2)))⁻¹) • normalTail m x.2,normalHead m x.2)=x.2
    rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr (sub_pos.mpr (hx.2.1.trans hb))).ne',one_smul]
    exact (normalSplit m).symm_apply_apply x.2
  have hemb : Topology.IsEmbedding (fun x : D => H x.val) := by
    apply Topology.IsEmbedding.of_comp (hH.continuous.comp continuous_subtype_val) hG
    convert Topology.IsEmbedding.subtypeVal (p := fun x => x∈D) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact hGH x.val x.property
  refine ⟨H,hH,D,hD,fun x hx => ⟨hKO ⟨x,hx,rfl⟩,hKb x hx,hKd x hx⟩,hemb,
    fun _ => rfl,?_,fun x hx => firstTailMap_primitive a hs x (hratio x hx)⟩
  intro x hx
  refine ⟨hx.2.1,?_⟩
  change phaseSq (s x.2 • normalTail m x.2)<d/Real.pi
  rw [phaseSq_smul]
  apply (lt_div_iff₀ Real.pi_pos).mpr
  have hu : 0<1-radialArea (normalHead m x.2) := sub_pos.mpr (hx.2.1.trans hb)
  apply (mul_lt_mul_iff_of_pos_left hu).mp
  calc
    (1-radialArea (normalHead m x.2))*((s x.2)^2*phaseSq (normalTail m x.2)*Real.pi)=
        Real.pi*phaseSq (normalTail m x.2) := by rw [← mul_assoc,← mul_assoc,hratio x hx]; ring
    _<d*(1-radialArea (normalHead m x.2)) := hx.2.2
    _=(1-radialArea (normalHead m x.2))*d := mul_comm _ _

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped Manifold ContDiff Topology
open Set Function Manifold

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

 theorem firstLineBaseMap_isEmbedding_on {g : M → N} {U : Set M}
    (hg : Topology.IsEmbedding (fun x : U => g x.val)) :
    Topology.IsEmbedding (fun x : Prod.fst ⁻¹' U => firstLineBaseMap g x.val) := by
  let j : (Prod.fst ⁻¹' U : Set (M × Plane)) → U × Plane :=
    fun x => (⟨x.val.1,x.property⟩,x.val.2)
  have hjc : Continuous j :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
  let k : U × Plane → M × Plane := Prod.map Subtype.val id
  have hkc : Continuous k := continuous_subtype_val.prodMap continuous_id
  have hj : Topology.IsEmbedding j := by
    apply Topology.IsEmbedding.of_comp hjc hkc
    exact Topology.IsEmbedding.subtypeVal
  exact (hg.prodMap Topology.IsEmbedding.id).comp hj

 theorem firstLineMoving_smooth {A : ℝ × M → N}
    (hA : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ A) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E × Plane)) 𝓘(ℝ,F × Plane) ∞
      (fun p : ℝ × (M × Plane) => firstLineBaseMap (fun x => A (p.1,x)) p.2) := by
  rw [show 𝓘(ℝ,F × Plane)=(𝓘(ℝ,F)).prod 𝓘(ℝ,Plane) from modelWithCornersSelf_prod]
  exact (hA.comp (contMDiff_fst.prodMk
    ((flatProduct_fst_smooth (E := E) (M := M) (V := Plane)).comp contMDiff_snd))).prodMk
      ((flatProduct_snd_smooth (E := E) (M := M) (V := Plane)).comp contMDiff_snd)

 theorem firstLineBaseMap_primitive_eq {g : M → N}
    (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g) (α : ManifoldOneForm F N)
    (β : ManifoldOneForm E M) {x : M × Plane}
    (he : (α (g x.1)).comp (manifoldMapDifferential (E := F) (F := E) g x.1)=β x.1) :
    manifoldPullbackOneForm (fun _ => firstLinePrimitive α) (firstLineBaseMap g) 0 x=
      firstLinePrimitive β x := by
  rw [firstLineBaseMap_primitive hg]
  apply ContinuousLinearMap.ext
  intro v
  rw [firstLinePrimitive_apply,firstLinePrimitive_apply]
  change linearLiouville planarArea x.2 v.2+(1-radialArea x.2)*
    ((α (g x.1)).comp (manifoldMapDifferential (E := F) (F := E) g x.1)) v.1=_
  rw [he]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 theorem exists_actual_large_normal_transfer {b d : ℝ} (hb : b<1)
    (hd : 0<d) (hdhalf : d<1/2) {K : Set (LargeNormalSpace a)} (hK : IsCompact K)
    (hKb : ∀ x∈K,radialArea (normalHead m x.2)<b)
    (hKd : ∀ x∈K,Real.pi*phaseSq (normalTail m x.2)<d*(1-radialArea (normalHead m x.2))) :
    ∃ t : ℝ,0<t ∧ ∃ g : LargeNormalSpace a → Affine m × Plane,
      ∃ W : Set (LargeNormalSpace a),IsOpen W ∧ K⊆W ∧
      ContMDiff 𝓘(ℝ,LargeNormalModel m) 𝓘(ℝ,Affine m × Plane) ∞ g ∧
      Topology.IsEmbedding (fun x : W => g x.val) ∧
      (∀ x∈W,radialArea (g x).2<b) ∧
      ∀ x∈W,∀ v w,
        euclideanExteriorOneForm (firstLinePrimitive (normalAmbientPrimitive a (1/Real.pi) d t)) (g x)
          (mfderiv 𝓘(ℝ,LargeNormalModel m) 𝓘(ℝ,Affine m × Plane) g x v)
          (mfderiv 𝓘(ℝ,LargeNormalModel m) 𝓘(ℝ,Affine m × Plane) g x w)=
        globalHorizontalCoupling phaseArea (largeHorizontalPrimitive (q := m) a ∘ planeMoments) x v w := by
  let : SigmaCompactSpace (locus a) := IsClosed.sigmaCompactSpace (locus_isClosed a)
  obtain ⟨H,hH,D,hD,hKD,hHemb,_hHu,hHD,hHprim⟩ := exists_compact_first_tail_bridge a hb hK hKb hKd
  have hHK : IsCompact (Prod.fst '' (H '' K)) := (hK.image hH.continuous).image continuous_fst
  obtain ⟨A,Γ,δ,hδ,U,hU,hUK,hA,hΓ,hΓ0,hAemb,hΓprim⟩ :=
    exists_actual_radial_primitive_family_bp240 a hd hHK (by
      rintro y ⟨z,⟨x,hx,rfl⟩,rfl⟩
      exact (hHD x (hKD hx)).2)
  let V : Set (LargeNormalSpace a) := D∩(fun x => (H x).1) ⁻¹' U
  have hV : IsOpen V := hD.inter (hU.preimage hH.continuous.fst)
  have hKV : K⊆V := fun x hx => ⟨hKD hx,hUK ⟨H x,⟨x,hx,rfl⟩,rfl⟩⟩
  let Δ : ℝ → ManifoldOneForm (LargeNormalModel m) (LargeNormalSpace a) :=
    manifoldPullbackOneForm (fun t => firstLinePrimitive (Γ t)) H
  have hΔ : SmoothOneFormFamily Δ :=
    manifoldPullbackOneForm_smooth hH (firstLinePrimitive_family_smooth hΓ)
  have hΔ0 (x : LargeNormalSpace a) (hx : x∈V) : Δ 0 x=largeCouplingPrimitive a x := by
    have he : firstLinePrimitive (Γ 0) (H x)=firstLinePrimitive (normalCouplingPrimitive a) (H x) := by
      apply ContinuousLinearMap.ext
      intro v
      rw [firstLinePrimitive_apply,firstLinePrimitive_apply,hΓ0 hx.2]
    change (firstLinePrimitive (Γ 0) (H x)).comp
      (manifoldMapDifferential (E := NormalModel m × Plane) (F := LargeNormalModel m) H x)=_
    rw [he]
    exact hHprim x hx.1
  have hΔext (x : LargeNormalSpace a) (hx : x∈V) :
      manifoldExteriorOneForm (Δ 0) x=manifoldExteriorOneForm (largeCouplingPrimitive a) x :=
    manifoldExteriorOneForm_congr_germ (Filter.eventually_of_mem (hV.mem_nhds hx) hΔ0)
  have hinv (x : LargeNormalSpace a) (hx : x∈K) : (manifoldExteriorOneForm (Δ 0) x).IsInvertible := by
    rw [hΔext x (hKV hx)]
    apply largeCouplingPrimitive_invertible_bp240
    have hu : 0<1-radialArea (normalHead m x.2) := sub_pos.mpr ((hKb x hx).trans hb)
    have hm := hKd x hx
    have hp := mul_pos (show 0<1-2*d by linarith) hu
    nlinarith
  let J : ℝ × LargeNormalSpace a → Affine m × Plane :=
    fun p => firstLineBaseMap (fun x => A (p.1,x)) (H p.2)
  have hJ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,LargeNormalModel m)) 𝓘(ℝ,Affine m × Plane) ∞ J :=
    by
      have hh := firstLineMoving_smooth hA
      simp +instances only [flatProduct_chartedSpace,chartedSpaceSelf_prod] at hh
      exact hh.comp (contMDiff_fst.prodMk (hH.comp contMDiff_snd))
  have hJs (t : ℝ) : ContMDiff 𝓘(ℝ,LargeNormalModel m) 𝓘(ℝ,Affine m × Plane) ∞ (fun x => J (t,x)) :=
    hJ.comp (contMDiff_const.prodMk contMDiff_id)
  have hJemb (t : ℝ) (ht : t∈Ioc (0:ℝ) δ) : Topology.IsEmbedding (fun x : V => J (t,x.val)) := by
    exact (firstLineBaseMap_isEmbedding_on (g := fun y => A (t,y)) (hAemb t ht)).comp
      ((hHemb.comp (Topology.IsEmbedding.inclusion inter_subset_left)).codRestrict
        (Prod.fst ⁻¹' U) (fun x : V => x.property.2))
  let α : ℝ → (Affine m × Plane) → (Affine m × Plane) →L[ℝ] ℝ :=
    fun t => firstLinePrimitive (normalAmbientPrimitive a (1/Real.pi) d t)
  have hα (t : ℝ) : ContDiff ℝ ∞ (α t) :=
    firstLinePrimitive_smooth (normalAmbientPrimitive_smooth a _ d t)
  have hJprim (t : ℝ) (ht : t∈Ioc (0:ℝ) δ) (x : LargeNormalSpace a) (hx : x∈V) :
      Δ t x=manifoldPullbackOneForm (fun _ => α t) (fun y => J (t,y)) 0 x := by
    have hs : ContMDiff 𝓘(ℝ,NormalModel m) 𝓘(ℝ,Affine m) ∞ (fun y => A (t,y)) :=
      hA.comp (contMDiff_const.prodMk contMDiff_id)
    have he := firstLineBaseMap_primitive_eq hs (normalAmbientPrimitive a (1/Real.pi) d t)
      (Γ t) (x := H x) (hΓprim t ht (H x).1 hx.2).symm
    simp +instances only [flatProduct_chartedSpace,chartedSpaceSelf_prod] at he
    have hc := congrArg (fun L : (NormalModel m × Plane) →L[ℝ] ℝ =>
      L.comp (manifoldMapDifferential (E := NormalModel m × Plane) (F := LargeNormalModel m) H x)) he
    have hb := firstLineBaseMap_smooth hs
    simp +instances only [flatProduct_chartedSpace,chartedSpaceSelf_prod] at hb
    have hdif := manifoldMapDifferential_comp
      (hb.mdifferentiable (by simp) (H x)) (hH.mdifferentiable (by simp) x)
    change manifoldMapDifferential (E := Affine m × Plane) (F := LargeNormalModel m)
      (fun y => J (t,y)) x=_ at hdif
    simp only [manifoldPullbackOneForm] at hc
    change (firstLinePrimitive (Γ t) (H x)).comp
      (manifoldMapDifferential (E := NormalModel m × Plane) (F := LargeNormalModel m) H x)=_
    rw [← hc,ContinuousLinearMap.comp_assoc]
    exact congrArg (fun L => (α t (J (t,x))).comp L) hdif.symm
  have hJform (t : ℝ) (ht : t∈Ioc (0:ℝ) δ) (x : LargeNormalSpace a) (hx : x∈V) :
      manifoldExteriorOneForm (Δ t) x=(euclideanExteriorOneForm (α t) (J (t,x))).bilinearComp
        (manifoldMapDifferential (E := Affine m × Plane) (F := LargeNormalModel m) (fun y => J (t,y)) x)
        (manifoldMapDifferential (E := Affine m × Plane) (F := LargeNormalModel m) (fun y => J (t,y)) x) := by
    rw [manifoldExteriorOneForm_congr_germ (Filter.eventually_of_mem (hV.mem_nhds hx) (hJprim t ht))]
    have ha' : ∀ c : Affine m × Plane, ContDiffOn ℝ ∞ (chartOneForm (α t) c)
        (extChartAt 𝓘(ℝ,Affine m × Plane) c).target := by
      intro c y _hy
      rw [show chartOneForm (α t) c=α t from funext (chartOneForm_model _ _)]
      exact (hα t).contDiffAt.contDiffWithinAt
    have he := manifold_pullback_exterior ha' (hJs t) x
    simpa only [manifoldPullbackTwoForm,manifoldExteriorOneForm_model] using he
  have hinto (t : ℝ) (_ht : t∈Ioc (0:ℝ) δ) :
      MapsTo (fun x => J (t,x)) V {y | radialArea y.2<b} :=
    fun x hx => (hHD x hx.1).1
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,hginto,hgform⟩ := exists_compact_exact_fibre_embedding_into_bp240
    hΔ hK hinv hV hKV hδ hJ hJemb hinto (fun t => euclideanExteriorOneForm (α t)) hJform
  refine ⟨t,ht.1,g,W∩V,hW.inter hV,fun x hx => ⟨hKW hx,hKV hx⟩,hg,
    hgemb.comp (Topology.IsEmbedding.inclusion inter_subset_left),
    fun x hx => hginto hx.1,?_⟩
  intro x hx v w
  have he := hgform x hx.1 v w
  rw [hΔext x hx.2,largeCouplingPrimitive_exterior] at he
  exact he

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_QuadricLargeAmbientPacking
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open Hamiltonian MomentPolytope

 theorem actual_large_polynomial_packing (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) {a₀ : ℝ} (ha₀ : 0<a₀) (ha₁ : a₀<1)
    (hrs : ∀ i,r i<1-a₀) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+4)<1-a₀^(m+4)) :
    ∃ b d t : ℝ,b<1-a₀ ∧ 0<d ∧ d<1/2 ∧ 0<t ∧
      ∃ f : Fin N → Ambient (m+4) → Affine (m+2) × Plane,
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+4) (r' i))
          (fun _ => successorStandardForm (m+3))
          (euclideanExteriorOneForm (firstLinePrimitive
            (normalAmbientPrimitive (parameters m) (1/Real.pi) d t))) (f i)) ∧
        (∀ i,∀ x∈closedBall (m+4) (r' i),radialArea (f i x).2<b) ∧
        Pairwise (fun i j => Disjoint (f i '' closedBall (m+4) (r' i))
          (f j '' closedBall (m+4) (r' j))) := by
  classical
  obtain ⟨h₁,h₂,d₁,d₂,_hr₁,hhd₁,hd₁,hr₂,hhd₂,hd₂,ℓ,φ,hφ,hφK,hdisj⟩ :=
    actual_large_normal_packing_bp240 m r r' hr hr' hrr ha₀ ha₁ hrs hhalf hvol
  let K : Set (LargeNormalSpace (parameters m)) := ⋃ i,φ i '' closedBall (m+4) (r' i)
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hφ i
    exact (closedBall_isCompact (m+4) (r' i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hh₁d₁ : (h₁:ℝ)<d₁ := by exact_mod_cast hhd₁
  have hh₂d₂ : (h₂:ℝ)<d₂ := by exact_mod_cast hhd₂
  have hd : 0<(d₂:ℝ) := by
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    exact ((hr i).trans (hr₂ i)).trans hh₂d₂
  have hKb (x : LargeNormalSpace (parameters m)) (hx : x∈K) :
      radialArea (normalHead (m+2) x.2)<(d₁:ℝ) := by
    obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
    have hm := (interior_subset (hφK i hy)).2.2 0
    simp only [largeModelBounds,Fin.sum_univ_succ,Matrix.cons_val_zero,
      Fin.cons_zero,Fin.cons_succ,zero_mul,Finset.sum_const_zero,
      add_zero,one_mul] at hm
    exact hm.trans_lt hh₁d₁
  have hKd (x : LargeNormalSpace (parameters m)) (hx : x∈K) :
      Real.pi*phaseSq (normalTail (m+2) x.2)<(d₂:ℝ)*(1-radialArea (normalHead (m+2) x.2)) := by
    have hu := hKb x hx
    have hu1 : radialArea (normalHead (m+2) x.2)<1 := hu.trans (by linarith)
    obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
    have hm := (interior_subset (hφK i hy)).2.2 1
    rw [Fin.sum_univ_succ] at hm
    simp only [largeModelBounds,Matrix.cons_val_one,
      Matrix.cons_val_zero,Fin.cons_zero,Fin.cons_succ,one_mul] at hm
    have he : (∑ j : Fin (m+2),planeMoments (φ i y).2 j.succ)=
        Real.pi*phaseSq (normalTail (m+2) (φ i y).2) := by
      simp only [planeMoments,radialArea,radiusSq,phaseSq,phaseDot_apply,
        normalTail,ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply,
        pow_two,← Finset.mul_sum]
    rw [he] at hm
    have hmul := mul_lt_mul_of_pos_right hh₂d₂ (sub_pos.mpr hu1)
    change (h₂:ℝ)*radialArea (normalHead (m+2) (φ i y).2)+_≤(h₂:ℝ) at hm
    linarith
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,hginto,hgform⟩ :=
    exists_actual_large_normal_transfer (parameters m) (by linarith : (d₁:ℝ)<1)
      hd hd₂ hK hKb hKd
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall (m+4) (r' i))
    (fun _ => successorStandardForm (m+3))
    (globalHorizontalCoupling phaseArea (largeHorizontalPrimitive (q := m+2) (parameters m) ∘ planeMoments))
    (euclideanExteriorOneForm (firstLinePrimitive
      (normalAmbientPrimitive (parameters m) (1/Real.pi) d₂ t)))
    hW g hg.contMDiffOn hgemb hgform φ hφ
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hdisj
  exact ⟨d₁,d₂,t,hd₁,hd,hd₂,ht,fun i => g ∘ φ i,hf,
    fun i x hx => hginto _ (hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)),hdj⟩

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Function Filter
open Set
open Manifold
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem primitivePullback_exterior_at {α : F → F →L[ℝ] ℝ} {g : E → F} {x : E}
    (hα : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    euclideanExteriorOneForm (primitivePullback α g) x=
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  have hs : ContDiffAt ℝ ∞ (chartOneForm α (g x)) (extChartAt 𝓘(ℝ,F) (g x) (g x)) := by
    rw [show chartOneForm α (g x)=α from funext (vector_chartOneForm α (g x))]
    simpa only [extChartAt_model_space_eq_id,PartialEquiv.refl_coe,id_eq] using hα
  have hh := manifold_pullback_exterior_at (α := α) (g := g) hs hg.contMDiffAt
  have he : manifoldPullbackOneForm (fun _ => α) g 0=primitivePullback α g := by
    funext z
    simp [manifoldPullbackOneForm,manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback]
  rw [he] at hh
  simpa only [vector_exteriorOneForm,manifoldPullbackOneForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback] using hh

 theorem euclideanExteriorOneForm_congr_nhds {α β : E → E →L[ℝ] ℝ} {x : E}
    (he : α =ᶠ[𝓝 x] β) : euclideanExteriorOneForm α x=euclideanExteriorOneForm β x := by
  simp only [euclideanExteriorOneForm,he.fderiv_eq]

end
section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
 theorem firstDiskDomain_open : IsOpen (firstDiskDomain (V := V)) :=
  isOpen_lt (radialArea_smooth.continuous.comp continuous_snd) continuous_const

 theorem firstDiskScale_isEmbedding :
    Topology.IsEmbedding (fun x : firstDiskDomain (V := V) => firstDiskScale x.val) :=
  Topology.IsEmbedding.subtypeVal.comp firstDiskScaleHomeomorph.isEmbedding

variable {ι : Type} [Fintype ι]

 theorem phasePlusPlanePrimitive_smooth : ContDiff ℝ ∞ (phasePlusPlanePrimitive (ι := ι)) :=
  (((standardLiouville_smooth (ι := ι)).comp contDiff_fst).clm_comp contDiff_const).add
    (((linearLiouville_smooth planarArea).comp contDiff_snd).clm_comp contDiff_const)

 theorem firstDiskRadial_smoothOn (c : ℝ) :
    ContDiffOn ℝ ∞ (firstDiskRadial (ι := ι) c) firstDiskDomain :=
  firstDiskScale_smoothOn.comp
    (((fsBallMap_smooth c).comp contDiff_fst).prodMk contDiff_snd).contDiffOn (fun _ hx => hx)

 theorem firstDiskRadial_isEmbedding {c : ℝ} (hc : 0 < c) :
    Topology.IsEmbedding (fun x : firstDiskDomain (V := PlanePhase ι) => firstDiskRadial c x.val) := by
  have he : Topology.IsEmbedding (fun x : PlanePhase ι × Plane => (fsBallMap c x.1,x.2)) :=
    (fsBallMap_isEmbedding hc).prodMap Topology.IsEmbedding.id
  exact firstDiskScale_isEmbedding.comp
    ((he.comp Topology.IsEmbedding.subtypeVal).codRestrict firstDiskDomain (fun x => x.property))

 theorem firstDiskRadial_primitive {c : ℝ} (hc : 0 ≤ c) {x : PlanePhase ι × Plane}
    (hx : x∈firstDiskDomain) :
    primitivePullback phasePlusPlanePrimitive (firstDiskRadial c) x=
      firstLinePrimitive (affineFSPrimitive c) x := by
  apply ContinuousLinearMap.ext
  intro u
  let s : PlanePhase ι × Plane → ℝ := fun y => Real.sqrt (1-radialArea y.2)
  let w : PlanePhase ι × Plane → PlanePhase ι := fun y => fsBallMap c y.1
  have hs : ContDiffAt ℝ ∞ s x :=
    ((contDiff_const.sub (radialArea_smooth.comp contDiff_snd)).contDiffAt).sqrt (sub_pos.mpr hx).ne'
  have hw : ContDiff ℝ ∞ w := (fsBallMap_smooth c).comp contDiff_fst
  have hD := (((hs.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).smul (hw.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)).hasFDerivAt.prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := x))).fderiv
  change fderiv ℝ (firstDiskRadial c) x=_ at hD
  change phasePlusPlanePrimitive (firstDiskRadial c x) (fderiv ℝ (firstDiskRadial c) x u)=_
  rw [hD]
  change linearLiouville phaseArea (s x • w x) (fderiv ℝ (fun y => s y • w y) x u)+
    linearLiouville planarArea x.2 u.2=_
  rw [linearLiouville_variable_smul phaseArea phaseArea_self (hs.differentiableAt (by simp))
    (hw.differentiable (by simp) x)]
  have hwD := ((fsBallMap_hasFDerivAt c x.1).comp x (hasFDerivAt_fst (𝕜 := ℝ) (p := x))).fderiv
  change fderiv ℝ w x=_ at hwD
  rw [hwD]
  rw [← (fsBallMap_hasFDerivAt c x.1).fderiv]
  change (Real.sqrt (1-radialArea x.2))^2*
    standardLiouville (fsBallMap c x.1) (fderiv ℝ (fsBallMap c) x.1 u.1)+
      linearLiouville planarArea x.2 u.2=_
  rw [Real.sq_sqrt (sub_pos.mpr hx).le,fsBallMap_primitive hc,firstLinePrimitive_apply]
  ring

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_QuadricRelativeShellFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators Manifold
open Set Function

 theorem headComplexAmbient_capacity (n : ℕ) (x : Ambient n × Plane) :
    capacity (headComplexAmbient n x)=capacity x.1+radialArea x.2 := by
  simp only [capacity,Fin.sum_univ_succ,headComplexAmbient_apply,
    Fin.cons_zero,Fin.cons_succ,Complex.normSq_apply,radialArea,radiusSq]
  ring

 theorem headComplexAmbient_form (n : ℕ) (v w : Ambient n × Plane) :
    standardForm (headComplexAmbient n v) (headComplexAmbient n w)=
      standardForm v.1 w.1+planarArea v.2 w.2 := by
  simp only [standardForm,Fin.sum_univ_succ,headComplexAmbient_apply,
    Fin.cons_zero,Fin.cons_succ,planarArea_apply]
  ring

 theorem phasePlusPlaneAmbient_capacity (m : ℕ) (x : PlanePhase (Option (Fin m)) × Plane) :
    capacity (phasePlusPlaneAmbient m x)=Real.pi*phaseSq x.1+radialArea x.2 := by
  rw [phasePlusPlaneAmbient,ContinuousLinearEquiv.trans_apply,headComplexAmbient_capacity]
  exact congrArg (fun t => t+radialArea x.2) (optionPhaseAmbient_capacity m x.1)

 theorem phasePlusPlaneAmbient_form (m : ℕ) (v w : PlanePhase (Option (Fin m)) × Plane) :
    standardForm (phasePlusPlaneAmbient m v) (phasePlusPlaneAmbient m w)=
      phaseArea v.1 w.1+planarArea v.2 w.2 := by
  rw [phasePlusPlaneAmbient,ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.trans_apply,
    headComplexAmbient_form]
  exact congrArg (fun t => t+planarArea v.2 w.2) (optionPhaseAmbient_form m v.1 w.1)

 theorem phasePlusPlaneAmbient_first (m : ℕ) (x : PlanePhase (Option (Fin m)) × Plane) :
    Real.pi*Complex.normSq (phasePlusPlaneAmbient m x 0)=radialArea x.2 := by
  change Real.pi*Complex.normSq (⟨x.2.1,x.2.2⟩ : ℂ)=_
  simp only [Complex.normSq_apply,radialArea,radiusSq,pow_two]

 variable {ι : Type} [Fintype ι]
 theorem phasePlusPlanePrimitive_exterior (x v w : PlanePhase ι × Plane) :
    euclideanExteriorOneForm phasePlusPlanePrimitive x v w=phaseArea v.1 w.1+planarArea v.2 w.2 := by
  let Ω : (PlanePhase ι × Plane) →L[ℝ] (PlanePhase ι × Plane) →L[ℝ] ℝ :=
    phaseArea.bilinearComp (ContinuousLinearMap.fst ℝ _ _) (ContinuousLinearMap.fst ℝ _ _)+
      planarArea.bilinearComp (ContinuousLinearMap.snd ℝ _ _) (ContinuousLinearMap.snd ℝ _ _)
  have hΩ : ∀ v w,Ω v w= -Ω w v := by
    intro v w
    change phaseArea v.1 w.1+planarArea v.2 w.2= -(phaseArea w.1 v.1+planarArea w.2 v.2)
    rw [phaseArea_skew v.1 w.1]
    simp only [planarArea_apply]
    ring
  have he : (phasePlusPlanePrimitive (ι := ι))=linearLiouville Ω := by
    funext y
    apply ContinuousLinearMap.ext
    intro u
    change (1/2:ℝ)*phaseArea y.1 u.1+(1/2:ℝ)*planarArea y.2 u.2=
      (1/2:ℝ)*(phaseArea y.1 u.1+planarArea y.2 u.2)
    ring
  rw [he,← manifoldExteriorOneForm_model,linearLiouville_exterior Ω hΩ]
  rfl

 theorem firstDiskRadial_mem_unit {x : PlanePhase ι × Plane} (hx : x∈firstDiskDomain) :
    Real.pi*phaseSq (firstDiskRadial (1/Real.pi) x).1+
      radialArea (firstDiskRadial (1/Real.pi) x).2<1 := by
  have hu : 0<1-radialArea x.2 := sub_pos.mpr hx
  have hc : 0<(1:ℝ)/Real.pi := one_div_pos.mpr Real.pi_pos
  have hfs := fsBallMap_mem (ι := ι) hc x.1
  change phaseSq (fsBallMap (1/Real.pi) x.1)<1/Real.pi at hfs
  have hb : Real.pi*phaseSq (fsBallMap (1/Real.pi) x.1)<1 := by
    simpa only [mul_comm] using (lt_div_iff₀ Real.pi_pos).mp hfs
  change Real.pi*phaseSq (Real.sqrt (1-radialArea x.2) • fsBallMap (1/Real.pi) x.1)+radialArea x.2<1
  rw [phaseSq_smul,Real.sq_sqrt hu.le]
  nlinarith [mul_lt_mul_of_pos_left hb hu]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian
open scoped Manifold Topology
open Set

 theorem affineLinePhase_primitive (m : ℕ) (c : ℝ) (x : Affine m × Plane) :
    primitivePullback (firstLinePrimitive (affineFSPrimitive c)) (affineLinePhase m) x=
      firstLinePrimitive (ambientFSPrimitive c) x := by
  apply ContinuousLinearMap.ext
  intro u
  change firstLinePrimitive (affineFSPrimitive c) (affineLinePhase m x)
    (fderiv ℝ (affineLinePhase m) x u)=_
  rw [(affineLinePhase m).fderiv,firstLinePrimitive_apply,firstLinePrimitive_apply]
  change linearLiouville planarArea x.2 u.2 + (1-radialArea x.2)*
    affineFSPrimitive c (affinePhaseEquiv m x.1) (affinePhaseEquiv m u.1)=_
  rw [affinePhaseEquiv_apply,affinePhaseEquiv_apply]
  rfl

 theorem affineLineRadial_smoothOn (m : ℕ) :
    ContDiffOn ℝ ∞ (affineLineRadial m) firstDiskDomain :=
  (firstDiskRadial_smoothOn _).comp (affineLinePhase m).contDiff.contDiffOn (fun _ hx => hx)

 theorem affineLineRadial_primitive (m : ℕ) {x : Affine m × Plane} (hx : x∈firstDiskDomain) :
    primitivePullback phasePlusPlanePrimitive (affineLineRadial m) x=
      firstLinePrimitive (ambientFSPrimitive (1/Real.pi)) x := by
  have hg := (firstDiskRadial_smoothOn (ι := Option (Fin m)) (1/Real.pi)).contDiffAt
    (firstDiskDomain_open.mem_nhds (show affineLinePhase m x∈firstDiskDomain from hx))
  apply ContinuousLinearMap.ext
  intro v
  change phasePlusPlanePrimitive (affineLineRadial m x) (fderiv ℝ (affineLineRadial m) x v)=_
  rw [show affineLineRadial m=firstDiskRadial (1/Real.pi) ∘ affineLinePhase m from rfl,
    fderiv_comp x (hg.differentiableAt (by simp)) ((affineLinePhase m).differentiableAt)]
  have he := congrArg (fun L => L (affineLinePhase m v))
    (firstDiskRadial_primitive (one_div_pos.mpr Real.pi_pos).le
      (show affineLinePhase m x∈firstDiskDomain from hx))
  change phasePlusPlanePrimitive (firstDiskRadial (1/Real.pi) (affineLinePhase m x))
    (fderiv ℝ (firstDiskRadial (1/Real.pi)) (affineLinePhase m x) (affineLinePhase m v))=_ at he
  have he' := congrArg (fun L => L v) (affineLinePhase_primitive m (1/Real.pi) x)
  simp only [primitivePullback,ContinuousLinearMap.comp_apply,(affineLinePhase m).fderiv] at he'
  simp only [ContinuousLinearMap.comp_apply,(affineLinePhase m).fderiv]
  convert! he.trans he' using 1
  all_goals try with_reducible_and_instances rfl

 theorem affineLineTarget_smoothOn (m : ℕ) :
    ContDiffOn ℝ ∞ (affineLineTarget m) firstDiskDomain :=
  (phasePlusPlaneAmbient m).contDiff.comp_contDiffOn (affineLineRadial_smoothOn m)

 theorem affineLineTarget_isEmbedding (m : ℕ) :
    Topology.IsEmbedding (fun x : firstDiskDomain (V := Affine m) => affineLineTarget m x.val) := by
  let j : firstDiskDomain (V := Affine m) → firstDiskDomain (V := PlanePhase (Option (Fin m))) :=
    fun x => ⟨affineLinePhase m x.val,x.property⟩
  have hj : Topology.IsEmbedding j :=
    ((affineLinePhase m).toHomeomorph.isEmbedding.comp
      (Topology.IsEmbedding.subtypeVal (p := fun x => x∈firstDiskDomain (V := Affine m)))).codRestrict
      firstDiskDomain (fun x : firstDiskDomain (V := Affine m) => x.property)
  have hr : Topology.IsEmbedding (fun x : firstDiskDomain (V := PlanePhase (Option (Fin m))) =>
      firstDiskRadial (1/Real.pi) x.val) := firstDiskRadial_isEmbedding (one_div_pos.mpr Real.pi_pos)
  have hh := (phasePlusPlaneAmbient m).toHomeomorph.isEmbedding.comp (hr.comp hj)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl

 theorem affineLineTarget_mem (m : ℕ) {x : Affine m × Plane} (hx : x∈firstDiskDomain) :
    affineLineTarget m x∈openBall (m+2) 1 := by
  change capacity (phasePlusPlaneAmbient m (affineLineRadial m x))<1
  rw [phasePlusPlaneAmbient_capacity]
  exact firstDiskRadial_mem_unit (show affineLinePhase m x∈firstDiskDomain from hx)

 theorem affineLineTarget_first (m : ℕ) (x : Affine m × Plane) :
    Real.pi*Complex.normSq (affineLineTarget m x 0)=radialArea x.2 :=
  phasePlusPlaneAmbient_first m (affineLineRadial m x)

 theorem affineLineTarget_pullback (m : ℕ) {x : Affine m × Plane} (hx : x∈firstDiskDomain)
    (v w : Affine m × Plane) :
    standardForm (fderiv ℝ (affineLineTarget m) x v) (fderiv ℝ (affineLineTarget m) x w)=
      euclideanExteriorOneForm (firstLinePrimitive (ambientFSPrimitive (1/Real.pi))) x v w := by
  have hg := (affineLineRadial_smoothOn m).contDiffAt (firstDiskDomain_open.mem_nhds hx)
  have hD := ((phasePlusPlaneAmbient m).hasFDerivAt.comp x (hg.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt).fderiv
  change fderiv ℝ (affineLineTarget m) x=_ at hD
  rw [hD]
  change standardForm (phasePlusPlaneAmbient m (fderiv ℝ (affineLineRadial m) x v))
    (phasePlusPlaneAmbient m (fderiv ℝ (affineLineRadial m) x w))=_
  rw [phasePlusPlaneAmbient_form,← phasePlusPlanePrimitive_exterior (affineLineRadial m x)]
  have he := primitivePullback_exterior_at
    (phasePlusPlanePrimitive_smooth (ι := Option (Fin m))).contDiffAt hg
  have he' := euclideanExteriorOneForm_congr_nhds
    (Filter.eventually_of_mem (firstDiskDomain_open.mem_nhds hx)
      (fun _ hy => affineLineRadial_primitive m hy))
  exact congrArg (fun B => B v w) (he.symm.trans he')

 theorem exists_polynomial_first_line_target {m : ℕ} (a : Fin m → ℂ) (t : ℝ)
    {d : ℝ} (hd : 0≤d) (hdhalf : d<1/2) :
    ∃ g : Affine m × Plane → Ambient (m+2),ContDiffOn ℝ ∞ g firstDiskDomain ∧
      Topology.IsEmbedding (fun x : firstDiskDomain (V := Affine m) => g x.val) ∧
      (∀ x∈firstDiskDomain,g x∈openBall (m+2) 1) ∧
      (∀ x,Real.pi*Complex.normSq (g x 0)=radialArea x.2) ∧
      ∀ x∈firstDiskDomain,∀ v w,standardForm (fderiv ℝ g x v) (fderiv ℝ g x w)=
        euclideanExteriorOneForm (firstLinePrimitive (normalAmbientPrimitive a (1/Real.pi) d t)) x v w := by
  obtain ⟨f,h,θ,hf,hh,hθ,hfh,hhf,he⟩ :=
    exists_quadric_exact_affine_moser_bp240 a t (one_div_pos.mpr Real.pi_pos) hd hdhalf
  let F := firstLineLift f θ
  have hF := firstLineLift_smooth hf hθ
  have hFe := firstLineLift_isEmbedding hf hh hθ hfh hhf
  have hFm (x : Affine m × Plane) : radialArea (F x).2=radialArea x.2 := radialArea_planeRotate _ _
  have hFd : MapsTo F firstDiskDomain firstDiskDomain := fun x hx => by
    change radialArea (F x).2<1
    rw [hFm]
    exact hx
  let j : firstDiskDomain (V := Affine m) → firstDiskDomain (V := Affine m) :=
    fun x => ⟨F x.val,hFd x.property⟩
  have hj : Topology.IsEmbedding j :=
    (hFe.comp Topology.IsEmbedding.subtypeVal).codRestrict _ _
  have hge : Topology.IsEmbedding (fun x : firstDiskDomain (V := Affine m) =>
      (affineLineTarget m ∘ F) x.val) := by
    convert! (affineLineTarget_isEmbedding m).comp hj using 1
    all_goals try with_reducible_and_instances rfl
  refine ⟨affineLineTarget m ∘ F,(affineLineTarget_smoothOn m).comp hF.contDiffOn hFd,
    hge,fun x hx => affineLineTarget_mem m (hFd hx),
    fun x => (affineLineTarget_first m (F x)).trans (hFm x),?_⟩
  intro x hx v w
  have hG := (affineLineTarget_smoothOn m).contDiffAt (firstDiskDomain_open.mem_nhds (hFd hx))
  rw [fderiv_comp x (hG.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)]
  change standardForm (fderiv ℝ (affineLineTarget m) (F x) (fderiv ℝ F x v))
    (fderiv ℝ (affineLineTarget m) (F x) (fderiv ℝ F x w))=_
  rw [affineLineTarget_pullback m (hFd hx)]
  exact congrArg (fun B => B v w) (firstLineLift_exterior (ambientFSPrimitive_smooth _)
    (normalAmbientPrimitive_smooth a _ d t) hf hθ he x)

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Packings_ComplementPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open Hamiltonian DiagonalQuadrics DiagonalQuadrics.Explicit

 theorem actual_complement_packing_bp240_oai (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) {a₀ : ℝ} (ha₀ : 0<a₀) (ha₁ : a₀<1)
    (hrs : ∀ i,r i<1-a₀) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+4)<1-a₀^(m+4)) :
    ∃ b : ℝ,b<1-a₀ ∧ ∃ f : Fin N → Ambient (m+4) → Ambient (m+4),
      (∀ i,IsBallEmbedding (r' i) (f i)) ∧
      (∀ i,f i '' closedBall (m+4) (r' i)⊆openBall (m+4) 1) ∧
      (∀ i,∀ x∈closedBall (m+4) (r' i),Real.pi*Complex.normSq (f i x 0)<b) ∧
      Pairwise (fun i j => Disjoint (f i '' closedBall (m+4) (r' i))
        (f j '' closedBall (m+4) (r' j))) := by
  obtain ⟨b,d,t,hb,hd,hdhalf,_ht,φ,hφ,hφb,hdisj⟩ :=
    actual_large_polynomial_packing m r r' hr hr' hrr ha₀ ha₁ hrs hhalf hvol
  obtain ⟨g,hg,hgemb,hgmem,hgfirst,hgform⟩ :=
    exists_polynomial_first_line_target (parameters m) t hd.le hdhalf
  have hφdom (i : Fin N) : MapsTo (φ i) (closedBall (m+4) (r' i)) firstDiskDomain := by
    intro x hx
    exact (hφb i x hx).trans (by linarith : b<1)
  have hform (x : Affine (m+2) × Plane) (hx : x∈firstDiskDomain) (v w) :
      successorStandardForm (m+3)
        (mfderiv 𝓘(ℝ,Affine (m+2) × Plane) 𝓘(ℝ,Ambient (m+4)) g x v)
        (mfderiv 𝓘(ℝ,Affine (m+2) × Plane) 𝓘(ℝ,Ambient (m+4)) g x w)=
      euclideanExteriorOneForm (firstLinePrimitive
        (normalAmbientPrimitive (parameters m) (1/Real.pi) d t)) x v w := by
    rw [mfderiv_eq_fderiv]
    exact (successorStandardForm_apply _ _ _).trans (hgform x hx v w)
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall (m+4) (r' i))
    (fun _ => successorStandardForm (m+3))
    (euclideanExteriorOneForm (firstLinePrimitive
      (normalAmbientPrimitive (parameters m) (1/Real.pi) d t)))
    (fun _ => successorStandardForm (m+3)) firstDiskDomain_open g
    hg.contMDiffOn hgemb hform φ hφ hφdom hdisj
  refine ⟨b,hb,fun i => g ∘ φ i,
    fun i => isBallEmbedding_iff_formNeighborhoodEmbedding.mpr (hf i),?_,?_,hdj⟩
  · intro i y hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact hgmem _ (hφdom i hx)
  · intro i x hx
    change Real.pi*Complex.normSq (g (φ i x) 0)<b
    rw [hgfirst]
    exact hφb i x hx

end PackingSufficiencySupport

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.actual_complement_packing_bp240_oai := @OAI.PackingSufficiencySupport.actual_complement_packing_bp240_oai
