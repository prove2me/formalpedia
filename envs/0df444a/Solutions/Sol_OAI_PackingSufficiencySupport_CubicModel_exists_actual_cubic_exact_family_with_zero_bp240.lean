-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_exact_family_with_zero_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:50:49.193599+00:00
-- url     : https://prove2.me/submissions/4695c467-be57-40e7-93d4-37614a873d3c

import Mathlib
import Definitions.Def_OAIQ240Bp019

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
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricCurveManifold
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter
section
variable {m : ℕ} (a : Fin m → ℂ) [ha : Fact (Injective a)] [ha0 : Fact (∀ j,a j≠0)]

theorem curve_inclusion_contMDiff :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Affine m) ∞ (Subtype.val : locus a → Affine m) := by
  intro x
  have he : chartAt ℂ x=(normalChartAt a x).sliceChart x := rfl
  rw [contMDiffAt_iff]
  constructor
  · exact continuous_subtype_val.continuousAt
  · have h := (normalChartAt a x).sliceChart_inverse_smooth x
    have hx : (chartAt ℂ x x)∈((normalChartAt a x).sliceChart x).target :=
      ((normalChartAt a x).sliceChart x).map_source (mem_normalChartAt a x)
    have ho := ((normalChartAt a x).sliceChart x).open_target
    have hc := (h _ hx).contDiffAt (ho.mem_nhds hx)
    simpa only [mfld_simps,chartAt_self_eq,he,OpenPartialHomeomorph.refl_apply,
      Function.id_comp,Function.comp_def,chartAt,curveChartedSpace] using hc.contDiffWithinAt

end

end PackingSufficiencySupport.DiagonalQuadrics

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

theorem phaseSq_eq_zero_iff (z : PlanePhase ι) : phaseSq z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    funext i
    have hi : (z i).1*(z i).1+(z i).2*(z i).2 ≤ phaseSq z := by
      rw [phaseSq,phaseDot_apply]
      exact Finset.single_le_sum (f := fun j => (z j).1*(z j).1+(z j).2*(z j).2) (fun j _ =>
        add_nonneg (mul_self_nonneg (z j).1) (mul_self_nonneg (z j).2)) (Finset.mem_univ i)
    rw [hz] at hi
    apply Prod.ext <;> dsimp
    · nlinarith [sq_nonneg (z i).2]
    · nlinarith [sq_nonneg (z i).1]
  · rintro rfl
    simp [phaseSq]

theorem phaseSq_pos {z : PlanePhase ι} (hz : z ≠ 0) : 0 < phaseSq z :=
  lt_of_le_of_ne (phaseSq_nonneg z) (fun h => hz ((phaseSq_eq_zero_iff z).mp h.symm))

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldMapDifferential
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldFormTransport
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
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

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricAnnulusDomain
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit

 theorem polynomial_contDiff : ContDiff ℂ ∞ polynomial := by
  unfold polynomial
  fun_prop

 theorem projection_contDiff : ContDiff ℂ ∞ projection := by
  exact (((contDiff_apply ℂ ℂ 0).comp contDiff_snd).sub contDiff_fst).prodMk
    (((contDiff_apply ℂ ℂ 1).comp contDiff_snd).sub contDiff_fst)

 theorem source_equation_zero (x : BaseCurve) : (x.val.2 0)^2=x.val.1^2-1 := by
  simpa only [parameters_zero] using (mem_locus.mp x.property) 0
 theorem source_equation_one (x : BaseCurve) : (x.val.2 1)^2=x.val.1^2-2 := by
  simpa only [parameters_one] using (mem_locus.mp x.property) 1

 theorem inclusion_polynomial (x : BaseCurve) : polynomial (inclusion x)=0 := by
  have h0 := source_equation_zero x
  have h1 := source_equation_one x
  dsimp [polynomial,inclusion,projection]
  linear_combination (x.val.2 1-x.val.1)*h0-(x.val.2 0-x.val.1)*h1

 theorem inclusion_fst_ne_zero (x : BaseCurve) : (inclusion x).1≠0 := by
  intro h
  have he : x.val.2 0=x.val.1 := sub_eq_zero.mp h
  have h0 := source_equation_zero x
  rw [he] at h0
  have hh : (1:ℂ)=0 := by linear_combination h0
  exact one_ne_zero hh

 theorem recovery_inclusion (x : BaseCurve) : recovery (inclusion x)=x.val := by
  have hv := inclusion_fst_ne_zero x
  have h0 := source_equation_zero x
  have ht : -((inclusion x).1^2+1)/(2*(inclusion x).1)=x.val.1 := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hv)).mpr
    dsimp [inclusion,projection]
    linear_combination -h0
  apply Prod.ext
  · exact ht
  · funext j
    change ![-((inclusion x).1^2+1)/(2*(inclusion x).1)+(inclusion x).1,
      -((inclusion x).1^2+1)/(2*(inclusion x).1)+(inclusion x).2] j=x.val.2 j
    rw [ht]
    fin_cases j <;> simp [inclusion,projection]

 theorem inclusion_contMDiff : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,PlaneBase) ∞ inclusion :=
  projection_contDiff.contMDiff.comp (curve_inclusion_contMDiff (parameters 0))

 theorem recovery_contDiffOn : ContDiffOn ℂ ∞ recovery {z | z.1≠0} := by
  intro z hz
  have ht : ContDiffAt ℂ ∞ (fun z : PlaneBase => -(z.1^2+1)/(2*z.1)) z :=
    ((contDiffAt_fst.pow 2).add contDiffAt_const).neg.div
      (contDiffAt_const.mul contDiffAt_fst) (mul_ne_zero (by norm_num) hz)
  apply ContDiffAt.contDiffWithinAt
  apply ht.prodMk
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j
  · exact ht.add contDiffAt_fst
  · exact ht.add contDiffAt_snd

 theorem inclusion_isEmbedding : Topology.IsEmbedding inclusion := by
  let f : BaseCurve → {z : PlaneBase // z.1≠0} := fun x => ⟨inclusion x,inclusion_fst_ne_zero x⟩
  have hf : Continuous f := inclusion_contMDiff.continuous.subtype_mk _
  have hR : Continuous (fun z : {z : PlaneBase // z.1≠0} => recovery z.val) :=
    recovery_contDiffOn.continuousOn.domRestrict
  have hcomp : (fun z : {z : PlaneBase // z.1≠0} => recovery z.val) ∘ f=
      (Subtype.val : BaseCurve → Affine 2) := funext recovery_inclusion
  have he := Topology.IsEmbedding.of_comp hf hR (hcomp ▸ Topology.IsEmbedding.subtypeVal)
  exact Topology.IsEmbedding.subtypeVal.comp he

 theorem polynomial_hasFDerivAt (z : PlaneBase) : HasFDerivAt polynomial (jacobian z) z := by
  have hv := hasFDerivAt_fst (𝕜 := ℂ) (p := z)
  have hw := hasFDerivAt_snd (𝕜 := ℂ) (p := z)
  have h := (((hv.mul hw).mul (hv.sub hw)).add hw).sub (hv.const_mul 2)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  symm
  change (2*z.1*z.2-z.2^2-2)*v.1+(z.1^2-2*z.1*z.2+1)*v.2=
    z.1*z.2*(v.1-v.2)+(z.1-z.2)*(z.1*v.2+z.2*v.1)+v.2-2*v.1
  ring

 theorem gradient_nonzero {z : PlaneBase} (hz : polynomial z=0) : gradV z≠0 ∨ gradW z≠0 := by
  by_contra h
  push Not at h
  obtain ⟨hv,hw⟩ := h
  have he : z.2=2*z.1 := by
    dsimp [polynomial] at hz
    dsimp [gradV] at hv
    dsimp [gradW] at hw
    linear_combination (3*hz-z.1*hv-z.2*hw)/2
  have hv' : gradV z= -2 := by rw [gradV,he]; ring
  rw [hv'] at hv
  norm_num at hv

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_CubicFubiniStudy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 theorem weightedProjection_contDiff (D m : ℕ) : ContDiff ℂ ∞ (weightedProjection D m) := by
  apply ContDiff.prodMk (contDiff_fst.pow (D-m))
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact contDiff_snd.pow (D-m)
  · exact (contDiff_fst.pow (D-m)).mul (contDiff_snd.pow m)
  · exact (contDiff_fst.pow m).mul (contDiff_snd.pow (D-m))

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_QuadricInfinityPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_vertical _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
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

variable {ι : Type*} [Fintype ι]

theorem complexAffineLift_smooth : ContDiff ℝ ∞ (complexAffineLift (ι := ι)) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | none => exact contDiff_const
  | some i => exact contDiff_apply ℝ ℂ i

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chart_parameterPullbackOneForm {α : ℝ → ManifoldOneForm E M} {g : ℝ × N → M}
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,F)) 𝓘(ℝ,E) ∞ g)
    (c : N) (s t : ℝ) {y : F} (hy : y ∈ (extChartAt 𝓘(ℝ,F) c).target) :
    chartOneForm (parameterPullbackOneForm α g s t) c y =
      (euclideanPullbackOneForm α
        (fun q : ℝ × F => g (q.1,(extChartAt 𝓘(ℝ,F) c).symm q.2)) (t,(s,y))).comp
          (ContinuousLinearMap.inr ℝ ℝ F) := by
  have hs : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (fun x => g (s,x)) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  rw [parameterPullbackOneForm,chartOneForm_manifoldPullback (α := α) (p := (t,y)) hs hy]
  let h : ℝ × F → M := fun q => g (q.1,(extChartAt 𝓘(ℝ,F) c).symm q.2)
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hy)
  have hh : ContMDiffAt 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ h (s,y) :=
    hg.contMDiffAt.comp (s,y) (contDiffAt_fst.contMDiffAt.prodMk
      (hc.comp (s,y) contDiffAt_snd.contMDiffAt))
  have hi : HasMFDerivAt 𝓘(ℝ,F) 𝓘(ℝ,ℝ × F) (fun z => (s,z)) y
      (ContinuousLinearMap.inr ℝ ℝ F) := by
    apply hasMFDerivAt_iff_hasFDerivAt.mpr
    convert! ((hasFDerivAt_const (𝕜 := ℝ) s y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)) using 1
    all_goals try with_reducible_and_instances rfl
  have hd := ((hh.mdifferentiableAt (by simp)).hasMFDerivAt.comp y hi).mfderiv
  simp only [euclideanPullbackOneForm]
  rw [show mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E)
    ((fun x => g (s,x)) ∘ (extChartAt 𝓘(ℝ,F) c).symm) y = _ from hd]
  ext v
  rfl

theorem parameterPullbackOneForm_smooth
    {α : ℝ → ManifoldOneForm E M} {g : ℝ × N → M}
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,F)) 𝓘(ℝ,E) ∞ g)
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (c : N) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × F) =>
      chartOneForm (parameterPullbackOneForm α g q.1 q.2.1) c q.2.2)
      (univ ×ˢ (univ ×ˢ (extChartAt 𝓘(ℝ,F) c).target)) := by
  intro p hp
  let h : ℝ × F → M := fun q => g (q.1,(extChartAt 𝓘(ℝ,F) c).symm q.2)
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hp.2.2)
  have hh : ContMDiffAt 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ h (p.1,p.2.2) :=
    hg.contMDiffAt.comp (p.1,p.2.2) (contDiffAt_fst.contMDiffAt.prodMk
      (hc.comp (p.1,p.2.2) contDiffAt_snd.contMDiffAt))
  have hs := ((euclideanPullbackOneForm_contDiffAt (p := (p.2.1,(p.1,p.2.2))) hα hh).comp p
    (contDiffAt_snd.fst.prodMk (contDiffAt_fst.prodMk contDiffAt_snd.snd))).clm_comp
      (contDiffAt_const (c := ContinuousLinearMap.inr ℝ ℝ F))
  apply (hs.congr_of_eventuallyEq _).contDiffWithinAt
  have ht := continuousAt_snd.snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hp.2.2)
  filter_upwards [ht] with q hq
  exact chart_parameterPullbackOneForm hg c q.1 q.2.1 hq

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem movingPrimitivePullback_smooth {α : F → F →L[ℝ] ℝ} {g : ℝ × M → F}
    (hα : ContDiff ℝ ∞ α)
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ g) :
    SmoothOneFormFamily (movingPrimitivePullback (E := E) α g) := by
  have hα' : SmoothOneFormFamily (fun _ : ℝ => α) := vector_oneForm_smooth hα
  intro c
  exact (parameterPullbackOneForm_smooth (E := F) (F := E) (M := F) (N := M) (α := fun _ : ℝ => α) hg hα' c).comp
    ((contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)).contDiffOn)
    (fun p hp => ⟨mem_univ _,mem_univ _,hp.2⟩)

 theorem movingPrimitivePullback_exterior {α : F → F →L[ℝ] ℝ} {g : ℝ × M → F}
    (hα : ContDiff ℝ ∞ α)
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ g) (t : ℝ) (x : M) :
    manifoldExteriorOneForm (movingPrimitivePullback (E := E) α g t) x=
      (euclideanExteriorOneForm α (g (t,x))).bilinearComp
        (manifoldMapDifferential (E := F) (F := E) (fun y => g (t,y)) x)
        (manifoldMapDifferential (E := F) (F := E) (fun y => g (t,y)) x) := by
  have hh := manifold_pullback_exterior (α := α) (g := fun y => g (t,y))
    (fun c => by
      rw [show chartOneForm α c=α from funext (vector_chartOneForm α c)]
      exact hα.contDiffOn)
    (hg.comp (contMDiff_const.prodMk contMDiff_id)) x
  simpa only [movingPrimitivePullback,manifoldPullbackTwoForm,vector_exteriorOneForm] using hh

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_AnnularChartHelpers
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
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

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

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

variable {ι : Type*} [Fintype ι]

 theorem hopfPrimitive_smoothAt (c : ℝ) {z : PlanePhase ι} (hz : z≠0) :
    ContDiffAt ℝ ∞ (hopfPrimitive c) z := by
  exact (contDiffAt_const.div (contDiffAt_const.mul phaseSq_smooth.contDiffAt)
    (mul_ne_zero (by norm_num) (phaseSq_pos hz).ne')).smul (phaseArea (ι := ι)).contDiff.contDiffAt

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RadialSwap
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.FiniteMoment.Radial

section

open scoped BigOperators Topology ContDiff
open Set Filter Function

theorem lattice_zero (A B : ℕ) : ∃ i : TrapezoidWeight A B,latticeIndex i=(0,0) :=
  ⟨⟨(⟨0,by omega⟩,⟨0,by omega⟩),by simp⟩,rfl⟩


end


open scoped BigOperators Topology ContDiff
open Set Filter Function



end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_ManifoldFormTransport
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

theorem chartField_smoothOn {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (x : M) : ContDiffOn ℝ ∞ (chartField v x) (extChartAt 𝓘(ℝ,E) x).target := by
  have h := (contMDiff_iff.mp hv).2 x (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)
  have hh := h.snd
  change ContDiffOn ℝ ∞ (chartField v x) _ at hh
  apply hh.mono
  intro y hy
  refine ⟨hy,?_⟩
  simp only [Set.mem_preimage, extChartAt_source, TangentBundle.mem_chart_source_iff]
  simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ,E) x).map_target hy

theorem chartCurve_hasMFDerivAt {v : (z : M) → TangentSpace 𝓘(ℝ,E) z}
    (x : M) {f : ℝ → E} {t : ℝ}
    (hf : f t ∈ (extChartAt 𝓘(ℝ,E) x).target)
    (hd : HasDerivAt f (chartField v x (f t)) t) :
    HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) x).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((extChartAt 𝓘(ℝ,E) x).symm (f t)))) := by
  change M → E at v
  let z : M := (extChartAt 𝓘(ℝ,E) x).symm (f t)
  have hz : z ∈ (extChartAt 𝓘(ℝ,E) x).source := (extChartAt 𝓘(ℝ,E) x).map_target hf
  have hz' := mem_extChartAt_source (I := 𝓘(ℝ,E)) z
  have hd' : HasDerivAt f (tangentCoordChange 𝓘(ℝ,E) z x z (v z)) t := hd
  refine ⟨(continuousAt_extChartAt_symm'' hf).comp hd.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt (𝕜 := ℝ) (F := E) ?_⟩
  simp only [mfld_simps,hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt 𝓘(ℝ,E) z ∘ (extChartAt 𝓘(ℝ,E) x).symm) ∘ f) (v z) t
  rw [←tangentCoordChange_self (I := 𝓘(ℝ,E)) (x := z) (z := z) (v := v z) hz',
    ←tangentCoordChange_comp (x := x) ⟨⟨hz',hz⟩,hz'⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ hd'
  apply HasFDerivWithinAt.hasFDerivAt (s := range 𝓘(ℝ,E)) _ (by simp)
  rw [←(extChartAt 𝓘(ℝ,E) x).right_inv hf]
  exact hasFDerivWithinAt_tangentCoordChange ⟨hz,hz'⟩


end

section
open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_global_bounded_trajectory {X : E → E} {L : ℝ≥0}
    (hL : LipschitzWith L X) {B : ℝ≥0} (hB : ∀ x, ‖X x‖ ≤ B) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (X (γ t)) t := by
  have hex (a : ℝ≥0) : ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Icc (-(a:ℝ)) a, HasDerivWithinAt γ (X (γ t)) (Icc (-(a:ℝ)) a) t := by
    let t₀ : Icc (-(a:ℝ)) a := ⟨0, neg_nonpos.mpr a.coe_nonneg, a.coe_nonneg⟩
    have hp : IsPicardLindelof (fun _ : ℝ => X) t₀ x (B*a) 0 B L := {
      lipschitzOnWith := fun _ _ => hL.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ y _ => hB y
      mul_max_le := by simp [t₀] }
    exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose u hu0 hud using hex
  have heq {a b : ℝ≥0} (hab : a ≤ b) : EqOn (u a) (u b) (Ioo (-(a:ℝ)) a) := by
    by_cases ha : a = 0
    · simp [ha]
    · have ha' : (0:ℝ) < a := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ha)
      apply ODE_solution_unique_of_mem_Ioo
        (s := fun _ => univ) (fun _ _ => hL.lipschitzOnWith)
        (t₀ := 0) ⟨by linarith,ha'⟩
        (fun t ht => ⟨(hud a t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2),mem_univ _⟩)
      · intro t ht
        have ht' : t ∈ Ioo (-(b:ℝ)) b := by
          have hab' : (a:ℝ) ≤ b := hab
          constructor <;> linarith [ht.1,ht.2]
        exact ⟨(hud b t (Ioo_subset_Icc_self ht')).hasDerivAt
          (Icc_mem_nhds ht'.1 ht'.2),mem_univ _⟩
      · rw [hu0 a,hu0 b]
  let γ : ℝ → E := fun t => u (‖t‖₊+1) t
  have hmatch {a : ℝ≥0} : EqOn γ (u a) (Ioo (-(a:ℝ)) a) := by
    intro t ht
    have ht' : t ∈ Ioo (-((‖t‖₊+1:ℝ≥0):ℝ)) (‖t‖₊+1:ℝ≥0) := by
      simp only [NNReal.coe_add,NNReal.coe_one,coe_nnnorm,Real.norm_eq_abs]
      exact abs_lt.mp (lt_add_one |t|)
    rcases le_total (‖t‖₊+1) a with h | h
    · exact heq h ht'
    · exact (heq h ht).symm
  refine ⟨γ,?_,?_⟩
  · change u (‖(0:ℝ)‖₊+1) 0 = x
    exact hu0 _
  · intro t
    let a : ℝ≥0 := ‖t‖₊+1
    have ht : t ∈ Ioo (-(a:ℝ)) a := by
      simpa only [a,NNReal.coe_add,NNReal.coe_one,coe_nnnorm,Real.norm_eq_abs,mem_Ioo]
        using abs_lt.mp (lt_add_one |t|)
    have he : γ =ᶠ[𝓝 t] u a := Filter.eventually_of_mem
      (isOpen_Ioo.mem_nhds ht) (fun s hs => hmatch hs)
    have hd := (hud a t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    rw [he.eq_of_nhds]
    exact hd.congr_of_eventuallyEq he


end

section
open scoped ContDiff Topology NNReal
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem stepEndpoint_eq_trajectory {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖*L < 1) {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) :
    stepEndpoint X hX h (γ 0) = γ h := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)
  let u : C(Time,E) := ⟨fun s => γ (h*(s:ℝ)),
    hγc.comp (continuous_const.mul continuous_subtype_val)⟩
  have hu0 : u ⟨0,by simp⟩ = γ 0 := by simp [u]
  have hud (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (extendPath u) (h • X (extendPath u s)) s := by
    have he : extendPath u =ᶠ[𝓝 s] (fun t => γ (h*t)) := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with t ht
      exact extendPath_coe u ⟨t,ht⟩
    have hd := (hγ (h*s)).scomp s (hasDerivAt_const_mul h)
    rw [he.eq_of_nhds]
    exact hd.congr_of_eventuallyEq he
  have he := fixedStep_eq_solution X hX hh u (γ 0) hu0 hud
  have he' := congrArg (fun v : C(Time,E) => v ⟨1,by simp⟩) he
  simpa only [stepEndpoint,u,ContinuousMap.coe_mk,mul_one] using he'

theorem shortFlow_zero {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (x : E) :
    shortFlow X hX (0,x) = x := by
  have he := fixedStep_equation X hX (h := 0) (by simp) x
  simp only [zero_smul,add_zero] at he
  change fixedStep X hX 0 x ⟨1,by simp⟩ = x
  rw [he]
  rfl

variable [FiniteDimensional ℝ E]

theorem shortFlow_smoothOn {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) :
    ContDiffOn ℝ ∞ (shortFlow X hX) {p : ℝ × E | ‖p.1‖*(L:ℝ) < 1} := by
  have hc := (localPath_smooth X hX hXs).comp
    (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun p hp => hp)
  exact (ContinuousMap.evalCLM (M := E) ℝ (⟨1,by simp⟩ : Time)).contDiff.comp_contDiffOn hc

omit [FiniteDimensional ℝ E] in

theorem shortFlow_derivative {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (hXc : HasCompactSupport X) {t : ℝ} (ht : ‖t‖*(L:ℝ) < 1) (x : E) :
    HasDerivAt (fun s => shortFlow X hX (s,x)) (X (shortFlow X hX (t,x))) t := by
  obtain ⟨B,hB⟩ := X.continuous.bounded_above_of_compact_support hXc
  have hB0 : 0 ≤ B := (norm_nonneg (X x)).trans (hB x)
  obtain ⟨γ,hγ0,hγd⟩ := exists_global_bounded_trajectory hX (B := ⟨B,hB0⟩) hB x
  have hopen : IsOpen {s : ℝ | ‖s‖*(L:ℝ) < 1} :=
    isOpen_lt (continuous_id.norm.mul continuous_const) continuous_const
  have he : (fun s => shortFlow X hX (s,x)) =ᶠ[𝓝 t] γ := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    change stepEndpoint X hX s x = γ s
    rw [←hγ0]
    exact stepEndpoint_eq_trajectory X hX hs hγd
  rw [he.eq_of_nhds]
  exact (hγd t).congr_of_eventuallyEq he


end

section
open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_smooth_local_manifold_flow
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (x : M) : ∃ (ε : ℝ) (U : Set E) (Φ : ℝ × E → M),
      0 < ε ∧ IsOpen U ∧ extChartAt 𝓘(ℝ,E) x x ∈ U ∧ U ⊆ (extChartAt 𝓘(ℝ,E) x).target ∧
      ContMDiffOn 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞ Φ (Ioo (-ε) ε ×ˢ U) ∧
      (∀ y ∈ U, Φ (0,y) = (extChartAt 𝓘(ℝ,E) x).symm y) ∧
      (∀ y ∈ U, IsMIntegralCurveOn (fun t => Φ (t,y)) v (Ioo (-ε) ε)) := by
  let c := extChartAt 𝓘(ℝ,E) x x
  have hc : c ∈ (extChartAt 𝓘(ℝ,E) x).target := mem_extChartAt_target x
  have hT := isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x
  obtain ⟨χ,_,_,_,_,_,hXs,hXc,hEq⟩ := exists_smooth_compact_extension
    (isCompact_singleton (x := c)) hT (singleton_subset_iff.mpr hc) (chartField_smoothOn hv x)
  let X : C(E,E) := ⟨fun y => χ y • chartField v x y,hXs.continuous⟩
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq : ∀ᶠ y in 𝓝 c, X y = chartField v x y := by
    simpa only [nhdsSet_singleton,X,ContinuousMap.coe_mk] using hEq
  have hnb : {y | X y = chartField v x y ∧ y ∈ (extChartAt 𝓘(ℝ,E) x).target} ∈ 𝓝 c :=
    heq.and (hT.mem_nhds hc)
  obtain ⟨V,hVsub,hVo,hcV⟩ := mem_nhds_iff.mp hnb
  let D : Set (ℝ × E) := {p | ‖p.1‖*(L:ℝ) < 1}
  have hDo : IsOpen D := isOpen_lt (continuous_fst.norm.mul continuous_const) continuous_const
  have hcD : ((0,c) : ℝ × E) ∈ D := by simp [D]
  have hflowc : ContinuousAt (shortFlow X hL) (0,c) :=
    ((shortFlow_smoothOn X hL hXs).contDiffAt (hDo.mem_nhds hcD)).continuousAt
  have hpV : (shortFlow X hL) ⁻¹' V ∈ 𝓝 ((0,c) : ℝ × E) := by
    apply hflowc.preimage_mem_nhds
    rw [shortFlow_zero]
    exact hVo.mem_nhds hcV
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hDo.mem_nhds hcD) hpV)
  let U : Set E := Metric.ball c δ
  have hroom {t : ℝ} (ht : t ∈ Ioo (-δ) δ) {y : E} (hy : y ∈ U) :
      (t,y) ∈ D ∧ shortFlow X hL (t,y) ∈ V := by
    apply hball
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨by simpa only [dist_zero_right,Real.norm_eq_abs] using (abs_lt.mpr ht),hy⟩
  have hUtarget : U ⊆ (extChartAt 𝓘(ℝ,E) x).target := by
    intro y hy
    have hm := (hroom (t := 0) ⟨by linarith,hδ⟩ hy).2
    rw [shortFlow_zero] at hm
    exact (hVsub hm).2
  let Φ : ℝ × E → M := (extChartAt 𝓘(ℝ,E) x).symm ∘ shortFlow X hL
  refine ⟨δ,U,Φ,hδ,Metric.isOpen_ball,Metric.mem_ball_self hδ,hUtarget,?_,?_,?_⟩
  · apply (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) x).comp
      ((shortFlow_smoothOn X hL hXs).mono (fun p hp => (hroom hp.1 hp.2).1)).contMDiffOn
    intro p hp
    exact (hVsub (hroom hp.1 hp.2).2).2
  · intro y _
    change (extChartAt 𝓘(ℝ,E) x).symm (shortFlow X hL (0,y)) = _
    rw [shortFlow_zero]
  · intro y hy t ht
    have hm := hroom ht hy
    have hd := shortFlow_derivative X hL hXc hm.1 y
    rw [(hVsub hm.2).1] at hd
    exact (chartCurve_hasMFDerivAt x (hVsub hm.2).2 hd).hasMFDerivWithinAt

theorem exists_smooth_local_manifold_family
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (x : M) : ∃ (ε : ℝ) (W : Set M) (Ψ : ℝ × M → M),
      0 < ε ∧ IsOpen W ∧ x ∈ W ∧
      ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ (Ioo (-ε) ε ×ˢ W) ∧
      (∀ y ∈ W, Ψ (0,y) = y) ∧
      (∀ y ∈ W, IsMIntegralCurveOn (fun t => Ψ (t,y)) v (Ioo (-ε) ε)) := by
  obtain ⟨ε,U,Φ,hε,hU,hxU,_,hΦ,hΦ0,hΦd⟩ := exists_smooth_local_manifold_flow hv x
  let e := extChartAt 𝓘(ℝ,E) x
  let W : Set M := e.source ∩ e ⁻¹' U
  have hW : IsOpen W := (continuousOn_extChartAt x).isOpen_inter_preimage
    (isOpen_extChartAt_source x) hU
  have hxW : x ∈ W := ⟨mem_extChartAt_source x,hxU⟩
  let Ψ : ℝ × M → M := fun p => Φ (p.1,e p.2)
  refine ⟨ε,W,Ψ,hε,hW,hxW,?_,?_,?_⟩
  · have hc : ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : ℝ × M => e p.2) (Ioo (-ε) ε ×ˢ W) :=
      (contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (x := x)).comp contMDiff_snd.contMDiffOn
        (fun p hp => by
          change p.2 ∈ (chartAt E x).source
          simpa only [e,extChartAt_source] using hp.2.1)
    exact hΦ.comp (contMDiff_fst.contMDiffOn.prodMk_space hc) (fun _ hp => ⟨hp.1,hp.2.2⟩)
  · intro y hy
    exact (hΦ0 (e y) hy.2).trans (e.left_inv hy.1)
  · intro y hy
    exact hΦd (e y) hy.2


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_uniform_smooth_manifold_families
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hvK : ∀ x, x ∉ K → v x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : M, ∃ (W : Set M) (Ψ : ℝ × M → M),
      IsOpen W ∧ x ∈ W ∧
      ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ (Ioo (-ε) ε ×ˢ W) ∧
      (∀ y ∈ W, Ψ (0,y) = y) ∧
      (∀ y ∈ W, IsMIntegralCurveOn (fun t => Ψ (t,y)) v (Ioo (-ε) ε)) := by
  classical
  choose ε W Ψ hε hW hxW hΨs hΨ0 hΨd using exists_smooth_local_manifold_family hv
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover W hW (fun x _ => mem_iUnion.mpr ⟨x,hxW x⟩)
  have hsmall : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, δ ≤ ε x := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ,hδ,hδs⟩ := ih
      refine ⟨min (ε a) δ,lt_min (hε a) hδ,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hδs x hx)
  obtain ⟨δ,hδ,hδs⟩ := hsmall
  refine ⟨δ,hδ,fun x => ?_⟩
  by_cases hx : x ∈ K
  · obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hs hx)
    have hI : Ioo (-δ) δ ⊆ Ioo (-ε a) (ε a) :=
      Ioo_subset_Ioo (neg_le_neg (hδs a ha)) (hδs a ha)
    exact ⟨W a,Ψ a,hW a,hxa,(hΨs a).mono (prod_mono hI Subset.rfl),
      hΨ0 a,fun y hy => (hΨd a y hy).mono hI⟩
  · exact ⟨Kᶜ,Prod.snd,hK.isClosed.isOpen_compl,hx,contMDiff_snd.contMDiffOn,
      fun _ _ => rfl,fun y hy => (isMIntegralCurve_const (hvK y hy)).isMIntegralCurveOn _⟩

theorem exists_global_compact_manifold_trajectory
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hvK : ∀ x, x ∉ K → v x = 0) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε,hε,h⟩ := exists_uniform_smooth_manifold_families hv hK hvK
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn (hv.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hε _ x
  intro y
  obtain ⟨W,Ψ,_,hy,_,hΨ0,hΨd⟩ := h y
  exact ⟨fun t => Ψ (t,y),hΨ0 y hy,hΨd y hy⟩



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_FlowSmoothExtension
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
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem flow_smooth_of_uniform_local
    (F : ℝ × M → M) (hzero : ∀ x, F (0,x) = x)
    (hadd : ∀ s t x, F (s+t,x) = F (s,F (t,x)))
    {ε : ℝ} (hε : 0 < ε)
    (hs : ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F (Ioo (-ε) ε ×ˢ univ)) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F := by
  have hshort (t : ℝ) (ht : t ∈ Ioo (-ε) ε) (x : M) :
      ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F (t,x) :=
    hs.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)
  have hmultiple (n : ℕ) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) (x : M) :
      ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : ℝ × M => F ((n:ℝ)*p.1,p.2)) (t,x) := by
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_mul,hzero] using
        (contMDiffAt_snd : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Prod.snd (t,x))
    | succ n ih =>
      have h := (hshort t ht (F ((n:ℝ)*t,x))).comp (t,x) (contMDiffAt_fst.prodMk ih)
      have he : (fun p : ℝ × M => F (((n+1:ℕ):ℝ)*p.1,p.2)) =
          (fun p : ℝ × M => F (p.1,F ((n:ℝ)*p.1,p.2))) := by
        funext p
        rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm,hadd]
      rw [he]
      exact h
  intro p
  obtain ⟨n,hn⟩ := exists_nat_gt (max (|p.1|/ε) 1)
  have hn0 : (0:ℝ) < n := lt_trans (by norm_num) ((le_max_right _ _).trans_lt hn)
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hn0
  have ht : p.1/(n:ℝ) ∈ Ioo (-ε) ε := by
    apply abs_lt.mp
    rw [abs_div,abs_of_pos hn0,div_lt_iff₀ hn0]
    have hb := (div_lt_iff₀ hε).mp ((le_max_left _ _).trans_lt hn)
    simpa only [mul_comm] using hb
  have hc : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞
      (fun q : ℝ × M => (q.1/(n:ℝ),q.2)) :=
    ((contDiff_id.div_const (n:ℝ)).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  have h := (hmultiple n (p.1/n) ht p.2).comp p hc.contMDiffAt
  have hcancel (r : ℝ) : (n:ℝ)*(r/(n:ℝ)) = r := by field_simp
  simpa only [Function.comp_def,hcancel] using h


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_smooth_global_manifold_flow
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hvK : ∀ x, x ∉ K → v x = 0) :
    ∃ F : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F ∧
      (∀ x, F (0,x) = x) ∧
      (∀ s t x, F (s+t,x) = F (s,F (t,x))) ∧
      (∀ x, IsMIntegralCurve (fun t => F (t,x)) v) ∧
      (∀ x, v x = 0 → ∀ t, F (t,x) = x) := by
  classical
  choose γ hγ0 hγd using exists_global_compact_manifold_trajectory hv hK hvK
  let F : ℝ × M → M := fun p => γ p.2 p.1
  have hF0 (x : M) : F (0,x) = x := hγ0 x
  have hFd (x : M) : IsMIntegralCurve (fun t => F (t,x)) v := hγd x
  have hv1 : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
      (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)) := hv.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hFa (s t : ℝ) (x : M) : F (s+t,x) = F (s,F (t,x)) := by
    have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv1
      ((hFd x).comp_add t) (hFd (F (t,x))) (by simp only [Function.comp_apply,zero_add,hF0])
    exact congrFun he s
  obtain ⟨ε,hε,hfamilies⟩ := exists_uniform_smooth_manifold_families hv hK hvK
  have hFs : ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F (Ioo (-ε) ε ×ˢ univ) := by
    intro p hp
    obtain ⟨W,Ψ,hW,hpW,hΨs,hΨ0,hΨd⟩ := hfamilies p.2
    have heq : EqOn F Ψ (Ioo (-ε) ε ×ˢ W) := by
      intro q hq
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (t₀ := 0) ⟨neg_lt_zero.mpr hε,hε⟩ hv1 ((hFd q.2).isMIntegralCurveOn _)
        (hΨd q.2 hq.2) ((hF0 q.2).trans (hΨ0 q.2 hq.2).symm) hq.1
    have hnb : Ioo (-ε) ε ×ˢ W ∈ 𝓝 p := (isOpen_Ioo.prod hW).mem_nhds ⟨hp.1,hpW⟩
    exact ((hΨs.contMDiffAt hnb).congr_of_eventuallyEq
      (Filter.mem_of_superset hnb heq)).contMDiffWithinAt
  refine ⟨F,flow_smooth_of_uniform_local F hF0 hFa hε hFs,hF0,hFa,hFd,?_⟩
  intro x hx t
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv1
    (hFd x) (isMIntegralCurve_const hx) (hF0 x)
  exact congrFun he t



end

open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_MovingPrimitiveNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem movingPrimitivePullback_exterior_comp
    {α : F → F →L[ℝ] ℝ} {g : ℝ × M → F} {A : G → F} {h : M → G}
    (hα : ContDiff ℝ ∞ α)
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ g)
    (hA : ContDiff ℝ ∞ A) (hh : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ h)
    {t : ℝ} {x : M} (he : (fun y => g (t,y)) =ᶠ[𝓝 x] A ∘ h) :
    manifoldExteriorOneForm (movingPrimitivePullback (E := E) α g t) x=
      (euclideanExteriorOneForm (primitivePullback α A) (h x)).bilinearComp
        (manifoldMapDifferential (E := G) (F := E) h x)
        (manifoldMapDifferential (E := G) (F := E) h x) := by
  rw [movingPrimitivePullback_exterior hα hg,primitivePullback_exterior hα hA]
  have hd : manifoldMapDifferential (E := F) (F := E) (fun y => g (t,y)) x=
      (fderiv ℝ A (h x)).comp (manifoldMapDifferential (E := G) (F := E) h x) := by
    unfold manifoldMapDifferential
    rw [he.mfderiv_eq]
    rw [mfderiv_comp x (hA.contMDiff.mdifferentiable (by simp) (h x))
      (hh.mdifferentiable (by simp) x)]
    rw [mfderiv_eq_fderiv]
    rfl
  rw [hd,he.eq_of_nhds]
  ext u v
  rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.NormalLift
open scoped ContDiff InnerProduct Topology
open Set Function
section

variable {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem gram_invertible {A : E →L[ℝ] F} (hA : Surjective A) :
    (gram A).IsInvertible := by
  have ha : Injective (adjointCLM A) := by
    apply LinearMap.ker_eq_bot.mp
    change (ContinuousLinearMap.adjoint A).ker=⊥
    rw [← A.orthogonal_range]
    have hr : A.range=⊤ := LinearMap.range_eq_top.mpr hA
    rw [hr,Submodule.top_orthogonal_eq_bot]
  have hg : Injective (gram A) := A.self_comp_adjoint_injective_iff.mpr ha
  have hb : Bijective (gram A) := ⟨hg,LinearMap.surjective_of_injective hg⟩
  exact ⟨(LinearEquiv.ofBijective (gram A).toLinearMap hb).toContinuousLinearEquiv,rfl⟩

theorem rightLift_right_inverse {A : E →L[ℝ] F} (hA : Surjective A) (v : F) :
    A (rightLift A v)=v := (gram_invertible hA).self_apply_inverse v

theorem gram_contDiff : ContDiff ℝ ∞ (gram : (E →L[ℝ] F) → (F →L[ℝ] F)) :=
  contDiff_id.clm_comp (adjointCLM : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E)).contDiff

theorem rightLift_contDiffAt {A : E →L[ℝ] F} (hA : Surjective A) :
    ContDiffAt ℝ ∞ rightLift A := by
  exact (adjointCLM : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E)).contDiff.contDiffAt.clm_comp
    ((gram_invertible hA).contDiffAt_map_inverse.comp A gram_contDiff.contDiffAt)

end

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

variable {E F}

theorem hilbertArrow_surjective {A : E →L[ℝ] F} (hA : Surjective A) :
    Surjective (hilbertArrow E F A) := by
  intro y
  obtain ⟨x,hx⟩ := hA ((hilbertEquiv F).symm y)
  refine ⟨hilbertEquiv E x,?_⟩
  change hilbertEquiv F (A ((hilbertEquiv E).symm (hilbertEquiv E x)))=y
  rw [ContinuousLinearEquiv.symm_apply_apply,hx,ContinuousLinearEquiv.apply_symm_apply]

theorem finiteRightLift_right_inverse {A : E →L[ℝ] F} (hA : Surjective A) (v : F) :
    A (finiteRightLift E F A v)=v := by
  apply (hilbertEquiv F).injective
  exact (rightLift_right_inverse (hilbertArrow_surjective hA) ((hilbertEquiv F) v))

theorem finiteRightLift_contDiffAt {A : E →L[ℝ] F} (hA : Surjective A) :
    ContDiffAt ℝ ∞ (finiteRightLift E F) A := by
  exact (((hilbertEquiv F).symm).arrowCongr (hilbertEquiv E).symm).contDiff.contDiffAt.comp A
    ((rightLift_contDiffAt (hilbertArrow_surjective hA)).comp A
      (hilbertArrow E F).contDiff.contDiffAt)

end PackingSufficiencySupport.NormalLift
end

section

open scoped Topology
open Set
namespace PackingSufficiencySupport.Hamiltonian
variable {M : Type*} [TopologicalSpace M]

theorem exists_uniform_short_transport
    {Φ : ℝ × M → M} (hΦ : Continuous Φ) (h0 : ∀ x, Φ (0,x) = x)
    {K O : Set M} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : Set M, IsOpen W ∧ K ⊆ W ∧ W ⊆ O ∧
      ∀ t ∈ Icc (-ε) ε, ∀ x ∈ W, Φ (t,x) ∈ O := by
  have hsub : ({0} : Set ℝ) ×ˢ K ⊆ Φ ⁻¹' O := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    rcases ht with rfl
    simpa only [mem_preimage,h0] using hKO hx
  obtain ⟨U,W,hU,hW,h0U,hKW,hUW⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hO.preimage hΦ) hsub
  obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp hU 0 (h0U (mem_singleton 0))
  refine ⟨δ/2,by positivity,W ∩ O,hW.inter hO,fun x hx => ⟨hKW hx,hKO hx⟩,
    inter_subset_right,?_⟩
  intro t ht x hx
  apply hUW
  refine ⟨hδU ?_,hx.1⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
  constructor <;> linarith [ht.1,ht.2]

end PackingSufficiencySupport.Hamiltonian

end

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_compact_localized_manifold_flow
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞
      (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K O : Set M} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ Φ : ℝ × M → M, ∃ ε : ℝ, 0 < ε ∧ ∃ W : Set M,
      IsOpen W ∧ K ⊆ W ∧ W ⊆ O ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
      (∀ x, Φ (0,x) = x) ∧
      (∀ s t x, Φ (s+t,x) = Φ (s,Φ (t,x))) ∧
      (∀ t ∈ Icc (-ε) ε, ∀ x ∈ W, Φ (t,x) ∈ O) ∧
      (∀ x ∈ W, ∀ t ∈ Icc (-ε) ε, HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
        (fun r => Φ (r,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (Φ (t,x))))) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  obtain ⟨C,hC,hKC,hCO⟩ := exists_compact_between hK hO hKO
  obtain ⟨χ,hχ1,hχ0,_⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ,E) hK.isClosed hKC
  obtain ⟨U,hU,hKU,hUχ⟩ := mem_nhdsSet_iff_exists.mp hχ1
  let v' : (x : M) → TangentSpace 𝓘(ℝ,E) x := fun x => χ x • v x
  have hv' : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞
      (fun x => (⟨x,v' x⟩ : TangentBundle 𝓘(ℝ,E) M)) :=
    χ.contMDiff.smul_section hv
  obtain ⟨Φ,hΦ,hΦ0,hΦa,hΦd,_⟩ := exists_smooth_global_manifold_flow hv' hC
    (fun x hx => by simp only [v',hχ0 x hx,zero_smul])
  obtain ⟨ε,hε,W,hW,hKW,hWO,hstay⟩ := exists_uniform_short_transport hΦ.continuous hΦ0
    hK (hU.inter hO) (fun x hx => ⟨hKU hx,hKO hx⟩)
  refine ⟨Φ,ε,hε,W,hW,hKW,fun x hx => (hWO hx).2,hΦ,hΦ0,hΦa,
    fun t ht x hx => (hstay t ht x hx).2,?_⟩
  intro x hx t ht
  have hd := hΦd x t
  have he : v' (Φ (t,x)) = v (Φ (t,x)) := by
    have hχx : χ (Φ (t,x)) = 1 := hUχ (hstay t ht x hx).1
    simp only [v',hχx,one_smul]
  simpa only [he] using hd

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.NormalLift
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem curve_eq_add_of_hasDerivAt {γ : ℝ → F} {b : F} {ε : ℝ} (hε : 0<ε)
    (hd : ∀ t∈Icc (-ε) ε, HasDerivAt γ b t) {t : ℝ} (ht : t∈Icc (-ε) ε) :
    γ t=γ 0+t•b := by
  have hd0 (s : ℝ) (hs : s∈Icc (-ε) ε) :
      HasDerivAt (fun r => γ r-r•b) 0 s := by
    convert! (hd s hs).sub ((hasDerivAt_id s).smul_const b) using 1; simp
  have he := (convex_Icc (-ε) ε).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd0 s hs).hasDerivWithinAt)
    (fun _ _ => (by simp : ‖(0:F)‖≤(0:ℝ)))
    (show (0:ℝ)∈Icc (-ε) ε by constructor <;> linarith) ht
  have he' : γ t-t•b=γ 0 := by
    simpa only [zero_smul,sub_zero,zero_mul,norm_le_zero_iff,sub_eq_zero] using he
  exact sub_eq_iff_eq_add.mp he'

theorem exists_compact_normal_flow {f : E → F} (hf : ContDiff ℝ ∞ f)
    {B : E → F →L[ℝ] E} (hB : ContDiff ℝ ∞ B)
    {O : Set E} (hO : IsOpen O) (hproj : ∀ z∈O,∀ w,fderiv ℝ f z (B z w)=w)
    {K : Set E} {H : Set F} (hK : IsCompact K) (hH : IsCompact H) (hKO : K⊆O) :
    ∃ Φ : ℝ × (E × F) → E × F, ∃ ε : ℝ, 0<ε ∧ ∃ W : Set (E × F),
      IsOpen W ∧ K×ˢH⊆W ∧ W⊆O×ˢuniv ∧ ContDiff ℝ ∞ Φ ∧
      (∀ p,Φ (0,p)=p) ∧ (∀ s t p,Φ (s+t,p)=Φ (s,Φ (t,p))) ∧
      (∀ p∈W,∀ t∈Icc (-ε) ε,(Φ (t,p)).2=p.2) ∧
      (∀ p∈W,∀ t∈Icc (-ε) ε,f (Φ (t,p)).1=f p.1+t•p.2) ∧
      (∀ p∈W,∀ t∈Icc (-ε) ε,(Φ (t,p)).1∈O) ∧
      ∀ p∈W,∀ t∈Icc (-ε) ε,
        HasDerivAt (fun s => (Φ (s,p)).1) (B (Φ (t,p)).1 p.2) t := by
  let V : E × F → E × F := fun p => (B p.1 p.2,0)
  have hV : ContDiff ℝ ∞ V :=
    ((hB.comp contDiff_fst).clm_apply contDiff_snd).prodMk contDiff_const
  have hVm : ContMDiff 𝓘(ℝ,E×F) (𝓘(ℝ,E×F)).tangent ∞
      (fun p => (⟨p,V p⟩ : TangentBundle 𝓘(ℝ,E×F) (E×F))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hV
  obtain ⟨Φ,ε,hε,W,hW,hKW,hWO,hΦ,hΦ0,hΦa,hstay,hODE⟩ :=
    exists_compact_localized_manifold_flow hVm (hK.prod hH) (hO.prod isOpen_univ)
      (fun p hp => ⟨hKO hp.1,mem_univ _⟩)
  have hΦs : ContDiff ℝ ∞ Φ := by
    rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hΦ
    exact contMDiff_iff_contDiff.mp hΦ
  have hd (p : E×F) (hp : p∈W) (t : ℝ) (ht : t∈Icc (-ε) ε) :
      HasDerivAt (fun s => Φ (s,p)) (V (Φ (t,p))) t := by
    rw [hasDerivAt_iff_hasFDerivAt]
    exact hasMFDerivAt_iff_hasFDerivAt.mp (hODE p hp t ht)
  have hparam (p : E×F) (hp : p∈W) (t : ℝ) (ht : t∈Icc (-ε) ε) :
      (Φ (t,p)).2=p.2 := by
    have hd2 (s : ℝ) (hs : s∈Icc (-ε) ε) :
        HasDerivAt (fun r => (Φ (r,p)).2) 0 s :=
      (ContinuousLinearMap.snd ℝ E F).hasFDerivAt.comp_hasDerivAt s (hd p hp s hs)
    simpa only [hΦ0,smul_zero,add_zero] using curve_eq_add_of_hasDerivAt hε hd2 ht
  have hd1 (p : E×F) (hp : p∈W) (t : ℝ) (ht : t∈Icc (-ε) ε) :
      HasDerivAt (fun s => (Φ (s,p)).1) (B (Φ (t,p)).1 p.2) t := by
    have hd' := (ContinuousLinearMap.fst ℝ E F).hasFDerivAt.comp_hasDerivAt t (hd p hp t ht)
    simpa only [V,ContinuousLinearMap.coe_fst',Function.comp_def,hparam p hp t ht] using hd'
  refine ⟨Φ,ε,hε,W,hW,hKW,hWO,hΦs,hΦ0,hΦa,hparam,?_,
    fun p hp t ht => (hstay t ht p hp).1,hd1⟩
  intro p hp t ht
  have hdf (s : ℝ) (hs : s∈Icc (-ε) ε) :
      HasDerivAt (fun r => f (Φ (r,p)).1) p.2 s := by
    have hc := (hf.differentiable (by simp) (Φ (s,p)).1).hasFDerivAt.comp_hasDerivAt s
      (hd1 p hp s hs)
    simpa only [hproj _ (hstay s hs p hp).1,Function.comp_def] using hc
  simpa only [hΦ0] using curve_eq_add_of_hasDerivAt hε hdf ht

end PackingSufficiencySupport.NormalLift

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open NormalLift Hamiltonian DiagonalQuadrics DiagonalQuadrics.Explicit

theorem regularLocus_isOpen : IsOpen regularLocus := by
  have hv : Continuous gradV := by unfold gradV; fun_prop
  have hw : Continuous gradW := by unfold gradW; fun_prop
  exact (isOpen_ne_fun hv continuous_const).union (isOpen_ne_fun hw continuous_const)

theorem regular_jacobian_surjective {z : PlaneBase} (hz : z∈regularLocus) :
    Surjective (jacobian z) := by
  rcases hz with hv | hw
  · intro w
    refine ⟨(w/gradV z,0),?_⟩
    simp [jacobian,mul_div_cancel₀ _ hv]
  · intro w
    refine ⟨(0,w/gradW z),?_⟩
    simp [jacobian,mul_div_cancel₀ _ hw]

theorem realJacobian_contDiff : ContDiff ℝ ∞ realJacobian := by
  have he : realJacobian=fderiv ℝ polynomial :=
    funext fun z => ((polynomial_hasFDerivAt z).restrictScalars ℝ).fderiv.symm
  rw [he]
  exact (polynomial_contDiff.restrict_scalars ℝ).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

theorem normalLift_projects {z : PlaneBase} (hz : z∈regularLocus) (w : ℂ) :
    realJacobian z (normalLift z w)=w :=
  finiteRightLift_right_inverse (regular_jacobian_surjective hz) w

theorem normalLift_contDiffOn : ContDiffOn ℝ ∞ normalLift regularLocus := by
  intro z hz
  exact ((finiteRightLift_contDiffAt (regular_jacobian_surjective hz)).comp z
    realJacobian_contDiff.contDiffAt).contDiffWithinAt

theorem exists_compact_normal_lift {K : Set PlaneBase} (hK : IsCompact K)
    (hK0 : ∀ z∈K,polynomial z=0) :
    ∃ B : PlaneBase → ℂ →L[ℝ] PlaneBase,
      ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧ ∃ O : Set PlaneBase,
      IsOpen O ∧ K⊆O ∧ O⊆regularLocus ∧
      ∀ z∈O,∀ w,realJacobian z (B z w)=w := by
  have hKr : K⊆regularLocus := fun z hz => gradient_nonzero (hK0 z hz)
  obtain ⟨χ,_hχ,_hχc,_hχU,_hr,_hχ1,hB,hBc,hBe⟩ := exists_smooth_compact_extension
    hK regularLocus_isOpen hKr normalLift_contDiffOn
  obtain ⟨O,hO,hKO,hOB⟩ := mem_nhdsSet_iff_exists.mp hBe
  refine ⟨fun z => χ z • normalLift z,hB,hBc,O∩regularLocus,
    hO.inter regularLocus_isOpen,fun z hz => ⟨hKO hz,hKr hz⟩,inter_subset_right,?_⟩
  intro z hz w
  change realJacobian z ((χ z • normalLift z) w)=w
  rw [hOB hz.1]
  exact normalLift_projects hz.2 w

theorem inclusion_real_contMDiff : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,PlaneBase) ∞ inclusion :=
  (projection_contDiff.restrict_scalars ℝ).contMDiff.comp
    (real_inclusion_contMDiff (parameters 0))

theorem exists_actual_cubic_normal_tube {K : Set BaseCurve} {H : Set ℂ}
    (hK : IsCompact K) (hH : IsCompact H) :
    ∃ Ψ : ℝ × (BaseCurve × ℂ) → PlaneBase, ∃ ε : ℝ, 0<ε ∧
      ∃ U : Set (BaseCurve × ℂ),IsOpen U ∧ K×ˢH⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,ℂ)))
        𝓘(ℝ,PlaneBase) ∞ Ψ ∧
      (∀ p,Ψ (0,p)=inclusion p.1) ∧
      (∀ p∈U,∀ t∈Icc (-ε) ε,polynomial (Ψ (t,p))=t•p.2) ∧
      ∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Ψ (t,p.val)) := by
  obtain ⟨B,hB,_hBc,O,hO,hKO,_hOr,hproj⟩ := exists_compact_normal_lift
    (hK.image inclusion_isEmbedding.continuous)
    (by rintro _ ⟨z,_hz,rfl⟩; exact inclusion_polynomial z)
  have hdf z : fderiv ℝ polynomial z=realJacobian z :=
    ((polynomial_hasFDerivAt z).restrictScalars ℝ).fderiv
  obtain ⟨Φ,ε,hε,W,hW,hKW,_hWO,hΦ,hΦ0,hΦa,hparam,he,_hst,_hd⟩ :=
    exists_compact_normal_flow (polynomial_contDiff.restrict_scalars ℝ)
      hB hO (by simpa only [hdf] using hproj)
      (hK.image inclusion_isEmbedding.continuous) hH hKO
  let ι : BaseCurve × ℂ → PlaneBase × ℂ := fun p => (inclusion p.1,p.2)
  have hι : ContMDiff ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,ℂ))
      𝓘(ℝ,PlaneBase × ℂ) ∞ ι := by
    exact (inclusion_real_contMDiff.comp contMDiff_fst).prodMk_space contMDiff_snd
  let Ψ : ℝ × (BaseCurve × ℂ) → PlaneBase := fun p => (Φ (p.1,ι p.2)).1
  have hΨ : ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,ℂ)))
      𝓘(ℝ,PlaneBase) ∞ Ψ := by
    exact contDiff_fst.contMDiff.comp (hΦ.contMDiff.comp
      (contMDiff_fst.prodMk_space (hι.comp contMDiff_snd)))
  refine ⟨Ψ,ε,hε,ι ⁻¹' W,hW.preimage hι.continuous,?_,hΨ,?_,?_,?_⟩
  · intro p hp
    exact hKW ⟨⟨p.1,hp.1,rfl⟩,hp.2⟩
  · intro p
    exact congrArg Prod.fst (hΦ0 (ι p))
  · intro p hp t ht
    change polynomial (Φ (t,ι p)).1=t•p.2
    rw [he _ hp _ ht,inclusion_polynomial,zero_add]
  · intro t ht ht0
    let S := ι ⁻¹' W
    let I : S → PlaneBase × ℂ := fun p => ι p.val
    have hI : Topology.IsEmbedding I :=
      (inclusion_isEmbedding.prodMap Topology.IsEmbedding.id).comp
        Topology.IsEmbedding.subtypeVal
    have hs : Continuous (fun p : S => Ψ (t,p.val)) :=
      (hΦ.continuous.comp (continuous_const.prodMk hI.continuous)).fst
    let R : PlaneBase → PlaneBase × ℂ := fun z => ((Φ (-t,(z,t⁻¹•polynomial z))).1,t⁻¹•polynomial z)
    have hc : Continuous (fun z => t⁻¹•polynomial z) :=
      (continuous_const : Continuous (fun _ : PlaneBase => (t⁻¹ : ℝ))).smul
        polynomial_contDiff.continuous
    have hR : Continuous R :=
      (hΦ.continuous.comp (continuous_const.prodMk (continuous_id.prodMk hc))).fst.prodMk hc
    have hRi : R ∘ (fun p : S => Ψ (t,p.val))=I := by
      funext p
      have hn : t⁻¹•polynomial (Φ (t,I p)).1=p.val.2 := by
        rw [he _ p.property _ ht,inclusion_polynomial,zero_add,smul_smul,
          inv_mul_cancel₀ ht0,one_smul]
      have hg : Φ (-t,Φ (t,I p))=I p := by rw [← hΦa,neg_add_cancel,hΦ0]
      have hpar := hparam (I p) p.property t ht
      have hin : ((Φ (t,I p)).1,t⁻¹•polynomial (Φ (t,I p)).1)=Φ (t,I p) := by
        rw [hn,← hpar]
      change ((Φ (-t,((Φ (t,I p)).1,t⁻¹•polynomial (Φ (t,I p)).1))).1,
        t⁻¹•polynomial (Φ (t,I p)).1)=I p
      rw [hin,hg,hn]
    exact Topology.IsEmbedding.of_comp hs hR (hRi ▸ hI)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem primitivePullback_smoothAt {α : F → F →L[ℝ] ℝ} {g : E → F} {x : E}
    (hα : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (primitivePullback α g) x :=
  (hα.comp x hg).clm_comp (hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_CubicToricAmbient
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem ambientWeightedCoefficient_smooth (D m : ℕ) :
    ContDiff ℝ ∞ (ambientWeightedCoefficient D m) :=
  complexAffineLift_smooth.comp ((complexCartesian (ι := Option (Fin 3))).symm.contDiff.comp
    ((affinePhase 3).contDiff.comp ((weightedProjection_contDiff D m).restrict_scalars ℝ)))

 theorem ambientWeightedCoefficient_none (D m : ℕ) (x : PlaneBase) :
    ambientWeightedCoefficient D m x none=1 := rfl

 theorem conePolynomial_smooth {A B : ℕ} (D S : ℕ) :
    ContDiff ℝ ∞ (conePolynomial (A := A) (B := B) D S) := by
  apply contDiff_pi.mpr
  intro ij
  change ContDiff ℝ ∞ (fun p : CubicConeTarget => p.2.1^(latticeIndex ij.1).1 *
    p.2.2^(latticeIndex ij.1).2 * ambientWeightedCoefficient (cubicDegree D ij.1) (cubicMarkedOrder S ij.1) p.1 ij.2)
  have hc : ContDiff ℝ ∞ (fun p : CubicConeTarget =>
      ambientWeightedCoefficient (cubicDegree D ij.1) (cubicMarkedOrder S ij.1) p.1 ij.2) :=
    (contDiff_apply ℝ ℂ ij.2).comp
    ((ambientWeightedCoefficient_smooth (cubicDegree D ij.1) (cubicMarkedOrder S ij.1)).comp contDiff_fst)
  exact (((contDiff_snd.fst).pow _).mul ((contDiff_snd.snd).pow _)).mul hc

 theorem conePolynomial_nonzero {A B : ℕ} (D S : ℕ) (p : CubicConeTarget) :
    complexCartesian (conePolynomial (A := A) (B := B) D S p)≠0 := by
  obtain ⟨i,hi⟩ := lattice_zero A B
  intro h
  have he := congrFun (complexCartesian.injective (h.trans (map_zero _).symm)) (i,none)
  have hh : conePolynomial (A := A) (B := B) D S p (i,none)=1 := by
    change p.2.1^(latticeIndex i).1*p.2.2^(latticeIndex i).2*
      ambientWeightedCoefficient (cubicDegree D i) (cubicMarkedOrder S i) p.1 none=1
    rw [hi,ambientWeightedCoefficient_none]
    simp
  rw [hh] at he
  exact one_ne_zero he

 theorem cubicConePrimitive_smooth {A B : ℕ} (D S : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (cubicConePrimitive (A := A) (B := B) D S c) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact primitivePullback_smoothAt (hopfPrimitive_smoothAt c (conePolynomial_nonzero D S p))
    (((complexCartesian (ι := TrapezoidWeight A B × WeightedHomogeneousIndex)).contDiff.comp
      (conePolynomial_smooth D S)).contDiffAt)

 theorem cubicNormalCoordinates_smooth (t : ℝ) : ContDiff ℝ ∞ (cubicNormalCoordinates t) :=
  contDiff_fst.prodMk (contDiff_snd.prodMk (((polynomial_contDiff.restrict_scalars ℝ).comp contDiff_fst).const_smul _))

 theorem exists_actual_cubic_exact_family_with_zero_bp240_oai {A B : ℕ} (D S : ℕ) (c : ℝ)
    {K : Set BaseCurve} {H : Set DiskPair} (hK : IsCompact K) (hH : IsCompact H) :
    ∃ Φ : ℝ × CubicConeSpace → CubicAmbient,
      ∃ Γ : ℝ → ManifoldOneForm CubicConeModel CubicConeSpace,
      ∃ ε : ℝ,0<ε ∧ ∃ U : Set CubicConeSpace,IsOpen U ∧ K×ˢH⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicConeModel)) 𝓘(ℝ,CubicAmbient) ∞ Φ ∧
      (∀ p,Φ (0,p)=(inclusion p.1,p.2.1)) ∧
      SmoothOneFormFamily Γ ∧ Γ 0=centralCubicPrimitive (A := A) (B := B) D S c ∧
      (∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Φ (t,p.val))) ∧
      ∀ t∈Icc (-ε) ε,t≠0 → ∀ p∈U,
        manifoldExteriorOneForm (Γ t) p=
          (cubicAmbientForm (A := A) (B := B) D S c t (Φ (t,p))).bilinearComp
            (manifoldMapDifferential (E := CubicAmbient) (F := CubicConeModel) (fun q => Φ (t,q)) p)
            (manifoldMapDifferential (E := CubicAmbient) (F := CubicConeModel) (fun q => Φ (t,q)) p) := by
  obtain ⟨Ψ,ε,hε,O,hO,hKO,hΨ,hΨ0,hEQ,hemb⟩ :=
    exists_actual_cubic_normal_tube hK (hH.image continuous_snd)
  have hxs : ContMDiff 𝓘(ℝ,CubicConeModel) ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,ℂ)) ∞
      (fun p : CubicConeSpace => (p.1,p.2.2)) :=
    (flatProduct_fst_smooth (V := DiskPair)).prodMk
      (contDiff_snd.contMDiff.comp (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve)))
  have hν : ContMDiff 𝓘(ℝ,CubicConeModel) 𝓘(ℝ,ℂ) ∞ (fun p : CubicConeSpace => p.2.1) :=
    contDiff_fst.contMDiff.comp (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve))
  let Φ : ℝ × CubicConeSpace → CubicAmbient := fun p => (Ψ (p.1,(p.2.1,p.2.2.2)),p.2.2.1)
  have hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicConeModel)) 𝓘(ℝ,CubicAmbient) ∞ Φ :=
    (hΨ.comp (contMDiff_fst.prodMk (hxs.comp contMDiff_snd))).prodMk_space (hν.comp contMDiff_snd)
  let g : ℝ × CubicConeSpace → CubicConeTarget := fun p => ((Φ p).1,p.2.2)
  have hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicConeModel)) 𝓘(ℝ,CubicConeTarget) ∞ g :=
    (contDiff_fst.contMDiff.comp hΦ).prodMk_space
      ((flatProduct_snd_smooth (E := RealModel) (M := BaseCurve) (V := DiskPair)).comp contMDiff_snd)
  let Γ := movingPrimitivePullback (E := CubicConeModel) (cubicConePrimitive (A := A) (B := B) D S c) g
  let U : Set CubicConeSpace := (fun p : CubicConeSpace => (p.1,p.2.2)) ⁻¹' O
  have hU : IsOpen U := hO.preimage hxs.continuous
  refine ⟨Φ,Γ,ε,hε,U,hU,?_,hΦ,?_,movingPrimitivePullback_smooth (cubicConePrimitive_smooth D S c) hg,?_,?_,?_⟩
  · intro p hp
    exact hKO ⟨hp.1,mem_image_of_mem _ hp.2⟩
  · intro p
    change (Ψ (0,(p.1,p.2.2)),p.2.1)=(inclusion p.1,p.2.1)
    rw [hΨ0]
  · have he : (fun p : CubicConeSpace => g (0,p))=centralCubicCoordinates := by
      funext p
      change (Ψ (0,(p.1,p.2.2)),p.2)=(inclusion p.1,p.2)
      rw [hΨ0]
    change manifoldPullbackOneForm (fun _ => cubicConePrimitive (A := A) (B := B) D S c)
      (fun p => g (0,p)) 0=centralCubicPrimitive (A := A) (B := B) D S c
    rw [he]
    rfl
  · intro t ht ht0
    let J : U → O × ℂ := fun p => (⟨(p.val.1,p.val.2.2),p.property⟩,p.val.2.1)
    have hJ : Topology.IsEmbedding J := by
      let e : CubicConeSpace ≃ₜ (BaseCurve × ℂ) × ℂ :=
        { toFun := fun p => ((p.1,p.2.2),p.2.1)
          invFun := fun p => (p.1.1,(p.2,p.1.2))
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          continuous_toFun := (continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst
          continuous_invFun := continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd) }
      have hc : Continuous J :=
        ((continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.snd).subtype_mk
          (fun p => p.property)).prodMk continuous_subtype_val.snd.fst
      exact Topology.IsEmbedding.of_comp hc (continuous_subtype_val.prodMap continuous_id)
        (e.isEmbedding.comp Topology.IsEmbedding.subtypeVal)
    exact ((hemb t ht ht0).prodMap Topology.IsEmbedding.id).comp hJ
  · intro t ht ht0 p hp
    have he : (fun q => g (t,q))=ᶠ[𝓝 p] cubicNormalCoordinates t ∘ (fun q => Φ (t,q)) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      change (Ψ (t,(q.1,q.2.2)),q.2)=
        (Ψ (t,(q.1,q.2.2)),(q.2.1,t⁻¹ • polynomial (Ψ (t,(q.1,q.2.2)))))
      rw [hEQ _ hq t ht,smul_smul,inv_mul_cancel₀ ht0,one_smul]
    exact movingPrimitivePullback_exterior_comp (cubicConePrimitive_smooth D S c) hg
      (cubicNormalCoordinates_smooth t) (hΦ.comp (contMDiff_const.prodMk contMDiff_id)) he

end PackingSufficiencySupport.CubicModel

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_exact_family_with_zero_bp240_oai := @OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_exact_family_with_zero_bp240_oai
