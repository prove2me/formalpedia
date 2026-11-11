-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_exact_family_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:51.804589+00:00
-- url     : https://prove2.me/submissions/1965e022-4400-4cf2-ae1c-0658d1e855ba

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

@[simp] theorem phaseArea_J_right (z v : PlanePhase ι) :
    phaseArea z (phaseJ v) = phaseDot z v := by
  simp only [phaseDot_apply,phaseArea_apply,phaseJ_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

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

theorem complexPairing_im (z v : ι → ℂ) :
    (complexPairing z v).im=phaseArea (complexCartesian z) (complexCartesian v) := by
  simp only [complexPairing,Complex.im_sum,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,phaseArea_apply,complexCartesian_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem complexPairing_self (z : ι → ℂ) :
    complexPairing z z=(∑ i,Complex.normSq (z i) : ℝ) := by
  simp only [complexPairing,Complex.ofReal_sum,Complex.star_def,← Complex.normSq_eq_conj_mul_self]

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

theorem veronese_hasFDerivAt (z : ι → ℂ) :
    HasFDerivAt veronese (veroneseDerivative z) z := by
  apply hasFDerivAt_pi.mpr
  rintro (⟨b,i⟩|⟨i,j⟩)
  · exact (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt
  · convert! ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt.mul
      (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt) using 1
    all_goals try with_reducible_and_instances rfl

theorem veronese_pairing (z v : ι → ℂ) :
    complexPairing (veronese z) (veroneseDerivative z v)=
      2*(1+complexPairing z z)*complexPairing z v := by
  classical
  simp only [complexPairing,Fintype.sum_sum_type,Fintype.sum_prod_type,veronese,
    veroneseDerivative,ContinuousLinearMap.pi_apply,add_apply,
    smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,
    Fintype.sum_bool,star_mul]
  have hterm (i j : ι) : star (z j)*star (z i)*(z i*v j+z j*v i)=
      (star (z i)*z i)*(star (z j)*v j)+(star (z i)*v i)*(star (z j)*z j) := by ring
  simp_rw [hterm,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
  ring

theorem veronese_sq (z : ι → ℂ) :
    1+phaseSq (complexCartesian (veronese z))=(1+phaseSq (complexCartesian z))^2 := by
  rw [complexCartesian_sq,complexCartesian_sq]
  simp only [veronese,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,
    Complex.normSq_mul,← Finset.mul_sum,← Finset.sum_mul]
  ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

theorem complexCartesian_affineComplex (z : Affine m) :
    complexCartesian (affineComplex m z)=affinePhase m z := by
  ext i <;> cases i <;> rfl

end PackingSufficiencySupport.DiagonalQuadrics

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

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in

theorem tubeSlice_isEmbedding {f : E → F} (hf : Continuous f)
    {Φ : ℝ × (E×F) → E×F} (hΦ : Continuous Φ)
    (hΦ0 : ∀ p,Φ (0,p)=p) (hΦa : ∀ s t p,Φ (s+t,p)=Φ (s,Φ (t,p)))
    {W : Set (E×F)} {t : ℝ} (ht : t≠0)
    (hp : ∀ p∈W,(Φ (t,p)).2=p.2)
    (he : ∀ p∈W,f (Φ (t,p)).1=f p.1+t•p.2) :
    Topology.IsEmbedding (tubeSlice Φ t f W) := by
  let ι : tubeDomain f W → E×F := fun p => ((p.val.1 : E),p.val.2)
  have hι : Topology.IsEmbedding ι :=
    (Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id).comp
      Topology.IsEmbedding.subtypeVal
  have hs : Continuous (tubeSlice Φ t f W) :=
    (hΦ.comp (continuous_const.prodMk hι.continuous)).fst
  let R : E → E×F := fun z => ((Φ (-t,(z,t⁻¹•f z))).1,t⁻¹•f z)
  have hR : Continuous R :=
    (hΦ.comp (continuous_const.prodMk (continuous_id.prodMk
      (continuous_const.smul hf)))).fst.prodMk (continuous_const.smul hf)
  have hRi : R ∘ tubeSlice Φ t f W=ι := by
    funext p
    have hn : t⁻¹ • f (Φ (t,ι p)).1=p.val.2 := by
      rw [he _ p.property,p.val.1.property,zero_add,smul_smul,inv_mul_cancel₀ ht,one_smul]
    have hg : Φ (-t,Φ (t,ι p))=ι p := by rw [← hΦa,neg_add_cancel,hΦ0]
    have hparam := hp (ι p) p.property
    have hinput : ((Φ (t,ι p)).1,t⁻¹•f (Φ (t,ι p)).1)=Φ (t,ι p) := by
      rw [hn,← hparam]
    change ((Φ (-t,((Φ (t,ι p)).1,t⁻¹•f (Φ (t,ι p)).1))).1,
      t⁻¹•f (Φ (t,ι p)).1)=ι p
    rw [hinput,hg,hn]
  exact Topology.IsEmbedding.of_comp hs hR (hRi ▸ hι)

end PackingSufficiencySupport.NormalLift

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_TailLineCoordinates
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function
open NormalLift Hamiltonian
open scoped Manifold
open Manifold
section

variable {m : ℕ}

theorem regularLocus_isOpen (m : ℕ) : IsOpen (regularLocus m) :=
  isOpen_iUnion regularCoordinate_isOpen

theorem locus_subset_regularLocus {a : Fin m → ℂ} (ha : Injective a) (ha0 : ∀ j,a j≠0) :
    locus a⊆regularLocus m := by
  intro z hz
  obtain ⟨c,hc⟩ := exists_regularCoordinate ha ha0 hz
  exact mem_iUnion.mpr ⟨c,hc⟩

theorem regular_jacobian_surjective {z : Affine m} (hz : z∈regularLocus m) :
    Surjective (jacobian z) := by
  obtain ⟨c,hc⟩ := mem_iUnion.mp hz
  intro w
  obtain ⟨v,hv⟩ := (regularCoordinate_bijective c hc).2 (0,w)
  exact ⟨v,congrArg Prod.snd hv⟩

theorem equations_real_hasFDerivAt (a : Fin m → ℂ) (z : Affine m) :
    HasFDerivAt (equations a) (realJacobian z) z :=
  (equations_hasFDerivAt a z).restrictScalars ℝ

theorem realJacobian_contDiff :
    ContDiff ℝ ∞ (realJacobian : Affine m → Affine m →L[ℝ] (Fin m → ℂ)) := by
  have he : realJacobian (m := m)=fderiv ℝ (equations (0 : Fin m → ℂ)) :=
    funext fun z => (equations_real_hasFDerivAt 0 z).fderiv.symm
  rw [he]
  exact ((equations_contDiff 0).restrict_scalars ℝ).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

theorem normalLift_projects {z : Affine m} (hz : z∈regularLocus m) (w : Fin m → ℂ) :
    realJacobian z (normalLift z w)=w :=
  finiteRightLift_right_inverse (regular_jacobian_surjective hz) w

theorem normalLift_contDiffOn :
    ContDiffOn ℝ ∞ (normalLift : Affine m → (Fin m → ℂ) →L[ℝ] Affine m) (regularLocus m) := by
  intro z hz
  exact ((finiteRightLift_contDiffAt (regular_jacobian_surjective hz)).comp z
    realJacobian_contDiff.contDiffAt).contDiffWithinAt

theorem exists_compact_normal_lift {a : Fin m → ℂ} (ha : Injective a) (ha0 : ∀ j,a j≠0)
    {K : Set (Affine m)} (hK : IsCompact K) (hKa : K⊆locus a) :
    ∃ B : Affine m → (Fin m → ℂ) →L[ℝ] Affine m,
      ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧ ∃ O : Set (Affine m),
      IsOpen O ∧ K⊆O ∧ O⊆regularLocus m ∧
      ∀ z∈O,∀ w,realJacobian z (B z w)=w := by
  obtain ⟨χ,_hχ,_hχc,_hχU,_hr,hχ1,hB,hBc,hBe⟩ := exists_smooth_compact_extension
    hK (regularLocus_isOpen m) (hKa.trans (locus_subset_regularLocus ha ha0)) normalLift_contDiffOn
  obtain ⟨O,hO,hKO,hOB⟩ := mem_nhdsSet_iff_exists.mp hBe
  refine ⟨fun z => χ z • normalLift z,hB,hBc,O∩regularLocus m,
    hO.inter (regularLocus_isOpen m),fun z hz => ⟨hKO hz,locus_subset_regularLocus ha ha0 (hKa hz)⟩,
    inter_subset_right,?_⟩
  intro z hz w
  change realJacobian z ((χ z • normalLift z) w)=w
  rw [hOB hz.1]
  exact normalLift_projects hz.2 w

end

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem exists_actual_normal_tube {K : Set (locus a)} {H : Set (Fin m → ℂ)}
    (hK : IsCompact K) (hH : IsCompact H) :
    ∃ Ψ : ℝ × (locus a × (Fin m → ℂ)) → Affine m, ∃ ε : ℝ, 0<ε ∧
      ∃ U : Set (locus a × (Fin m → ℂ)), IsOpen U ∧ K×ˢH⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,Fin m → ℂ)))
        𝓘(ℝ,Affine m) ∞ Ψ ∧
      (∀ p,Ψ (0,p)=p.1.val) ∧
      (∀ p∈U,∀ t∈Icc (-ε) ε,equations a (Ψ (t,p))=t•p.2) ∧
      ∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Ψ (t,p.val)) := by
  obtain ⟨B,hB,_hBc,O,hO,hKO,_hOr,hproj⟩ := exists_compact_normal_lift
    (Fact.out : Injective a) (Fact.out : ∀ j,a j≠0)
    (hK.image continuous_subtype_val) (by rintro _ ⟨z,_hz,rfl⟩; exact z.property)
  have hdf z : fderiv ℝ (equations a) z=realJacobian z :=
    (equations_real_hasFDerivAt a z).fderiv
  obtain ⟨Φ,ε,hε,W,hW,hKW,_hWO,hΦ,hΦ0,hΦa,hparam,he,_hst,_hd⟩ :=
    exists_compact_normal_flow ((equations_contDiff a).restrict_scalars ℝ)
      hB hO (by simpa only [hdf] using hproj)
      (hK.image continuous_subtype_val) hH hKO
  let ι : locus a × (Fin m → ℂ) → Affine m × (Fin m → ℂ) := fun p => (p.1.val,p.2)
  have hι : ContMDiff ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,Fin m → ℂ))
      𝓘(ℝ,Affine m × (Fin m → ℂ)) ∞ ι := by
    apply ContMDiff.prodMk_space
    · exact (real_inclusion_contMDiff a).comp contMDiff_fst
    · exact contMDiff_snd
  let Ψ : ℝ × (locus a × (Fin m → ℂ)) → Affine m := fun p => (Φ (p.1,ι p.2)).1
  have hΨ : ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,Fin m → ℂ)))
      𝓘(ℝ,Affine m) ∞ Ψ := by
    have hi : ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,Fin m → ℂ)))
        𝓘(ℝ,ℝ × (Affine m × (Fin m → ℂ))) ∞
        (fun p : ℝ × (locus a × (Fin m → ℂ)) => (p.1,ι p.2)) :=
      contMDiff_fst.prodMk_space (hι.comp contMDiff_snd)
    have hc := hΦ.contMDiff.comp hi
    exact (contDiff_fst.contMDiff).comp hc
  refine ⟨Ψ,ε,hε,ι ⁻¹' W,hW.preimage hι.continuous,?_,hΨ,?_,?_,?_⟩
  · intro p hp
    exact hKW ⟨⟨p.1,hp.1,rfl⟩,hp.2⟩
  · intro p
    exact congrArg Prod.fst (hΦ0 (ι p))
  · intro p hp t ht
    change equations a (Φ (t,ι p)).1=t•p.2
    rw [he _ hp _ ht]
    have hz : equations a p.1.val=0 := p.1.property
    rw [hz,zero_add]
  · intro t ht ht0
    exact tubeSlice_isEmbedding (equations_contDiff a).continuous
      hΦ.continuous hΦ0 hΦa ht0 (fun p hp => hparam p hp t ht)
      (fun p hp => he p hp t ht)

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open scoped BigOperators
section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem coneDenominator_pos (p : PlanePhase ι × PlanePhase κ) : 0 < coneDenominator p :=
  add_pos_of_pos_of_nonneg (sq_pos_of_pos (fs_den_pos p.1)) (phaseSq_nonneg p.2)

theorem conePrimitive_apply (c d : ℝ) (p v : PlanePhase ι × PlanePhase κ) :
    conePrimitive c d p v=(1-2*d)*affineFSPrimitive c p.1 v.1+
      c*d/(2*coneDenominator p)*(2*(1+phaseSq p.1)*phaseArea p.1 v.1+phaseArea p.2 v.2) := rfl

theorem conePrimitive_smooth (c d : ℝ) :
    ContDiff ℝ ∞ (conePrimitive (ι := ι) (κ := κ) c d) := by
  have hden : ContDiff ℝ ∞ (coneDenominator : PlanePhase ι × PlanePhase κ → ℝ) :=
    ((contDiff_const.add (phaseSq_smooth.comp contDiff_fst)).pow 2).add
      (phaseSq_smooth.comp contDiff_snd)
  have hcoef : ContDiff ℝ ∞ (fun p : PlanePhase ι × PlanePhase κ => c*d/(2*coneDenominator p)) :=
    contDiff_const.div (contDiff_const.mul hden)
      (fun p => mul_ne_zero (by norm_num) (coneDenominator_pos p).ne')
  have hbase : ContDiff ℝ ∞ (fun p : PlanePhase ι × PlanePhase κ =>
      ((1-2*d) • affineFSPrimitive c p.1).comp (ContinuousLinearMap.fst ℝ (PlanePhase ι) (PlanePhase κ))) :=
    (((affineFSPrimitive_smooth (ι := ι) c).comp contDiff_fst).const_smul (1-2*d)).clm_comp contDiff_const
  have hb : ContDiff ℝ ∞ (fun p : PlanePhase ι × PlanePhase κ =>
      (phaseArea p.1).comp (ContinuousLinearMap.fst ℝ (PlanePhase ι) (PlanePhase κ))) :=
    ((phaseArea (ι := ι)).contDiff.comp contDiff_fst).clm_comp contDiff_const
  have hv : ContDiff ℝ ∞ (fun p : PlanePhase ι × PlanePhase κ =>
      (phaseArea p.2).comp (ContinuousLinearMap.snd ℝ (PlanePhase ι) (PlanePhase κ))) :=
    ((phaseArea (ι := κ)).contDiff.comp contDiff_snd).clm_comp contDiff_const
  exact hbase.add (hcoef.smul
    (((contDiff_const.mul (contDiff_const.add (phaseSq_smooth.comp contDiff_fst))).smul hb).add hv))

end

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 theorem joinedVeronese_smooth : ContDiff ℂ ∞ (joinedVeronese (ι := ι) (κ := κ)) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact (contDiff_apply ℂ ℂ i).comp (veronese_contDiff.comp contDiff_fst)
  | inr i => exact (contDiff_apply ℂ ℂ i).comp contDiff_snd

 theorem joinedVeronese_hasFDerivAt (p : (ι → ℂ) × (κ → ℂ)) :
    HasFDerivAt joinedVeronese (joinedVeroneseDerivative p) p := by
  apply hasFDerivAt_pi.mpr
  intro i
  cases i with
  | inl i =>
      exact (ContinuousLinearMap.proj i : (VeroneseIndex ι → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp p
        ((veronese_hasFDerivAt p.1).comp p (hasFDerivAt_fst (p := p)))
  | inr i =>
      exact (ContinuousLinearMap.proj i : (κ → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp p (hasFDerivAt_snd (p := p))

 theorem joinedVeronese_sq (p : (ι → ℂ) × (κ → ℂ)) :
    1+phaseSq (complexCartesian (joinedVeronese p))=
      (1+phaseSq (complexCartesian p.1))^2+phaseSq (complexCartesian p.2) := by
  rw [complexCartesian_sq,Fintype.sum_sum_type]
  change 1+((∑ j,Complex.normSq (veronese p.1 j))+(∑ j,Complex.normSq (p.2 j)))=_
  rw [← complexCartesian_sq,← complexCartesian_sq,← add_assoc,veronese_sq]

 theorem joinedVeronese_pairing (p v : (ι → ℂ) × (κ → ℂ)) :
    complexPairing (joinedVeronese p) (joinedVeroneseDerivative p v)=
      2*(1+complexPairing p.1 p.1)*complexPairing p.1 v.1+complexPairing p.2 v.2 := by
  change (∑ i,star (joinedVeronese p i)*(joinedVeroneseDerivative p v i))=_
  rw [Fintype.sum_sum_type]
  change complexPairing (veronese p.1) (veroneseDerivative p.1 v.1)+complexPairing p.2 v.2=_
  rw [veronese_pairing]

 theorem joinedVeronese_area (p v : (ι → ℂ) × (κ → ℂ)) :
    phaseArea (complexCartesian (joinedVeronese p))
      (complexCartesian (joinedVeroneseDerivative p v))=
      2*(1+phaseSq (complexCartesian p.1))*phaseArea (complexCartesian p.1) (complexCartesian v.1)+
        phaseArea (complexCartesian p.2) (complexCartesian v.2) := by
  rw [← complexPairing_im,joinedVeronese_pairing,complexPairing_self,complexCartesian_sq]
  simp [Complex.mul_im,complexPairing_im]

 theorem joinedVeronese_real_derivative (p : (ι → ℂ) × (κ → ℂ))
    (v : (ι → ℂ) × (κ → ℂ)) :
    fderiv ℝ (fun q => complexCartesian (joinedVeronese q)) p v=
      complexCartesian (joinedVeroneseDerivative p v) := by
  have hd := complexCartesian.toContinuousLinearMap.hasFDerivAt.comp p
    ((joinedVeronese_hasFDerivAt p).restrictScalars ℝ)
  change HasFDerivAt (fun q => complexCartesian (joinedVeronese q)) _ p at hd
  rw [hd.fderiv]
  rfl

 theorem joinedVeronese_primitive (c d : ℝ) (p v : (ι → ℂ) × (κ → ℂ)) :
    (1-2*d)*affineFSPrimitive c (complexCartesian p.1) (complexCartesian v.1)+
      d*primitivePullback (affineFSPrimitive c) (fun q => complexCartesian (joinedVeronese q)) p v=
      conePrimitive c d (complexCartesian p.1,complexCartesian p.2)
        (complexCartesian v.1,complexCartesian v.2) := by
  rw [primitivePullback,ContinuousLinearMap.comp_apply,joinedVeronese_real_derivative,
    conePrimitive_apply]
  simp only [affineFSPrimitive,smul_apply,smul_eq_mul,joinedVeronese_area]
  rw [joinedVeronese_sq]
  unfold coneDenominator
  ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

 theorem normalGraph_smooth (a : Fin m → ℂ) (t : ℝ) : ContDiff ℂ ∞ (normalGraph a t) :=
  (affineComplex m).contDiff.prodMk (contDiff_pi.mpr fun j =>
    contDiff_const.mul ((contDiff_apply ℂ ℂ j).comp (equations_contDiff a)))

 theorem normalPolynomial_eq_joined (a : Fin m → ℂ) (t : ℝ) (z : Affine m) :
    normalPolynomial a t z=joinedVeronese (normalGraph a t z) := by
  funext i
  cases i <;> rfl

 theorem normalConeCoordinates_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℝ ∞ (normalConeCoordinates a t) :=
  (affinePhase m).contDiff.prodMk
    ((complexCartesian (ι := Fin m)).contDiff.comp (((normalGraph_smooth a t).restrict_scalars ℝ).snd))

 theorem normalGraph_derivative_fst (a : Fin m → ℂ) (t : ℝ) (z v : Affine m) :
    (fderiv ℝ (normalGraph a t) z v).1=affineComplex m v := by
  have hd := (((normalGraph_smooth a t).restrict_scalars ℝ).differentiable (by simp) z).hasFDerivAt.fst.fderiv
  change fderiv ℝ (affineComplex m) z=_ at hd
  have he : fderiv ℝ (affineComplex m) z=(affineComplex m).restrictScalars ℝ :=
    (((affineComplex m).hasFDerivAt (x := z)).restrictScalars ℝ).fderiv
  rw [he] at hd
  exact congrArg (fun L => L v) hd.symm

 theorem normalConeCoordinates_derivative (a : Fin m → ℂ) (t : ℝ) (z v : Affine m) :
    fderiv ℝ (normalConeCoordinates a t) z v=
      (complexCartesian (fderiv ℝ (normalGraph a t) z v).1,
        complexCartesian (fderiv ℝ (normalGraph a t) z v).2) := by
  have hd := (((normalGraph_smooth a t).restrict_scalars ℝ).differentiable (by simp) z).hasFDerivAt
  have h₁ := (complexCartesian (ι := Option (Fin m))).toContinuousLinearMap.hasFDerivAt.comp z hd.fst
  have h₂ := (complexCartesian (ι := Fin m)).toContinuousLinearMap.hasFDerivAt.comp z hd.snd
  have hh := h₁.prodMk h₂
  have he : (fun x => (complexCartesian (normalGraph a t x).1,complexCartesian (normalGraph a t x).2))=
      normalConeCoordinates a t := by
    funext x; exact Prod.ext (complexCartesian_affineComplex x) rfl
  change HasFDerivAt (fun x => (complexCartesian (normalGraph a t x).1,
    complexCartesian (normalGraph a t x).2)) _ z at hh
  rw [he] at hh
  rw [hh.fderiv]
  rfl

 theorem normalPolynomial_derivative_joined (a : Fin m → ℂ) (t : ℝ) (z v : Affine m) :
    fderiv ℝ (fun x => complexCartesian (normalPolynomial a t x)) z v=
      fderiv ℝ (fun p => complexCartesian (joinedVeronese p)) (normalGraph a t z)
        (fderiv ℝ (normalGraph a t) z v) := by
  have hgC : ContDiff ℂ ∞ (joinedVeronese (ι := Option (Fin m)) (κ := Fin m)) :=
    joinedVeronese_smooth
  have hg : ContDiff ℝ ∞ (fun p : (Option (Fin m) → ℂ) × (Fin m → ℂ) =>
      complexCartesian (joinedVeronese p)) :=
    (complexCartesian (ι := NormalPolynomialIndex m)).contDiff.comp
      (hgC.restrict_scalars ℝ)
  have hd := (hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (normalGraph a t z)).hasFDerivAt.comp z
    (((normalGraph_smooth a t).restrict_scalars ℝ).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt
  have he : (fun x => complexCartesian (normalPolynomial a t x))=
      (fun p => complexCartesian (joinedVeronese p)) ∘ normalGraph a t := by
    funext x; rw [normalPolynomial_eq_joined]; rfl
  rw [he,hd.fderiv]
  rfl

 theorem normalAmbientPrimitive_eq_cone (a : Fin m → ℂ) (c d t : ℝ) :
    normalAmbientPrimitive a c d t=primitivePullback (conePrimitive c d) (normalConeCoordinates a t) := by
  funext z
  apply ContinuousLinearMap.ext
  intro v
  have hh := joinedVeronese_primitive c d (normalGraph a t z) (fderiv ℝ (normalGraph a t) z v)
  rw [normalGraph_derivative_fst,complexCartesian_affineComplex] at hh
  simp only [normalGraph,complexCartesian_affineComplex] at hh
  change (1-2*d)*affineFSPrimitive c (affinePhase m z) (affinePhase m v)+
    d*affineFSPrimitive c (complexCartesian (joinedVeronese (normalGraph a t z)))
      (fderiv ℝ (fun p => complexCartesian (joinedVeronese p)) (normalGraph a t z)
        (fderiv ℝ (normalGraph a t) z v))=_ at hh
  change (1-2*d)*affineFSPrimitive c (affinePhase m z) (affinePhase m v)+
    d*affineFSPrimitive c (complexCartesian (normalPolynomial a t z))
      (fderiv ℝ (fun x => complexCartesian (normalPolynomial a t x)) z v)=
    conePrimitive c d (normalConeCoordinates a t z)
      (fderiv ℝ (normalConeCoordinates a t) z v)
  rw [normalPolynomial_derivative_joined,normalConeCoordinates_derivative,normalPolynomial_eq_joined,
    normalGraph_derivative_fst,complexCartesian_affineComplex]
  exact hh

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_QuadricMovingCone
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

 theorem movingConeCoordinates_smooth {Ψ : ℝ × ConeSpace a → Affine m}
    (hΨ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ConeModel m)) 𝓘(ℝ,Affine m) ∞ Ψ) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ConeModel m)) 𝓘(ℝ,ConeTarget m) ∞
      (movingConeCoordinates a Ψ) := by
  apply ContMDiff.prodMk_space
  · exact (affinePhase m).contDiff.contMDiff.comp hΨ
  · have hs : ContMDiff 𝓘(ℝ,ConeModel m) 𝓘(ℝ,Fin m → ℂ) ∞
        (Prod.snd : ConeSpace a → Fin m → ℂ) := by
      simpa only [modelWithCornersSelf_prod] using
        (contMDiff_snd : ContMDiff ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,Fin m → ℂ))
          𝓘(ℝ,Fin m → ℂ) ∞ (Prod.snd : ConeSpace a → Fin m → ℂ))
    exact (complexCartesian (ι := Fin m)).contDiff.contMDiff.comp (hs.comp contMDiff_snd)

 omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
 theorem movingConeCoordinates_zero {Ψ : ℝ × ConeSpace a → Affine m}
    (hΨ : ∀ p,Ψ (0,p)=p.1.val) :
    (fun p => movingConeCoordinates a Ψ (0,p))=centralConeCoordinates a := by
  funext p
  simp only [movingConeCoordinates,centralConeCoordinates,hΨ]

 omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
 theorem movingConeCoordinates_nonzero {Ψ : ℝ × ConeSpace a → Affine m}
    {t : ℝ} (ht : t≠0) {p : ConeSpace a} (he : equations a (Ψ (t,p))=t•p.2) :
    movingConeCoordinates a Ψ (t,p)=normalConeCoordinates a t (Ψ (t,p)) := by
  apply Prod.ext
  · rfl
  apply congrArg (complexCartesian (ι := Fin m))
  change p.2=fun j => (t:ℂ)⁻¹*equations a (Ψ (t,p)) j
  funext j
  rw [he]
  simp only [Pi.smul_apply,Complex.real_smul]
  rw [← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht),one_mul]

 theorem exists_actual_normal_exact_family_bp240_oai {K : Set (locus a)} {H : Set (Fin m → ℂ)}
    (hK : IsCompact K) (hH : IsCompact H) (c d : ℝ) :
    ∃ Ψ : ℝ × ConeSpace a → Affine m, ∃ Γ : ℝ → ManifoldOneForm (ConeModel m) (ConeSpace a),
      ∃ ε : ℝ,0<ε ∧ ∃ U : Set (ConeSpace a),IsOpen U ∧ K×ˢH⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ConeModel m)) 𝓘(ℝ,Affine m) ∞ Ψ ∧
      SmoothOneFormFamily Γ ∧ Γ 0=centralConePrimitive a c d ∧
      (∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Ψ (t,p.val))) ∧
      (∀ t∈Icc (-ε) ε,t≠0 → ∀ p∈U,
        manifoldExteriorOneForm (Γ t) p=
          (normalAmbientForm a c d t (Ψ (t,p))).bilinearComp
            (manifoldMapDifferential (E := Affine m) (F := ConeModel m) (fun q => Ψ (t,q)) p)
            (manifoldMapDifferential (E := Affine m) (F := ConeModel m) (fun q => Ψ (t,q)) p)) := by
  obtain ⟨Ψ,ε,hε,U,hU,hKU,hΨ,hΨ0,hEQ,hemb⟩ := exists_actual_normal_tube a hK hH
  have hs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ConeModel m)) 𝓘(ℝ,Affine m) ∞ Ψ := by
    simpa only [modelWithCornersSelf_prod] using hΨ
  let g := movingConeCoordinates a Ψ
  have hg := movingConeCoordinates_smooth a hs
  let Γ := movingPrimitivePullback (E := ConeModel m) (conePrimitive c d) g
  refine ⟨Ψ,Γ,ε,hε,U,hU,hKU,hs,movingPrimitivePullback_smooth (conePrimitive_smooth c d) hg,?_,hemb,?_⟩
  · change manifoldPullbackOneForm (fun _ => conePrimitive c d)
      (fun p => movingConeCoordinates a Ψ (0,p)) 0=centralConePrimitive a c d
    rw [movingConeCoordinates_zero a hΨ0]
    rfl
  · intro t ht ht0 p hp
    have he : (fun q => g (t,q)) =ᶠ[𝓝 p] normalConeCoordinates a t ∘ (fun q => Ψ (t,q)) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact movingConeCoordinates_nonzero a ht0 (hEQ q hq t ht)
    have hh := movingPrimitivePullback_exterior_comp (conePrimitive_smooth c d) hg
      (normalConeCoordinates_smooth a t) (hs.comp (contMDiff_const.prodMk contMDiff_id)) he
    rw [← normalAmbientPrimitive_eq_cone a c d t] at hh
    exact hh

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_exact_family_bp240_oai := @OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_exact_family_bp240_oai
