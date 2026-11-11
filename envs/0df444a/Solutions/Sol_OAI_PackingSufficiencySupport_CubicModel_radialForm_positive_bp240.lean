-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.CubicModel.radialForm_positive_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:43.13898+00:00
-- url     : https://prove2.me/submissions/497abced-b827-4672-9435-c57887252058

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
-- module Solutions.OAIQ240_BP.BallPacking_Kahler_PhaseArea
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.curveChartedSpace _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.curveComplexManifold _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceManifold _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
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

theorem affineFSForm_apply (a : ℝ) (z v w : PlanePhase ι) :
    affineFSForm a z v w = a/(1+phaseSq z)*phaseArea v w - a/(1+phaseSq z)^2*
      (phaseDot z v*phaseArea z w-phaseArea z v*phaseDot z w) := by
  simp only [affineFSForm,sub_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul]

theorem affineFSPrimitive_smooth (a : ℝ) :
    ContDiff ℝ ∞ (affineFSPrimitive a : PlanePhase ι → _) := by
  have hc : ContDiff ℝ ∞ (fun z : PlanePhase ι => a/(2*(1+phaseSq z))) :=
    contDiff_const.div (contDiff_const.mul (contDiff_const.add phaseSq_smooth))
      (fun z => mul_ne_zero (by norm_num) (fs_den_pos z).ne')
  exact hc.smul (phaseArea (ι := ι)).contDiff

theorem affineFSPrimitive_fderiv (a : ℝ) (z v w : PlanePhase ι) :
    fderiv ℝ (affineFSPrimitive a) z v w =
      a/(2*(1+phaseSq z))*phaseArea v w -
        a/(1+phaseSq z)^2*phaseDot z v*phaseArea z w := by
  have hs : HasFDerivAt (fun y : PlanePhase ι => 1+phaseSq y)
      ((2:ℝ) • phaseDot z) z := (phaseSq_hasFDerivAt z).const_add 1
  have hc := ((hasDerivAt_inv (fs_den_pos z).ne').comp_hasFDerivAt z hs).const_mul (a/2)
  have hc' : HasFDerivAt (fun y : PlanePhase ι => a/(2*(1+phaseSq y)))
      ((-a/(1+phaseSq z)^2) • phaseDot z) z := by
    have he : (fun y : PlanePhase ι => a/(2*(1+phaseSq y))) =
        (fun y => a/2 * ((1+phaseSq y))⁻¹) := by funext y; field_simp [(fs_den_pos y).ne']
    rw [he]
    apply hc.congr_fderiv
    ext v
    simp only [smul_apply,smul_eq_mul,smul_smul]
    ring
  have hd := hc'.smul (phaseArea (ι := ι)).hasFDerivAt
  rw [show fderiv ℝ (affineFSPrimitive a) z = _ from hd.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

theorem affineFSPrimitive_exterior (a : ℝ) (z v w : PlanePhase ι) :
    fderiv ℝ (affineFSPrimitive a) z v w -
      fderiv ℝ (affineFSPrimitive a) z w v = affineFSForm a z v w := by
  rw [affineFSPrimitive_fderiv,affineFSPrimitive_fderiv,affineFSForm_apply,
    phaseArea_skew w v]
  field_simp [(fs_den_pos z).ne']
  ring

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

theorem phase_complex_cauchy (z v : PlanePhase ι) :
    (phaseDot z v)^2+(phaseArea z v)^2 ≤ phaseSq z*phaseSq v := by
  by_cases hz : z=0
  · subst z
    simp [phaseSq]
  have hq := phaseSq_pos hz
  have h := phaseSq_nonneg (phaseSq z • v - phaseDot z v • z - phaseArea z v • phaseJ z)
  have he : phaseSq (phaseSq z • v - phaseDot z v • z - phaseArea z v • phaseJ z) =
      (phaseSq z)^2*phaseSq v-phaseSq z*((phaseDot z v)^2+(phaseArea z v)^2) := by
    simp only [phaseSq,map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul,
      phaseDot_J_left,phaseDot_J_right,phaseArea_J_left,phaseArea_self]
    rw [phaseDot_symm v z,phaseArea_skew v z]
    ring
  rw [he] at h
  have hm : 0 ≤ phaseSq z*(phaseSq z*phaseSq v-((phaseDot z v)^2+(phaseArea z v)^2)) := by
    nlinarith only [h]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hq).mp hm)

end

variable {ι : Type*} [Fintype ι]

theorem affineFSForm_eq_exterior (a : ℝ) :
    (affineFSForm a : PlanePhase ι → _) = euclideanExteriorOneForm (affineFSPrimitive a) := by
  funext z
  ext v w
  exact (affineFSPrimitive_exterior a z v w).symm

theorem affineFSForm_positive {a : ℝ} (ha : 0<a) (z v : PlanePhase ι) (hv : v≠0) :
    0 < affineFSForm a z v (phaseJ v) := by
  rw [affineFSForm_apply,phaseArea_J_right,phaseArea_J_right,phaseDot_J_right]
  change 0 < a/(1+phaseSq z)*phaseSq v - a/(1+phaseSq z)^2 *
    (phaseDot z v*phaseDot z v-phaseArea z v*(-phaseArea z v))
  have he : a/(1+phaseSq z)*phaseSq v - a/(1+phaseSq z)^2 *
      (phaseDot z v*phaseDot z v-phaseArea z v*(-phaseArea z v)) =
      a/(1+phaseSq z)^2 * ((1+phaseSq z)*phaseSq v-
        ((phaseDot z v)^2+(phaseArea z v)^2)) := by
    field_simp [(fs_den_pos z).ne']
    ring
  rw [he]
  apply mul_pos (div_pos ha (sq_pos_of_pos (fs_den_pos z)))
  have hc := phase_complex_cauchy z v
  have hp := phaseSq_pos hv
  nlinarith

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function
open Hamiltonian

theorem affinePhase_injective (m : ℕ) : Injective (affinePhase m) := by
  intro z w h
  apply Prod.ext
  · apply Complex.ext
    · exact congrArg Prod.fst (congrFun h none)
    · exact congrArg Prod.snd (congrFun h none)
  · funext j
    apply Complex.ext
    · exact congrArg Prod.fst (congrFun h (some j))
    · exact congrArg Prod.snd (congrFun h (some j))

theorem affinePhase_I (m : ℕ) (z : Affine m) :
    affinePhase m (Complex.I • z)=phaseJ (affinePhase m z) := by
  funext j
  cases j <;> simp [Pi.smul_apply,Complex.mul_re,Complex.mul_im]

 theorem realPhaseDerivative_I {m : ℕ} (L : ℂ →L[ℂ] Affine m) :
    realPhaseDerivative L (0,1)=phaseJ (realPhaseDerivative L (1,0)) := by
  change affinePhase m (L Complex.I)=phaseJ (affinePhase m (L 1))
  have hL := L.map_smul Complex.I (1 : ℂ)
  rw [smul_eq_mul,mul_one] at hL
  rw [hL]
  exact affinePhase_I m (L 1)

 theorem affineFSForm_holomorphic_positive {m : ℕ} {c : ℝ} (hc : 0 < c)
    (z : Affine m) (L : ℂ →L[ℂ] Affine m) (hL : L 1≠0) :
    0<affineFSForm c (affinePhase m z) (realPhaseDerivative L (1,0))
      (realPhaseDerivative L (0,1)) := by
  rw [realPhaseDerivative_I]
  apply affineFSForm_positive hc
  rw [realPhaseDerivative_one]
  intro hz
  apply hL
  exact affinePhase_injective m (by simpa using hz)

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricInfinityDiffeomorph
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian
open scoped BigOperators
section

variable {m : ℕ} {a : Fin m → ℂ}
namespace NormalChart
variable (e : NormalChart a) (x : locus a)

theorem inclusionChart_smooth : ContDiffOn ℂ ∞ (e.inclusionChart x) (e.sliceChart x).target :=
  e.sliceChart_inverse_smooth x

theorem inclusionChart_coordinate {z : ℂ} (hz : z∈(e.sliceChart x).target) :
    curveCoordinate e.coordinate (e.inclusionChart x z)=z :=
  (e.sliceChart x).right_inv hz

theorem inclusionChart_derivative_leftInverse {z : ℂ} (hz : z∈(e.sliceChart x).target) :
    (curveCoordinate e.coordinate).comp (fderiv ℂ (e.inclusionChart x) z)=
      ContinuousLinearMap.id ℂ ℂ := by
  have hd := ((e.inclusionChart_smooth x).contDiffAt ((e.sliceChart x).open_target.mem_nhds hz)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hh : (curveCoordinate e.coordinate ∘ e.inclusionChart x)=ᶠ[𝓝 z] id := by
    filter_upwards [(e.sliceChart x).open_target.mem_nhds hz] with y hy
    exact e.inclusionChart_coordinate x hy
  simpa only [fderiv_comp z (curveCoordinate e.coordinate).differentiableAt hd,
    ContinuousLinearMap.fderiv,fderiv_id] using hh.fderiv_eq (𝕜 := ℂ)

theorem inclusionChart_derivative_injective {z : ℂ} (hz : z∈(e.sliceChart x).target) :
    Injective (fderiv ℂ (e.inclusionChart x) z) := by
  intro v w hvw
  have h := congrArg (curveCoordinate e.coordinate) hvw
  have he := e.inclusionChart_derivative_leftInverse x hz
  have h' : ∀ u,curveCoordinate e.coordinate (fderiv ℂ (e.inclusionChart x) z u)=u :=
    fun u => congrArg (fun L : ℂ→L[ℂ]ℂ => L u) he
  rwa [h' v,h' w] at h

theorem inclusionChart_derivative_one_ne {z : ℂ} (hz : z∈(e.sliceChart x).target) :
    fderiv ℂ (e.inclusionChart x) z 1≠0 := by
  intro h
  exact one_ne_zero ((e.inclusionChart_derivative_injective x hz) (by simpa using h))

end NormalChart

end

end PackingSufficiencySupport.DiagonalQuadrics

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

theorem chartTwoForm_manifoldPullback {Ω : ℝ → ManifoldTwoForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target) :
    chartTwoForm (manifoldPullbackTwoForm Ω e p.1) b p.2 =
      euclideanPullbackTwoForm Ω (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := ((he.mdifferentiable (by simp) _).hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackTwoForm,hd,chartTwoForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v w
  rfl

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartOneForm_transition {α : ManifoldOneForm E M} {b c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target)
    (hc : (extChartAt 𝓘(ℝ,E) b).symm y ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    chartOneForm α b y =
      staticPullbackOneForm (chartOneForm α c)
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y := by
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have he := euclideanPullbackOneForm_chart (α := fun _ => α) (p := (0,y)) hi hc
  simpa only [euclideanPullbackOneForm,chartOneForm,chartDifferential_inverse hy,
    staticPullbackOneForm,Function.comp_apply] using he

theorem chartOneForm_exterior_transition {α : ManifoldOneForm E M} {b c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target)
    (hc : (extChartAt 𝓘(ℝ,E) b).symm y ∈ (extChartAt 𝓘(ℝ,E) c).source)
    (hα : ContDiffAt ℝ ∞ (chartOneForm α c)
      (extChartAt 𝓘(ℝ,E) c ((extChartAt 𝓘(ℝ,E) b).symm y))) :
    euclideanExteriorOneForm (chartOneForm α b) y =
      (euclideanExteriorOneForm (chartOneForm α c)
        (extChartAt 𝓘(ℝ,E) c ((extChartAt 𝓘(ℝ,E) b).symm y))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y) := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)
  have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
    (by simpa only [extChartAt_source] using hc)
  have ht : ContDiffAt ℝ ∞
      (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y :=
    (ho.comp y hi).contDiffAt
  have he : chartOneForm α b =ᶠ[𝓝 y]
      staticPullbackOneForm (chartOneForm α c)
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy,
      hi.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)]
      with z hz hzc
    exact chartOneForm_transition hz hzc
  calc
    _ = euclideanExteriorOneForm
        (staticPullbackOneForm (chartOneForm α c)
          (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm)) y := by
      unfold euclideanExteriorOneForm
      rw [he.fderiv_eq]
    _ = _ := staticPullbackOneForm_exterior hα ht

theorem manifoldExteriorOneForm_chart {α : ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    {b : M} {y : E} (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target) :
    chartTwoForm (manifoldExteriorOneForm α) b y =
      euclideanExteriorOneForm (chartOneForm α b) y := by
  let x := (extChartAt 𝓘(ℝ,E) b).symm y
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) x).source := mem_extChartAt_source x
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have ho := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := x)
    (by simpa only [extChartAt_source] using hx)
  let A : E →L[ℝ] E := (chartDifferential x x).comp
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) b).symm y)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) x ∘ (extChartAt 𝓘(ℝ,E) b).symm) A y :=
    hasMFDerivAt_iff_hasFDerivAt.mp (ho.hasMFDerivAt.comp y hi.hasMFDerivAt)
  have he := hf.fderiv
  dsimp only [A,chartDifferential] at he
  rw [chartOneForm_exterior_transition hy hx ((hα x).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds
      ((extChartAt 𝓘(ℝ,E) x).map_source hx)))]
  change fderiv ℝ (extChartAt 𝓘(ℝ,E) x ∘ (extChartAt 𝓘(ℝ,E) b).symm) y = _ at he
  rw [he]
  simp only [chartTwoForm,manifoldExteriorOneForm,chartDifferential_inverse hy]
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

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem realChart_complex_target (b : locus a) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    Complex.equivRealProdCLM.symm y∈((normalChartAt a b).sliceChart b).target := by
  have he : chartAt RealModel b=realChart a b := rfl
  simp only [mfld_simps,he,realChart] at hy
  exact hy

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricAnnulusDomain
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

 theorem projection_contDiff : ContDiff ℂ ∞ projection := by
  exact (((contDiff_apply ℂ ℂ 0).comp contDiff_snd).sub contDiff_fst).prodMk
    (((contDiff_apply ℂ ℂ 1).comp contDiff_snd).sub contDiff_fst)

 theorem source_equation_zero (x : BaseCurve) : (x.val.2 0)^2=x.val.1^2-1 := by
  simpa only [parameters_zero] using (mem_locus.mp x.property) 0
 theorem source_equation_one (x : BaseCurve) : (x.val.2 1)^2=x.val.1^2-2 := by
  simpa only [parameters_one] using (mem_locus.mp x.property) 1

 theorem inclusion_fst_ne_zero (x : BaseCurve) : (inclusion x).1≠0 := by
  intro h
  have he : x.val.2 0=x.val.1 := sub_eq_zero.mp h
  have h0 := source_equation_zero x
  rw [he] at h0
  have hh : (1:ℂ)=0 := by linear_combination h0
  exact one_ne_zero hh

 theorem inclusion_snd_ne_zero (x : BaseCurve) : (inclusion x).2≠0 := by
  intro h
  have he : x.val.2 1=x.val.1 := sub_eq_zero.mp h
  have h1 := source_equation_one x
  rw [he] at h1
  have hh : (1:ℂ)=0 := by linear_combination h1 / 2
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

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_CubicFubiniStudy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
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

 theorem planeAffine_injective : Injective planeAffine := by
  intro z w h
  exact Prod.ext (congrArg (fun q : Affine 1 => q.1) h)
    (congrArg (fun q : Affine 1 => q.2 0) h)

 theorem cubicChart_derivative_one_ne (b : BaseCurve) {y : ℂ}
    (hy : y∈((normalChartAt (parameters 0) b).sliceChart b).target) :
    fderiv ℂ (cubicChart b) y 1≠0 := by
  let e := normalChartAt (parameters 0) b
  let f := e.inclusionChart b
  have hf : DifferentiableAt ℂ f y :=
    ((e.inclusionChart_smooth b).contDiffAt ((e.sliceChart b).open_target.mem_nhds hy)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hp : DifferentiableAt ℂ (projection ∘ f) y := (projection_contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (f y)).comp y hf
  have hne : (projection (f y)).1≠0 := inclusion_fst_ne_zero ((e.sliceChart b).symm y)
  have hr : DifferentiableAt ℂ recovery (projection (f y)) :=
    (recovery_contDiffOn.contDiffAt ((isOpen_ne_fun continuous_fst continuous_const).mem_nhds hne)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq : recovery ∘ (projection ∘ f)=f := by
    funext z
    exact recovery_inclusion ((e.sliceChart b).symm z)
  have hd : (fderiv ℂ recovery (projection (f y))).comp (fderiv ℂ (projection ∘ f) y)=fderiv ℂ f y := by
    calc
      _=fderiv ℂ (recovery ∘ (projection ∘ f)) y := by
        simpa only [Function.comp_apply] using (fderiv_comp y hr hp).symm
      _=_ := congrArg (fun g => fderiv ℂ g y) heq
  intro hz
  have hz' : planeAffine (fderiv ℂ (projection ∘ f) y 1)=0 := by
    change (fderiv ℂ (planeAffine ∘ (projection ∘ f)) y) 1=0 at hz
    rw [fderiv_comp y planeAffine.differentiableAt hp,ContinuousLinearMap.fderiv] at hz
    exact hz
  have hp0 : fderiv ℂ (projection ∘ f) y 1=0 :=
    planeAffine_injective (by simpa only [map_zero] using hz')
  apply e.inclusionChart_derivative_one_ne b hy
  have hx := congrArg (fun L : ℂ→L[ℂ] Affine 2 => L 1) hd
  simpa only [ContinuousLinearMap.comp_apply,hp0,map_zero] using hx.symm

 theorem weightedProjection_contDiff (D m : ℕ) : ContDiff ℂ ∞ (weightedProjection D m) := by
  apply ContDiff.prodMk (contDiff_fst.pow (D-m))
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact contDiff_snd.pow (D-m)
  · exact (contDiff_fst.pow (D-m)).mul (contDiff_snd.pow m)
  · exact (contDiff_fst.pow m).mul (contDiff_snd.pow (D-m))

 theorem weightedProjection_fderiv_fst (D m : ℕ) (z v : PlaneBase) :
    (fderiv ℂ (weightedProjection D m) z v).1=(D-m:ℕ)*z.1^(D-m-1)*v.1 := by
  have h := ((hasFDerivAt_fst (𝕜 := ℂ) (p := z)).pow (D-m))
  have hc := (ContinuousLinearMap.fst ℂ ℂ (Fin 3→ℂ)).hasFDerivAt.comp z
    ((weightedProjection_contDiff D m).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt
  have he : (ContinuousLinearMap.fst ℂ ℂ (Fin 3→ℂ)) ∘ weightedProjection D m=
      fun z : PlaneBase => z.1^(D-m) := rfl
  rw [he] at hc
  have hd := hc.unique h
  have hh := congrArg (fun A : PlaneBase→L[ℂ] ℂ => A v) hd
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
    smul_apply,nsmul_eq_mul,smul_eq_mul] using hh

 theorem weightedProjection_fderiv_snd (D m : ℕ) (z v : PlaneBase) :
    (fderiv ℂ (weightedProjection D m) z v).2 0=(D-m:ℕ)*z.2^(D-m-1)*v.2 := by
  let P : Affine 3→L[ℂ] ℂ := (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ ℂ (Fin 3→ℂ))
  have h := ((hasFDerivAt_snd (𝕜 := ℂ) (p := z)).pow (D-m))
  have hc := P.hasFDerivAt.comp z
    ((weightedProjection_contDiff D m).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt
  have he : P ∘ weightedProjection D m=fun z : PlaneBase => z.2^(D-m) := rfl
  rw [he] at hc
  have hd := hc.unique h
  have hh := congrArg (fun A : PlaneBase→L[ℂ] ℂ => A v) hd
  simpa only [P,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.proj_apply,smul_apply,nsmul_eq_mul,smul_eq_mul] using hh

 theorem weightedProjection_fderiv_kernel {D m : ℕ} (hm : m<D) {z : PlaneBase}
    (hzv : z.1≠0) (hzw : z.2≠0) {v : PlaneBase}
    (hv : fderiv ℂ (weightedProjection D m) z v=0) : v=0 := by
  have hL : (D-m:ℕ)≠0 := (Nat.sub_pos_of_lt hm).ne'
  have hLc : ((D-m:ℕ):ℂ)≠0 := by exact_mod_cast hL
  have hv0 := weightedProjection_fderiv_fst D m z v
  have hw0 := weightedProjection_fderiv_snd D m z v
  rw [hv] at hv0 hw0
  apply Prod.ext
  · exact (mul_eq_zero.mp hv0.symm).resolve_left (mul_ne_zero hLc (pow_ne_zero _ hzv))
  · exact (mul_eq_zero.mp hw0.symm).resolve_left (mul_ne_zero hLc (pow_ne_zero _ hzw))

 theorem weightedChart_smooth (D m : ℕ) (b : BaseCurve) :
    ContDiffOn ℂ ∞ (weightedChart D m b) ((normalChartAt (parameters 0) b).sliceChart b).target :=
  (weightedProjection_contDiff D m).comp_contDiffOn
    (projection_contDiff.comp_contDiffOn ((normalChartAt (parameters 0) b).inclusionChart_smooth b))

 theorem weightedChart_derivative_one_ne {D m : ℕ} (hm : m<D) (b : BaseCurve) {y : ℂ}
    (hy : y∈((normalChartAt (parameters 0) b).sliceChart b).target) :
    fderiv ℂ (weightedChart D m b) y 1≠0 := by
  let e := normalChartAt (parameters 0) b
  let f := projection ∘ e.inclusionChart b
  have hf : DifferentiableAt ℂ f y :=
    ((projection_contDiff.comp_contDiffOn (e.inclusionChart_smooth b)).contDiffAt
      ((e.sliceChart b).open_target.mem_nhds hy)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  intro hz
  change fderiv ℂ (weightedProjection D m ∘ f) y 1=0 at hz
  rw [fderiv_comp y ((weightedProjection_contDiff D m).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) hf] at hz
  have hz' : fderiv ℂ f y 1=0 := weightedProjection_fderiv_kernel hm
    (inclusion_fst_ne_zero ((e.sliceChart b).symm y))
    (inclusion_snd_ne_zero ((e.sliceChart b).symm y)) hz
  apply cubicChart_derivative_one_ne b hy
  change fderiv ℂ (planeAffine ∘ f) y 1=0
  rw [fderiv_comp y planeAffine.differentiableAt hf,ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply,hz',map_zero]

 theorem weightedPhaseInclusion_smooth (D m : ℕ) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin 3))) ∞ (weightedPhaseInclusion D m) :=
  (affinePhase 3).contDiff.contMDiff.comp
    (((weightedProjection_contDiff D m).restrict_scalars ℝ).contMDiff.comp
      ((projection_contDiff.restrict_scalars ℝ).contMDiff.comp
        (real_inclusion_contMDiff (parameters 0))))

 theorem weightedFSPrimitive_smooth (D m : ℕ) (c : ℝ) :
    SmoothOneFormFamily (fun _ : ℝ => weightedFSPrimitive D m c) := by
  have hα : SmoothOneFormFamily (fun _ : ℝ =>
      (affineFSPrimitive c : PlanePhase (Option (Fin 3)) → _)) :=
    vector_oneForm_smooth (affineFSPrimitive_smooth c)
  intro b
  exact manifoldPullbackOneForm_smooth (α := fun _ : ℝ =>
    (affineFSPrimitive c : PlanePhase (Option (Fin 3)) → _)) (weightedPhaseInclusion_smooth D m) hα b

 theorem weightedFSPrimitive_exterior (D m : ℕ) (c : ℝ) :
    manifoldExteriorOneForm (weightedFSPrimitive D m c)=weightedFSForm D m c := by
  have hα : ∀ z : PlanePhase (Option (Fin 3)),ContDiffOn ℝ ∞
      (chartOneForm (affineFSPrimitive c) z) (extChartAt 𝓘(ℝ,PlanePhase (Option (Fin 3))) z).target := by
    intro z
    rw [show chartOneForm (affineFSPrimitive c) z=affineFSPrimitive c from
      funext (vector_chartOneForm (affineFSPrimitive c) z)]
    exact (affineFSPrimitive_smooth c).contDiffOn
  funext x
  change manifoldExteriorOneForm (manifoldPullbackOneForm
    (fun _ => (affineFSPrimitive c : PlanePhase (Option (Fin 3)) → _)) (weightedPhaseInclusion D m) 0) x=_
  rw [manifold_pullback_exterior hα (weightedPhaseInclusion_smooth D m) x]
  rw [vector_exteriorOneForm,← affineFSForm_eq_exterior]
  rfl

 theorem weighted_phase_chart_function (D m : ℕ) (b : BaseCurve) :
    (weightedPhaseInclusion D m ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm)=
      affinePhase 3 ∘ weightedChart D m b ∘ Complex.equivRealProdCLM.symm := by
  funext y
  have he : chartAt RealModel b=realChart (parameters 0) b := rfl
  simp only [mfld_simps,he,realChart,Function.comp_apply,weightedPhaseInclusion,
    weightedInclusion,weightedChart,inclusion,NormalChart.inclusionChart]
  rfl

 theorem weighted_phase_chart_derivative (D m : ℕ) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    manifoldMapDifferential (E := PlanePhase (Option (Fin 3))) (F := RealModel)
      (weightedPhaseInclusion D m ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y=
    realPhaseDerivative (fderiv ℂ (weightedChart D m b) (Complex.equivRealProdCLM.symm y)) := by
  change mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin 3))) _ y=_
  rw [mfderiv_eq_fderiv,weighted_phase_chart_function]
  have hdf := ((weightedChart_smooth D m b).contDiffAt
    (((normalChartAt (parameters 0) b).sliceChart b).open_target.mem_nhds
      (realChart_complex_target (parameters 0) b hy))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ((affinePhase 3).hasFDerivAt.comp y
    ((hdf.hasFDerivAt.restrictScalars ℝ).comp y Complex.equivRealProdCLM.symm.hasFDerivAt)).fderiv

 theorem weightedFSForm_positive {D m : ℕ} (hm : m<D) {c : ℝ} (hc : 0 < c) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0 < chartTwoForm (weightedFSForm D m c) b y (1,0) (0,1) := by
  rw [weightedFSForm,chartTwoForm_manifoldPullback (weightedPhaseInclusion_smooth D m) (p := (0,y)) hy]
  change 0<affineFSForm c _
    (manifoldMapDifferential (E := PlanePhase (Option (Fin 3))) (F := RealModel)
      (weightedPhaseInclusion D m ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (1,0))
    (manifoldMapDifferential (E := PlanePhase (Option (Fin 3))) (F := RealModel)
      (weightedPhaseInclusion D m ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (0,1))
  rw [weighted_phase_chart_derivative D m b hy]
  apply affineFSForm_holomorphic_positive hc
  exact weightedChart_derivative_one_ne hm b (realChart_complex_target (parameters 0) b hy)

end PackingSufficiencySupport.CubicModel

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

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_ExponentialMoment
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem partition_pos {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (x : E) :
    0<partition w a x := by
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (ha i) (Real.exp_pos _)
  · exact Finset.univ_nonempty

 omit [Nonempty ι] in
 theorem partition_contDiff (w : ι → E) (a : ι → ℝ) : ContDiff ℝ ∞ (partition w a) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (((innerSL ℝ (w i)).contDiff).exp)

 omit [Nonempty ι] in
 theorem partition_hasFDerivAt (w : ι → E) (a : ι → ℝ) (x : E) :
    HasFDerivAt (partition w a) (innerSL ℝ (gradient w a x)) x := by
  have h := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((innerSL ℝ (w i)).hasFDerivAt (x := x)).exp).const_mul (a i))
  convert! h using 1
  · ext y
    simp [partition]
  · simp only [gradient,map_sum,map_smul,smul_smul,innerSL_apply_apply]

 theorem partition_coercive [ProperSpace E] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {δ : ℝ} (hδ : 0<δ)
    (hw : ∀ x : E,∃ i,δ*‖x‖≤ inner ℝ (w i) x) :
    Tendsto (partition w a) (cocompact E) atTop := by
  classical
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  have hb (x : E) : a j*Real.exp (δ*‖x‖)≤partition w a x := by
    obtain ⟨i,hi⟩ := hw x
    calc
      a j*Real.exp (δ*‖x‖)≤a i*Real.exp (inner ℝ (w i) x) :=
        mul_le_mul (hj i (Finset.mem_univ i)) (Real.exp_le_exp.mpr hi)
          (Real.exp_pos _).le (ha i).le
      _≤partition w a x := by
        exact Finset.single_le_sum
          (fun k _ => (mul_pos (ha k) (Real.exp_pos (inner ℝ (w k) x))).le) (Finset.mem_univ i)
  exact tendsto_atTop_mono hb ((Real.tendsto_exp_atTop.comp
    (tendsto_norm_cocompact_atTop.const_mul_atTop hδ)).const_mul_atTop (ha j))

 theorem exists_gradient_zero [ProperSpace E] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {δ : ℝ} (hδ : 0<δ)
    (hw : ∀ x : E,∃ i,δ*‖x‖≤ inner ℝ (w i) x) :
    ∃ x : E,gradient w a x=0 := by
  obtain ⟨x,hx⟩ := (partition_contDiff w a).continuous.exists_forall_le
    (partition_coercive ha hδ hw)
  refine ⟨x,?_⟩
  have hm : IsLocalMin (partition w a) x := Filter.Eventually.of_forall hx
  have hz := hm.hasFDerivAt_eq_zero (partition_hasFDerivAt w a x)
  have he := congrArg (fun L : E →L[ℝ] ℝ => L (gradient w a x)) hz
  change inner ℝ (gradient w a x) (gradient w a x)=0 at he
  exact inner_self_eq_zero.mp he

 theorem exp_difference_nonneg (u v : ℝ) :
    0≤(Real.exp u-Real.exp v)*(u-v) := by
  rcases le_total v u with h|h
  · exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)) (sub_nonneg.mpr h)
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h))
      (sub_nonpos.mpr h)

 theorem exp_difference_pos {u v : ℝ} (h : v<u) :
    0<(Real.exp u-Real.exp v)*(u-v) :=
  mul_pos (sub_pos.mpr (Real.exp_lt_exp.mpr h)) (sub_pos.mpr h)

 omit [Nonempty ι] in
 theorem gradient_zero_unique {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {δ : ℝ} (hδ : 0<δ)
    (hw : ∀ x : E,∃ i,δ*‖x‖≤ inner ℝ (w i) x) {x y : E}
    (hx : gradient w a x=0) (hy : gradient w a y=0) : x=y := by
  classical
  by_contra hxy
  have hd : 0<δ*‖x-y‖ := mul_pos hδ (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
  obtain ⟨j,hj⟩ := hw (x-y)
  have hjp : inner ℝ (w j) y< inner ℝ (w j) x := by
    rw [inner_sub_right] at hj
    linarith
  have hs : 0< ∑ i,a i*((Real.exp (inner ℝ (w i) x)-Real.exp (inner ℝ (w i) y))*
      (inner ℝ (w i) x-inner ℝ (w i) y)) := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (ha i).le (exp_difference_nonneg _ _)
    · exact ⟨j,Finset.mem_univ j,mul_pos (ha j) (exp_difference_pos hjp)⟩
  have he : ∑ i,a i*((Real.exp (inner ℝ (w i) x)-Real.exp (inner ℝ (w i) y))*
      (inner ℝ (w i) x-inner ℝ (w i) y))=
      inner ℝ (gradient w a x-gradient w a y) (x-y) := by
    simp only [gradient,inner_sub_left,sum_inner,real_inner_smul_left,inner_sub_right,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,hx,hy,sub_self,inner_zero_left] at hs
  exact (lt_irrefl (0:ℝ)) hs

 omit [Nonempty ι] in
 theorem gradient_center (w : ι → E) (a : ι → ℝ) (p x : E) :
    gradient (fun i => w i-p) a x = Real.exp (-inner ℝ p x) •
      (gradient w a x-partition w a x • p) := by
  have he (i : ι) : (a i * Real.exp (inner ℝ (w i-p) x)) • (w i-p) =
      Real.exp (-inner ℝ p x) • ((a i*Real.exp (inner ℝ (w i) x)) • w i-
        (a i*Real.exp (inner ℝ (w i) x)) • p) := by
    rw [inner_sub_left,sub_eq_add_neg (inner ℝ (w i) x),Real.exp_add]
    simp only [smul_sub,smul_smul]
    congr 1 <;> congr 1 <;> ring
  simp only [gradient,he,←Finset.smul_sum,Finset.sum_sub_distrib,←Finset.sum_smul,partition]

 theorem moment_eq_iff_gradient_center_zero {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (p x : E) :
    moment w a x=p ↔ gradient (fun i => w i-p) a x=0 := by
  rw [gradient_center,smul_eq_zero]
  simp only [Real.exp_ne_zero,false_or,sub_eq_zero]
  dsimp [moment]
  rw [inv_smul_eq_iff₀ (partition_pos ha x).ne']

 theorem exists_unique_moment [ProperSpace E] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {p : E} (hp : Surrounds w p) : ∃! x,moment w a x=p := by
  obtain ⟨δ,hδ,hw⟩ := hp
  obtain ⟨x,hx⟩ := exists_gradient_zero ha hδ hw
  refine ⟨x,(moment_eq_iff_gradient_center_zero ha p x).mpr hx,?_⟩
  intro y hy
  exact gradient_zero_unique ha hδ hw ((moment_eq_iff_gradient_center_zero ha p y).mp hy) hx

 omit [Fintype ι] in
 theorem surrounds_of_interior {w : ι → E} {p : E}
    (hp : p∈interior (convexHull ℝ (range w))) : Surrounds w p := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  refine ⟨ε/2,half_pos hε,?_⟩
  intro v
  by_cases hv : v=0
  · subst v
    exact ⟨Classical.ofNonempty,by simp⟩
  have hvp : 0<‖v‖ := norm_pos_iff.mpr hv
  let z := p+((ε/2)/‖v‖) • v
  have hz : z∈convexHull ℝ (range w) := by
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    dsimp [z]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos (half_pos hε) hvp),
      div_mul_cancel₀ _ hvp.ne']
    linarith
  obtain ⟨y,⟨i,rfl⟩,hi⟩ := ((innerSL ℝ v).toLinearMap.convexOn convex_univ).exists_ge_of_mem_convexHull
    (subset_univ (range w)) hz
  refine ⟨i,?_⟩
  change inner ℝ v z≤ inner ℝ v (w i) at hi
  have he : inner ℝ v z=inner ℝ v p+(ε/2)*‖v‖ := by
    dsimp [z]
    rw [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  rw [he] at hi
  rw [inner_sub_left,real_inner_comm v (w i),real_inner_comm v p]
  linarith

 omit [Fintype ι] [Nonempty ι] in
 theorem surrounds_isOpen (w : ι → E) : IsOpen {p | Surrounds w p} := by
  apply Metric.isOpen_iff.mpr
  intro p hp
  obtain ⟨δ,hδ,hw⟩ := hp
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro q hq
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro v
  obtain ⟨i,hi⟩ := hw v
  refine ⟨i,?_⟩
  have hc := real_inner_le_norm (q-p) v
  have hnorm : ‖q-p‖<δ/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hq
  have hmul := mul_le_mul_of_nonneg_right hnorm.le (norm_nonneg v)
  rw [inner_sub_left] at hi hc ⊢
  linarith

end
section

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem hessian_apply (w : ι → E) (a : ι → ℝ) (x v : E) :
    hessian w a x v=∑ i, (a i*Real.exp (inner ℝ (w i) x)*inner ℝ (w i) v) • w i := by
  simp [hessian]

 theorem gradient_hasFDerivAt (w : ι → E) (a : ι → ℝ) (x : E) :
    HasFDerivAt (gradient w a) (hessian w a x) x := by
  have h := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    ((((innerSL ℝ (w i)).hasFDerivAt (x := x)).exp).const_mul (a i)).smul_const (w i))
  convert! h using 1
  · ext y
    simp [gradient]
  · simp only [hessian,smul_smul,innerSL_apply_apply]

 theorem hessian_inner (w : ι → E) (a : ι → ℝ) (x v : E) :
    inner ℝ (hessian w a x v) v=
      ∑ i,(a i*Real.exp (inner ℝ (w i) x))*(inner ℝ (w i) v)^2 := by
  rw [hessian_apply,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left]
  ring

 theorem hessian_positive {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (hw : ∀ v : E,v≠0 → ∃ i,inner ℝ (w i) v≠0) (x : E) {v : E} (hv : v≠0) :
    0< inner ℝ (hessian w a x v) v := by
  classical
  rw [hessian_inner]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_pos (ha i) (Real.exp_pos _)).le (sq_nonneg _)
  · obtain ⟨i,hi⟩ := hw v hv
    exact ⟨i,Finset.mem_univ i,mul_pos (mul_pos (ha i) (Real.exp_pos _)) (sq_pos_of_ne_zero hi)⟩

 theorem hessian_isInvertible [FiniteDimensional ℝ E] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hw : ∀ v : E,v≠0 → ∃ i,inner ℝ (w i) v≠0) (x : E) :
    (hessian w a x).IsInvertible := by
  have hi : Injective (hessian w a x) := by
    intro v u h
    by_contra hn
    have hp := hessian_positive ha hw x (sub_ne_zero.mpr hn)
    rw [map_sub,h,sub_self,inner_zero_left] at hp
    exact (lt_irrefl (0:ℝ)) hp
  let L := ContinuousLinearEquiv.ofBijective (hessian w a x)
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi))
  exact ⟨L,rfl⟩

 omit [Fintype ι] in
 theorem surrounds_separates {w : ι → E} {p : E} (hp : Surrounds w p)
    {v : E} (hv : v≠0) : ∃ i,inner ℝ (w i-p) v≠0 := by
  obtain ⟨δ,hδ,hw⟩ := hp
  obtain ⟨i,hi⟩ := hw v
  exact ⟨i,(lt_of_lt_of_le (mul_pos hδ (norm_pos_iff.mpr hv)) hi).ne'⟩

 theorem centeredGradient_contDiff (w : ι → E) :
    ContDiff ℝ ∞ (fun q : ((ι → ℝ) × E) × E => gradient (fun i => w i-q.1.2) q.1.1 q.2) := by
  apply ContDiff.sum
  intro i _
  have ha : ContDiff ℝ ∞ (fun q : ((ι → ℝ) × E) × E => q.1.1 i) := by fun_prop
  have hu : ContDiff ℝ ∞ (fun q : ((ι → ℝ) × E) × E => w i-q.1.2) := by fun_prop
  exact (ha.mul ((hu.inner ℝ contDiff_snd).exp)).smul hu

end

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem inverse_spec {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) : moment w a (inverse w a p)=p :=
  invFun_eq (exists_unique_moment ha hp).exists

 theorem inverse_unique {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) {x : E} (hx : moment w a x=p) : x=inverse w a p :=
  (exists_unique_moment ha hp).unique hx (inverse_spec ha hp)

 omit [Nonempty ι] in
 theorem positiveCoefficients_isOpen : IsOpen {a : ι → ℝ | ∀ i,0<a i} := by
  have h : IsOpen (⋂ i : ι,{a : ι → ℝ | 0<a i}) :=
    isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  simp

 theorem inverse_contDiffAt {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × E => inverse w q.1 q.2) (a,p) := by
  let q := (a,p)
  let x := inverse w a p
  let F : ((ι → ℝ) × E) × E → E :=
    fun t => gradient (fun i => w i-t.1.2) t.1.1 t.2
  have hF : ContDiff ℝ ∞ F := centeredGradient_contDiff w
  have hpartial : (fderiv ℝ F (q,x)).comp (ContinuousLinearMap.inr ℝ ((ι → ℝ) × E) E)=
      hessian (fun i => w i-p) a x := by
    have hc := ((hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (q,x)).hasFDerivAt.comp x
      ((hasFDerivAt_const q x).prodMk (hasFDerivAt_id x)))
    exact hc.unique (gradient_hasFDerivAt (fun i => w i-p) a x)
  have hinv : (fderiv ℝ F (q,x) ∘L ContinuousLinearMap.inr ℝ ((ι → ℝ) × E) E).IsInvertible := by
    rw [hpartial]
    exact hessian_isInvertible ha (fun _ hv => surrounds_separates hp hv) x
  have hzero : F (q,x)=0 :=
    (moment_eq_iff_gradient_center_zero ha p x).mp (inverse_spec ha hp)
  have hapos : ∀ᶠ t : (ι → ℝ) × E in 𝓝 q,∀ i,0<t.1 i := by
    apply (positiveCoefficients_isOpen.preimage continuous_fst).mem_nhds
    exact ha
  have htpos : ∀ᶠ t : (ι → ℝ) × E in 𝓝 q,Surrounds w t.2 := by
    apply ((surrounds_isOpen w).preimage continuous_snd).mem_nhds
    exact hp
  have hloc := hF.contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv
  apply hloc.congr_of_eventuallyEq
  filter_upwards [hF.contDiffAt.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv,hapos,htpos]
    with t ht hta htp
  rw [hzero] at ht
  have hm := (moment_eq_iff_gradient_center_zero hta t.2 _).mpr ht
  exact (inverse_unique hta htp hm).symm

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem monomial_nonneg (k : ℕ × ℕ) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    0 ≤ monomial k r := mul_nonneg (pow_nonneg hr.1 _) (pow_nonneg hr.2 _)

theorem polynomial_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (hzero : ∃ i,k i=(0,0)) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    0<polynomial k a r := by
  classical
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (ha i).le (monomial_nonneg _ hr)
  · obtain ⟨i,hi⟩ := hzero
    refine ⟨i,Finset.mem_univ i,?_⟩
    simpa [hi,monomial] using ha i

theorem monomial_axis (k : ℕ × ℕ) (t : ℝ) :
    monomial k (0,t)=if k.1=0 then t^k.2 else 0 := by
  by_cases h : k.1=0
  · simp [monomial,h]
  · simp [monomial,h,zero_pow h]

theorem nat_mul_power (n : ℕ) (t : ℝ) :
    (n:ℝ)*t^(n-1)*t=(n:ℝ)*t^n := by
  rcases n with _|n
  · simp
  · simp only [Nat.succ_sub_one,pow_succ]
    ring

end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RadialSlopes
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem slopeNumerator_fst_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (he : ∃ i,k i=(1,0)) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    0<(slopeNumerator k a r).1 := by
  classical
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha i).le)
      (pow_nonneg hr.1 _)) (pow_nonneg hr.2 _)
  · obtain ⟨i,hi⟩ := he
    exact ⟨i,Finset.mem_univ i,by simpa [hi] using ha i⟩

theorem slopeNumerator_snd_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (he : ∃ i,k i=(0,1)) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    0<(slopeNumerator k a r).2 := by
  classical
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha i).le)
      (pow_nonneg hr.1 _)) (pow_nonneg hr.2 _)
  · obtain ⟨i,hi⟩ := he
    exact ⟨i,Finset.mem_univ i,by simpa [hi] using ha i⟩

theorem slope_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (hzero : ∃ i,k i=(0,0)) (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) : 0<(slope k a r).1 ∧ 0<(slope k a r).2 := by
  have hP := inv_pos.mpr (polynomial_pos ha hzero hr)
  exact ⟨mul_pos hP (slopeNumerator_fst_pos ha he0 hr),
    mul_pos hP (slopeNumerator_snd_pos ha he1 hr)⟩

theorem moment_eq_radius_slope (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    moment k a r=(r.1*(slope k a r).1,r.2*(slope k a r).2) := by
  have h0 : (numerator k a r).1=r.1*(slopeNumerator k a r).1 := by
    change (∑ i,((k i).1:ℝ)*a i*monomial (k i) r)=
      r.1*(∑ i,((k i).1:ℝ)*a i*r.1^((k i).1-1)*r.2^(k i).2)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold monomial
    calc
      _=a i*r.2^(k i).2*(((k i).1:ℝ)*r.1^(k i).1) := by ring
      _=_ := by rw [← nat_mul_power]; ring
  have h1 : (numerator k a r).2=r.2*(slopeNumerator k a r).2 := by
    change (∑ i,((k i).2:ℝ)*a i*monomial (k i) r)=
      r.2*(∑ i,((k i).2:ℝ)*a i*r.1^(k i).1*r.2^((k i).2-1))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold monomial
    calc
      _=a i*r.1^(k i).1*(((k i).2:ℝ)*r.2^(k i).2) := by ring
      _=_ := by rw [← nat_mul_power]; ring
  apply Prod.ext
  · change (polynomial k a r)⁻¹*(numerator k a r).1=
      r.1*((polynomial k a r)⁻¹*(slopeNumerator k a r).1)
    rw [h0]
    ring
  · change (polynomial k a r)⁻¹*(numerator k a r).2=
      r.2*((polynomial k a r)⁻¹*(slopeNumerator k a r).2)
    rw [h1]
    ring

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Function

 theorem openTrapezoid_isOpen (A B : ℝ) : IsOpen (openTrapezoid A B) := by
  have hc (j : Fin 2) : Continuous (fun p : MomentPlane => p j) := by fun_prop
  exact ((isOpen_lt continuous_const (hc 0)).inter
    ((isOpen_lt (hc 0) continuous_const).inter
      ((isOpen_lt continuous_const (hc 1)).inter
        (isOpen_lt ((hc 0).add (hc 1)) continuous_const))))

 theorem trapezoid_mem_convexHull {A B : ℝ} {p : MomentPlane} (hp : p∈openTrapezoid A B) :
    p∈convexHull ℝ (range (trapezoidCorners A B)) := by
  have hA : 0<A := hp.1.trans hp.2.1
  have hB : 0<B-p 0 := by linarith [hp.2.2.1,hp.2.2.2]
  let l := p 0/A
  let t := p 1/(B-p 0)
  have hl0 : 0<l := div_pos hp.1 hA
  have hl1 : l<1 := (div_lt_one hA).mpr hp.2.1
  have ht0 : 0<t := div_pos hp.2.2.1 hB
  have ht1 : t<1 := (div_lt_one hB).mpr (by linarith [hp.2.2.2])
  let c : Fin 4 → ℝ := ![(1-l)*(1-t),l*(1-t),l*t,(1-l)*t]
  apply mem_convexHull_of_exists_fintype c (trapezoidCorners A B)
  · intro i
    fin_cases i <;> dsimp [c] <;> positivity
  · simp only [c,Fin.sum_univ_succ]
    dsimp
    ring
  · intro i
    exact mem_range_self i
  · ext j
    fin_cases j <;>
      simp [c,trapezoidCorners,planeVector,Fin.sum_univ_succ,l,t] <;>
      field_simp <;> ring

 theorem trapezoid_interior {ι : Type*} {w : ι → MomentPlane} {A B : ℝ}
    (hw : range (trapezoidCorners A B)⊆range w) {p : MomentPlane}
    (hp : p∈openTrapezoid A B) : p∈interior (convexHull ℝ (range w)) := by
  have hsub : openTrapezoid A B⊆convexHull ℝ (range w) := by
    intro q hq
    exact convexHull_mono hw (trapezoid_mem_convexHull hq)
  exact interior_maximal hsub (openTrapezoid_isOpen A B) hp

 theorem trapezoidWeight_corners {A B : ℕ} (hAB : A≤B) :
    range (trapezoidCorners A B)⊆range (trapezoidWeight A B) := by
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · refine ⟨⟨(⟨0,by omega⟩,⟨0,by omega⟩),by simp⟩,?_⟩
    simp [trapezoidWeight,trapezoidCorners]
  · refine ⟨⟨(⟨A,by omega⟩,⟨0,by omega⟩),by simp [hAB]⟩,?_⟩
    simp [trapezoidWeight,trapezoidCorners]
  · refine ⟨⟨(⟨A,by omega⟩,⟨B-A,by omega⟩),by simp [Nat.add_sub_of_le hAB]⟩,?_⟩
    simp [trapezoidWeight,trapezoidCorners,Nat.cast_sub hAB]
  · refine ⟨⟨(⟨0,by omega⟩,⟨B,by omega⟩),by simp⟩,?_⟩
    simp [trapezoidWeight,trapezoidCorners]

 theorem trapezoidWeight_surrounds {A B : ℕ} (hAB : A≤B) {p : MomentPlane}
    (hp : p∈openTrapezoid A B) : Surrounds (trapezoidWeight A B) p :=
  surrounds_of_interior (trapezoid_interior (trapezoidWeight_corners hAB) hp)

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem expRadius_logRadius {r : Plane} (hr : 0 < r.1 ∧ 0 < r.2) :
    expRadius (logRadius r)=r := by
  apply Prod.ext <;> simp [expRadius,logRadius,planeVector,Real.exp_log,hr.1,hr.2]

theorem monomial_expRadius (k : ℕ × ℕ) (x : MomentPlane) :
    monomial k (expRadius x)=Real.exp (inner ℝ (planeVector k.1 k.2) x) := by
  simp [monomial,expRadius,planeVector,PiLp.inner_apply,Fin.sum_univ_succ,
    ← Real.exp_nat_mul,← Real.exp_add,mul_comm]

theorem polynomial_expRadius (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : MomentPlane) :
    polynomial k a (expRadius x)=partition (weight k) a x := by
  apply Finset.sum_congr rfl
  intro i _
  rw [monomial_expRadius]
  rfl

theorem moment_expRadius (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : MomentPlane) :
    planeVector (moment k a (expRadius x)).1 (moment k a (expRadius x)).2=
      FiniteMoment.moment (weight k) a x := by
  rw [FiniteMoment.moment,← polynomial_expRadius]
  ext j
  fin_cases j <;>
    simp [moment,numerator,gradient,weight,planeVector,monomial_expRadius,
      mul_assoc,mul_comm,mul_left_comm]

theorem exists_positive_radial_solution [Nonempty ι] {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {p : Plane} (hp : Surrounds (weight k) (planeVector p.1 p.2)) :
    ∃ r : Plane, (0 < r.1 ∧ 0 < r.2) ∧ moment k a r=p := by
  let x := inverse (weight k) a (planeVector p.1 p.2)
  refine ⟨expRadius x,⟨Real.exp_pos _,Real.exp_pos _⟩,?_⟩
  have he := moment_expRadius k a x
  rw [inverse_spec ha hp] at he
  exact Prod.ext (congrArg (fun z : MomentPlane => z 0) he)
    (congrArg (fun z : MomentPlane => z 1) he)

theorem moment_axis_fst (k : ι → ℕ × ℕ) (a : ι → ℝ) (t : ℝ) :
    (moment k a (0,t)).1=0 := by
  change (polynomial k a (0,t))⁻¹*(∑ i,((k i).1:ℝ)*a i*monomial (k i) (0,t))=0
  have h : (∑ i,((k i).1:ℝ)*a i*monomial (k i) (0,t))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [monomial_axis]
    by_cases h : (k i).1=0 <;> simp [h]
  rw [h,mul_zero]

theorem moment_origin (k : ι → ℕ × ℕ) (a : ι → ℝ) : moment k a (0,0)=(0,0) := by
  apply Prod.ext
  · exact moment_axis_fst k a 0
  · change (polynomial k a (0,0))⁻¹*(∑ i,((k i).2:ℝ)*a i*monomial (k i) (0,0))=0
    have h : (∑ i,((k i).2:ℝ)*a i*monomial (k i) (0,0))=0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases h : (k i).2=0
      · simp [monomial,h]
      · simp [monomial,zero_pow h]
    rw [h,mul_zero]

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators
open Function

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exp_difference_strict {u v : ℝ} (h : u≠v) :
    0<(Real.exp u-Real.exp v)*(u-v) := by
  rcases lt_or_gt_of_ne h with hlt|hgt
  · have h := exp_difference_pos hlt
    nlinarith
  · exact exp_difference_pos hgt

theorem gradient_zero_unique_of_separates {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hw : ∀ v : E,v≠0 → ∃ i,inner ℝ (w i) v≠0)
    {x y : E} (hx : gradient w a x=0) (hy : gradient w a y=0) : x=y := by
  classical
  by_contra hxy
  obtain ⟨j,hj⟩ := hw (x-y) (sub_ne_zero.mpr hxy)
  have hjn : inner ℝ (w j) x≠inner ℝ (w j) y := by
    rwa [inner_sub_right,sub_ne_zero] at hj
  have hs : 0<∑ i,a i*((Real.exp (inner ℝ (w i) x)-Real.exp (inner ℝ (w i) y))*
      (inner ℝ (w i) x-inner ℝ (w i) y)) := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (ha i).le (exp_difference_nonneg _ _)
    · exact ⟨j,Finset.mem_univ j,mul_pos (ha j) (exp_difference_strict hjn)⟩
  have he : ∑ i,a i*((Real.exp (inner ℝ (w i) x)-Real.exp (inner ℝ (w i) y))*
      (inner ℝ (w i) x-inner ℝ (w i) y))=
      inner ℝ (gradient w a x-gradient w a y) (x-y) := by
    simp only [gradient,inner_sub_left,sum_inner,real_inner_smul_left,inner_sub_right,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,hx,hy,sub_self,inner_zero_left] at hs
  exact (lt_irrefl (0:ℝ)) hs

theorem moment_unique_of_separates [Nonempty ι] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {p : E}
    (hw : ∀ v : E,v≠0 → ∃ i,inner ℝ (w i-p) v≠0)
    {x y : E} (hx : moment w a x=p) (hy : moment w a y=p) : x=y :=
  gradient_zero_unique_of_separates ha hw
    ((moment_eq_iff_gradient_center_zero ha p x).mp hx)
    ((moment_eq_iff_gradient_center_zero ha p y).mp hy)

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem sum_face (k : ι → ℕ × ℕ) (f : ι → ℝ) :
    (∑ i, if (k i).1=0 then f i else 0)=∑ i : Face k,f i.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

theorem polynomial_face_exp (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : ℝ) :
    polynomial k a (0,Real.exp x)=partition (faceWeight k) (fun i => a i.val) x := by
  calc
    _=∑ i,if (k i).1=0 then a i*Real.exp (((k i).2:ℝ)*x) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [monomial_axis]
      by_cases h : (k i).1=0 <;> simp [h,Real.exp_nat_mul]
    _=_ := by
      rw [sum_face]
      apply Finset.sum_congr rfl
      intro i _
      simp [faceWeight,mul_comm]

theorem numerator_face_exp_snd (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : ℝ) :
    (numerator k a (0,Real.exp x)).2=
      gradient (faceWeight k) (fun i => a i.val) x := by
  calc
    _=∑ i,if (k i).1=0 then ((k i).2:ℝ)*a i*Real.exp (((k i).2:ℝ)*x) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [monomial_axis]
      by_cases h : (k i).1=0 <;> simp [h,Real.exp_nat_mul]
    _=_ := by
      rw [sum_face]
      apply Finset.sum_congr rfl
      intro i _
      simp [faceWeight,mul_comm,mul_left_comm,mul_assoc]

theorem moment_face_exp (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : ℝ) :
    moment k a (0,Real.exp x)=
      (0,FiniteMoment.moment (faceWeight k) (fun i => a i.val) x) := by
  apply Prod.ext
  · exact moment_axis_fst k a _
  · change (polynomial k a (0,Real.exp x))⁻¹*(numerator k a (0,Real.exp x)).2=_
    rw [polynomial_face_exp,numerator_face_exp_snd]
    rfl

omit [Fintype ι] in
theorem interval_surrounds {w : ι → ℝ} {B p : ℝ}
    (h0 : ∃ i,w i=0) (hB : ∃ i,w i=B) (hp : 0<p ∧ p<B) : Surrounds w p := by
  refine ⟨min p (B-p),lt_min hp.1 (sub_pos.mpr hp.2),?_⟩
  intro v
  rcases le_total 0 v with hv|hv
  · obtain ⟨i,hi⟩ := hB
    refine ⟨i,?_⟩
    simp only [hi,Real.norm_eq_abs,abs_of_nonneg hv]
    change min p (B-p)*v≤v*(B-p)
    nlinarith [min_le_right p (B-p)]
  · obtain ⟨i,hi⟩ := h0
    refine ⟨i,?_⟩
    simp only [hi,Real.norm_eq_abs,abs_of_nonpos hv,zero_sub]
    change min p (B-p)*(-v)≤v*(-p)
    nlinarith [min_le_left p (B-p)]

omit [Fintype ι] in
theorem interval_separates {w : ι → ℝ} {B : ℝ} (hB : B≠0)
    (h0 : ∃ i,w i=0) (h1 : ∃ i,w i=B) (p : ℝ) {v : ℝ} (hv : v≠0) :
    ∃ i,inner ℝ (w i-p) v≠0 := by
  by_cases hp : p=0
  · obtain ⟨i,hi⟩ := h1
    refine ⟨i,?_⟩
    simpa [hi,hp] using mul_ne_zero hv hB
  · obtain ⟨i,hi⟩ := h0
    refine ⟨i,?_⟩
    simpa [hi] using mul_ne_zero hv (neg_ne_zero.mpr hp)

theorem exists_axis_solution {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) {B : ℕ} (hB : ∃ i,k i=(0,B)) {p : ℝ}
    (hp : 0<p ∧ p<B) : ∃ t : ℝ,0<t ∧ moment k a (0,t)=(0,p) := by
  obtain ⟨i0,hi0⟩ := h0
  obtain ⟨iB,hiB⟩ := hB
  let : Nonempty (Face k) := ⟨⟨i0,by simp [hi0]⟩⟩
  have hw0 : ∃ i : Face k,faceWeight k i=0 := ⟨⟨i0,by simp [hi0]⟩,by simp [faceWeight,hi0]⟩
  have hwB : ∃ i : Face k,faceWeight k i=(B:ℝ) := ⟨⟨iB,by simp [hiB]⟩,by simp [faceWeight,hiB]⟩
  obtain ⟨x,hx,_⟩ := exists_unique_moment (fun i : Face k => ha i.val)
    (interval_surrounds hw0 hwB hp)
  exact ⟨Real.exp x,Real.exp_pos _,by rw [moment_face_exp,hx]⟩

theorem positive_axis_unique {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) (h1 : ∃ i,k i=(0,1)) {t u p : ℝ} (ht : 0<t) (hu : 0<u)
    (htp : moment k a (0,t)=(0,p)) (hup : moment k a (0,u)=(0,p)) : t=u := by
  obtain ⟨i0,hi0⟩ := h0
  obtain ⟨i1,hi1⟩ := h1
  let : Nonempty (Face k) := ⟨⟨i0,by simp [hi0]⟩⟩
  have hw0 : ∃ i : Face k,faceWeight k i=0 := ⟨⟨i0,by simp [hi0]⟩,by simp [faceWeight,hi0]⟩
  have hw1 : ∃ i : Face k,faceWeight k i=(1:ℝ) := ⟨⟨i1,by simp [hi1]⟩,by simp [faceWeight,hi1]⟩
  have hmt : FiniteMoment.moment (faceWeight k) (fun i => a i.val) (Real.log t)=p := by
    have h := moment_face_exp k a (Real.log t)
    rw [Real.exp_log ht,htp] at h
    exact (congrArg Prod.snd h).symm
  have hmu : FiniteMoment.moment (faceWeight k) (fun i => a i.val) (Real.log u)=p := by
    have h := moment_face_exp k a (Real.log u)
    rw [Real.exp_log hu,hup] at h
    exact (congrArg Prod.snd h).symm
  have he := moment_unique_of_separates (fun i : Face k => ha i.val)
    (fun v hv => interval_separates one_ne_zero hw0 hw1 p hv) hmt hmu
  have h := congrArg Real.exp he
  simpa only [Real.exp_log ht,Real.exp_log hu] using h

end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RadialSwap
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
variable {ι : Type*} [Fintype ι]

theorem polynomial_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    polynomial (fun i => (k i).swap) a r.swap=polynomial k a r := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [monomial,Prod.fst_swap,Prod.snd_swap]
  ring

theorem numerator_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    numerator (fun i => (k i).swap) a r.swap=(numerator k a r).swap := by
  apply Prod.ext <;> apply Finset.sum_congr rfl <;> intro i _
  all_goals simp only [monomial,Prod.fst_swap,Prod.snd_swap]; ring

theorem moment_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    moment (fun i => (k i).swap) a r.swap=(moment k a r).swap := by
  unfold moment
  rw [polynomial_swap,numerator_swap]
  rfl




theorem basis_weights_separate {k : ι → ℕ × ℕ} (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) (p : MomentPlane)
    {v : MomentPlane} (hv : v≠0) : ∃ i,inner ℝ (weight k i-p) v≠0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨i0,hi0⟩ := h0
  obtain ⟨i1,hi1⟩ := he0
  obtain ⟨i2,hi2⟩ := he1
  have hp : inner ℝ p v=0 := by
    have h := hn i0
    have hw : weight k i0=0 := by ext j; fin_cases j <;> simp [weight,hi0,planeVector]
    simpa only [hw,zero_sub,inner_neg_left,neg_eq_zero] using h
  have hv0 : v 0=0 := by
    have h := hn i1
    simpa [inner_sub_left,hp,weight,hi1,planeVector,PiLp.inner_apply,Fin.sum_univ_succ] using h
  have hv1 : v 1=0 := by
    have h := hn i2
    simpa [inner_sub_left,hp,weight,hi2,planeVector,PiLp.inner_apply,Fin.sum_univ_succ] using h
  apply hv
  ext j
  fin_cases j <;> assumption

theorem positive_radial_unique_basis {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    {r s : Plane} (hr : 0 < r.1 ∧ 0 < r.2) (hs : 0 < s.1 ∧ 0 < s.2)
    (he : moment k a r=moment k a s) : r=s := by
  let : Nonempty ι := ⟨h0.choose⟩
  let p := planeVector (moment k a r).1 (moment k a r).2
  have hre : FiniteMoment.moment (weight k) a (logRadius r)=p := by
    rw [← moment_expRadius,expRadius_logRadius hr]
  have hse : FiniteMoment.moment (weight k) a (logRadius s)=p := by
    rw [← moment_expRadius,expRadius_logRadius hs,← he]
  have hh := moment_unique_of_separates ha (fun v hv => basis_weights_separate h0 he0 he1 p hv) hre hse
  have h := congrArg expRadius hh
  simpa only [expRadius_logRadius hr,expRadius_logRadius hs] using h

theorem moment_zero_coordinates {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    ((moment k a r).1=0 ↔ r.1=0) ∧ ((moment k a r).2=0 ↔ r.2=0) := by
  have hs := slope_pos ha h0 he0 he1 hr
  rw [moment_eq_radius_slope]
  exact ⟨mul_eq_zero_iff_right hs.1.ne',mul_eq_zero_iff_right hs.2.ne'⟩

theorem moment_injective_quadrant {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) :
    InjOn (moment k a) {r : Plane | 0 ≤ r.1 ∧ 0 ≤ r.2} := by
  intro r hr s hs he
  have hzr := moment_zero_coordinates ha h0 he0 he1 hr
  have hzs := moment_zero_coordinates ha h0 he0 he1 hs
  have hz0 : r.1=0 ↔ s.1=0 := hzr.1.symm.trans ((congrArg Prod.fst he) ▸ hzs.1)
  have hz1 : r.2=0 ↔ s.2=0 := hzr.2.symm.trans ((congrArg Prod.snd he) ▸ hzs.2)
  by_cases hr0 : r.1=0
  · have hs0 := hz0.mp hr0
    by_cases hr1 : r.2=0
    · exact Prod.ext (hr0.trans hs0.symm) (hr1.trans (hz1.mp hr1).symm)
    · have hrp : 0 < r.2 := lt_of_le_of_ne hr.2 (Ne.symm hr1)
      have hsp : 0 < s.2 := lt_of_le_of_ne hs.2 (Ne.symm (fun h => hr1 (hz1.mpr h)))
      have hrr : r=(0,r.2) := Prod.ext hr0 rfl
      have hss : s=(0,s.2) := Prod.ext hs0 rfl
      have hp : moment k a (0,r.2)=(0,(moment k a (0,r.2)).2) :=
        Prod.ext (moment_axis_fst k a _) rfl
      have hps : moment k a (0,s.2)=(0,(moment k a (0,r.2)).2) := by
        rw [← hss,← he,hrr]
        exact hp
      exact Prod.ext (hr0.trans hs0.symm) (positive_axis_unique ha h0 he1 hrp hsp hp hps)
  · have hs0 : s.1≠0 := fun h => hr0 (hz0.mpr h)
    have hrp : 0 < r.1 := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    have hsp : 0 < s.1 := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    by_cases hr1 : r.2=0
    · have hs1 := hz1.mp hr1
      have h0' : ∃ i,(k i).swap=(0,0) := by obtain ⟨i,hi⟩ := h0; exact ⟨i,by simp [hi]⟩
      have h1' : ∃ i,(k i).swap=(0,1) := by obtain ⟨i,hi⟩ := he0; exact ⟨i,by simp [hi]⟩
      have hrr : r.swap=(0,r.1) := Prod.ext hr1 rfl
      have hss : s.swap=(0,s.1) := Prod.ext hs1 rfl
      have hes : moment (fun i => (k i).swap) a r.swap=moment (fun i => (k i).swap) a s.swap := by
        rw [moment_swap,moment_swap,he]
      rw [hrr,hss] at hes
      have hp : moment (fun i => (k i).swap) a (0,r.1)=
          (0,(moment (fun i => (k i).swap) a (0,r.1)).2) :=
        Prod.ext (moment_axis_fst _ a _) rfl
      exact Prod.ext (positive_axis_unique ha h0' h1' hrp hsp hp (hes.symm.trans hp))
        (hr1.trans hs1.symm)
    · exact positive_radial_unique_basis ha h0 he0 he1
        ⟨hrp,lt_of_le_of_ne hr.2 (Ne.symm hr1)⟩
        ⟨hsp,lt_of_le_of_ne hs.2 (Ne.symm (fun h => hr1 (hz1.mpr h)))⟩ he




theorem nonnegativeInverse_nonneg (k : ι → ℕ × ℕ) (a : ι → ℝ) (p : Plane) :
    0≤(nonnegativeInverse k a p).1 ∧ 0≤(nonnegativeInverse k a p).2 :=
  (invFun (fun r : Quadrant => moment k a r.val) p).property

theorem nonnegativeInverse_spec {k : ι → ℕ × ℕ} {a : ι → ℝ} {p : Plane}
    (hp : ∃ r : Plane,(0 ≤ r.1 ∧ 0 ≤ r.2) ∧ moment k a r=p) :
    moment k a (nonnegativeInverse k a p)=p := by
  change (fun r : Quadrant => moment k a r.val)
    (invFun (fun r : Quadrant => moment k a r.val) p)=p
  exact invFun_eq (f := fun r : Quadrant => moment k a r.val)
    (by obtain ⟨r,hr,he⟩ := hp; exact ⟨⟨r,hr⟩,he⟩)

theorem nonnegativeInverse_of_moment {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) : nonnegativeInverse k a (moment k a r)=r := by
  apply moment_injective_quadrant ha h0 he0 he1 (nonnegativeInverse_nonneg _ _ _) hr
  exact nonnegativeInverse_spec ⟨r,hr,rfl⟩

theorem nonnegativeInverse_eq_of_moment {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r p : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (he : moment k a r=p) : nonnegativeInverse k a p=r := by
  rw [← he]
  exact nonnegativeInverse_of_moment ha h0 he0 he1 hr


end

section

open scoped BigOperators Topology ContDiff
open Set Filter Function

theorem lattice_zero (A B : ℕ) : ∃ i : TrapezoidWeight A B,latticeIndex i=(0,0) :=
  ⟨⟨(⟨0,by omega⟩,⟨0,by omega⟩),by simp⟩,rfl⟩

theorem lattice_unit_fst {A B : ℕ} (hA : 0<A) (hAB : A≤B) :
    ∃ i : TrapezoidWeight A B,latticeIndex i=(1,0) :=
  ⟨⟨(⟨1,by omega⟩,⟨0,by omega⟩),by simp; omega⟩,rfl⟩

theorem lattice_unit_snd {A B : ℕ} (hA : 0<A) (hAB : A≤B) :
    ∃ i : TrapezoidWeight A B,latticeIndex i=(0,1) :=
  ⟨⟨(⟨0,by omega⟩,⟨1,by omega⟩),by simp; omega⟩,rfl⟩

theorem lattice_end_fst {A B : ℕ} (hAB : A≤B) :
    ∃ i : TrapezoidWeight A B,latticeIndex i=(A,0) :=
  ⟨⟨(⟨A,by omega⟩,⟨0,by omega⟩),by simp [hAB]⟩,rfl⟩

theorem lattice_end_snd (A B : ℕ) :
    ∃ i : TrapezoidWeight A B,latticeIndex i=(0,B) :=
  ⟨⟨(⟨0,by omega⟩,⟨B,by omega⟩),by simp⟩,rfl⟩

theorem trapezoid_radial_surjective {A B : ℕ} (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ∃ r : Plane,(0 ≤ r.1 ∧ 0 ≤ r.2) ∧ moment latticeIndex a r=p := by
  by_cases hp0 : p.1=0
  · by_cases hp1 : p.2=0
    · refine ⟨(0,0),⟨le_rfl,le_rfl⟩,?_⟩
      rw [moment_origin]
      exact Prod.ext hp0.symm hp1.symm
    · obtain ⟨t,ht,he⟩ := exists_axis_solution ha (lattice_zero A B) (lattice_end_snd A B)
        (p:=p.2) ⟨lt_of_le_of_ne hp.2.2.1 (Ne.symm hp1),by simpa [hp0] using hp.2.2.2⟩
      exact ⟨(0,t),⟨le_rfl,ht.le⟩,he.trans (Prod.ext hp0.symm rfl)⟩
  · have hp0p : 0<p.1 := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    by_cases hp1 : p.2=0
    · have hzero : ∃ i : TrapezoidWeight A B,(latticeIndex i).swap=(0,0) := by
        obtain ⟨i,hi⟩ := lattice_zero A B
        exact ⟨i,by simp [hi]⟩
      have hend : ∃ i : TrapezoidWeight A B,(latticeIndex i).swap=(0,A) := by
        obtain ⟨i,hi⟩ := lattice_end_fst hAB
        exact ⟨i,by simp [hi]⟩
      obtain ⟨t,ht,he⟩ := exists_axis_solution ha hzero hend ⟨hp0p,hp.2.1⟩
      refine ⟨(t,0),⟨ht.le,le_rfl⟩,?_⟩
      have hh := moment_swap latticeIndex a (t,0)
      change moment (fun i => (latticeIndex i).swap) a (0,t)=
        (moment latticeIndex a (t,0)).swap at hh
      rw [he] at hh
      have hx := congrArg Prod.swap hh
      exact (show moment latticeIndex a (t,0)=(p.1,0) by simpa using hx.symm).trans
        (Prod.ext rfl hp1.symm)
    · obtain ⟨r,hr,he⟩ := exists_positive_radial_solution ha
        (show Surrounds (weight (latticeIndex (A:=A) (B:=B))) (planeVector p.1 p.2) from
          trapezoidWeight_surrounds hAB ⟨hp0p,hp.2.1,lt_of_le_of_ne hp.2.2.1 (Ne.symm hp1),hp.2.2.2⟩)
      exact ⟨r,⟨hr.1.le,hr.2.le⟩,he⟩


end

section

open scoped BigOperators Topology ContDiff
open Set Filter Function
variable {ι : Type*} [Fintype ι]

theorem nonnegativeInverse_exp [Nonempty ι] {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : Surrounds (weight k) (planeVector p.1 p.2)) :
    nonnegativeInverse k a p=expRadius (inverse (weight k) a (planeVector p.1 p.2)) := by
  apply nonnegativeInverse_eq_of_moment ha h0 he0 he1
    ⟨(Real.exp_pos _).le,(Real.exp_pos _).le⟩
  have he := moment_expRadius k a (inverse (weight k) a (planeVector p.1 p.2))
  rw [inverse_spec ha hp] at he
  exact Prod.ext (congrArg (fun z : MomentPlane => z 0) he)
    (congrArg (fun z : MomentPlane => z 1) he)


end


open scoped BigOperators Topology ContDiff
open Set Filter Function



end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_AnalyticBoundary
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem gibbs_pos {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (x : E) (i : ι) :
    0<gibbs w a x i := div_pos (mul_pos (ha i) (Real.exp_pos _)) (partition_pos ha x)

 theorem sum_gibbs {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (x : E) :
    ∑ i,gibbs w a x i=1 := by
  simp only [gibbs,←Finset.sum_div]
  change partition w a x / partition w a x = 1
  exact div_self (partition_pos ha x).ne'

 omit [Nonempty ι] in
 theorem gibbs_mean {w : ι → E} {a : ι → ℝ} (x : E) :
    ∑ i,gibbs w a x i • w i=moment w a x := by
  simp only [gibbs,moment,gradient,Finset.smul_sum,smul_smul,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

 theorem gibbs_log {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (x : E) (i : ι) :
    Real.log (gibbs w a x i)=Real.log (a i)+inner ℝ (w i) x-Real.log (partition w a x) := by
  rw [gibbs,Real.log_div (mul_pos (ha i) (Real.exp_pos _)).ne' (partition_pos ha x).ne',
    Real.log_mul (ha i).ne' (Real.exp_ne_zero _),Real.log_exp]

end

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 omit [FiniteDimensional ℝ E] in
 theorem selected_pos {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (p : E) (i : ι) :
    0 < selected w a p i := gibbs_pos ha _ _

 omit [FiniteDimensional ℝ E] in
 theorem selected_sum {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (p : E) :
    ∑ i,selected w a p i=1 := sum_gibbs ha _

 theorem selected_mean {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) : ∑ i,selected w a p i • w i=p :=
  (gibbs_mean _).trans (inverse_spec ha hp)

 theorem selected_contDiffAt {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) (i : ι) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × E => selected w q.1 q.2 i) (a,p) := by
  have hx := inverse_contDiffAt ha hp
  have hnum (j : ι) : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × E =>
      q.1 j*Real.exp (inner ℝ (w j) (inverse w q.1 q.2))) (a,p) :=
    (by fun_prop : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × E => q.1 j) (a,p)).mul
      ((contDiffAt_const.inner ℝ hx).exp)
  exact (hnum i).div (ContDiffAt.sum (fun j _ => hnum j)) (partition_pos ha _).ne'

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι : Type*} [Fintype ι]

theorem probability_expRadius (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : MomentPlane) (i : ι) :
    probability k a (expRadius x) i=gibbs (weight k) a x i := by
  simp only [probability,monomial_expRadius,polynomial_expRadius,gibbs,weight]

theorem selected_eq_exponential [Nonempty ι] {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : Surrounds (weight k) (planeVector p.1 p.2)) (i : ι) :
    selected k a p i=FiniteMoment.selected (weight k) a (planeVector p.1 p.2) i := by
  unfold selected
  rw [nonnegativeInverse_exp ha h0 he0 he1 hp,probability_expRadius]
  rfl

end

end PackingSufficiencySupport.FiniteMoment.Radial

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open scoped BigOperators
section

section FormOperations
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem SmoothOneFormFamily.zero :
    SmoothOneFormFamily (fun _ : P => (0 : ManifoldOneForm E M)) := by
  intro c
  simpa only [chartOneForm_zero] using
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : P × E => (0 : E →L[ℝ] ℝ)) _)

theorem SmoothOneFormFamily.sum {I : Type*} (s : Finset I)
    {α : I → P → ManifoldOneForm E M} (hα : ∀ i ∈ s, SmoothOneFormFamily (α i)) :
    SmoothOneFormFamily (fun p => ∑ i ∈ s, α i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using SmoothOneFormFamily.zero (P := P)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hα i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hα j (Finset.mem_insert_of_mem hj)))

end FormOperations

end
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

 omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem chartOneForm_spatial_smul (ρ : M → ℝ) (α : ManifoldOneForm E M) (c : M) (y : E) :
    chartOneForm (fun x => ρ x • α x) c y=
      ρ ((extChartAt 𝓘(ℝ,E) c).symm y) • chartOneForm α c y := by
  ext u
  rfl

 theorem SmoothOneFormFamily.spatial_smul [IsManifold 𝓘(ℝ,E) ∞ M]
    {α : P → ManifoldOneForm E M} (hα : SmoothOneFormFamily α) {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ ρ) :
    SmoothOneFormFamily (fun p x => ρ x • α p x) := by
  intro c q hq
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hq.2)
  have hrs := (hρ.contMDiffAt.comp q.2 hi).contDiffAt.comp q contDiffAt_snd
  have hfs := (hα c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds hq)
  simpa only [chartOneForm_spatial_smul,Pi.smul_def',Function.comp_apply] using (hrs.smul hfs).contDiffWithinAt

end

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem coefficientNorm_pos (D m : ℕ) (x : BaseCurve) : 0 < coefficientNorm D m x := by
  dsimp [coefficientNorm]
  linarith [phaseSq_nonneg (weightedPhaseInclusion D m x)]

 theorem coefficientNorm_smooth (D m : ℕ) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (coefficientNorm D m) :=
  contMDiff_const.add (phaseSq_smooth.contMDiff.comp (weightedPhaseInclusion_smooth D m))

 theorem reducedProbability_smooth {w : ι → MomentPlane} (D m : ι → ℕ) {p : MomentPlane}
    (hp : Surrounds w p) (i : ι) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (fun x => reducedProbability w D m p x i) := by
  have ha : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ι → ℝ) ∞
      (fun x : BaseCurve => fun j => coefficientNorm (D j) (m j) x) :=
    contMDiff_pi_space.mpr (fun j => coefficientNorm_smooth _ _)
  intro x
  exact (selected_contDiffAt (fun j => coefficientNorm_pos (D j) (m j) x) hp i).contMDiffAt.comp x
    ((ha.prodMk_space contMDiff_const).contMDiffAt)

 theorem reducedPrimitive_smooth {w : ι → MomentPlane} (D m : ι → ℕ) (c : ℝ) {p : MomentPlane}
    (hp : Surrounds w p) : SmoothOneFormFamily (fun _ : ℝ => reducedPrimitive w D m c p) := by
  have hs := SmoothOneFormFamily.sum Finset.univ (fun i _ =>
    (weightedFSPrimitive_smooth (D i) (m i) c).spatial_smul (reducedProbability_smooth D m hp i))
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext t x
  simp only [reducedPrimitive,Finset.sum_apply]

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicCoefficientDifferential
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold _root_.ContinuousLinearMap
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 theorem coefficientNorm_chart_hasFDerivAt (D m : ℕ) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    HasFDerivAt (fun z => coefficientNorm D m ((extChartAt 𝓘(ℝ,RealModel) b).symm z))
      ((2:ℝ) • (phaseDot (weightedPhaseInclusion D m ((extChartAt 𝓘(ℝ,RealModel) b).symm y))).comp
        (realPhaseDerivative (fderiv ℂ (weightedChart D m b) (Complex.equivRealProdCLM.symm y)))) y := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,RealModel)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target b).mem_nhds hy)
  have hd := ((weightedPhaseInclusion_smooth D m).contMDiffAt.comp y hi).contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hf := (weighted_phase_chart_derivative D m b hy)
  rw [manifoldMapDifferential,mfderiv_eq_fderiv] at hf
  have h := ((phaseSq_hasFDerivAt _).comp y hd.hasFDerivAt).const_add 1
  rw [hf] at h
  exact h

 theorem weightedFSPrimitive_chart_log (D m : ℕ) (c : ℝ) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    chartOneForm (weightedFSPrimitive D m c) b y (0,1)=
      c/4*(fderiv ℝ (fun z => Real.log (coefficientNorm D m
        ((extChartAt 𝓘(ℝ,RealModel) b).symm z))) y (1,0)) ∧
    chartOneForm (weightedFSPrimitive D m c) b y (1,0)=
      -(c/4)*(fderiv ℝ (fun z => Real.log (coefficientNorm D m
        ((extChartAt 𝓘(ℝ,RealModel) b).symm z))) y (0,1)) := by
  have hl := (coefficientNorm_chart_hasFDerivAt D m b hy).log
    (coefficientNorm_pos D m ((extChartAt 𝓘(ℝ,RealModel) b).symm y)).ne'
  rw [hl.fderiv]
  rw [weightedFSPrimitive,chartOneForm_manifoldPullback (weightedPhaseInclusion_smooth D m) (p := (0,y)) hy]
  change affineFSPrimitive c _
      (manifoldMapDifferential (E := PlanePhase (Option (Fin 3))) (F := RealModel)
        (weightedPhaseInclusion D m ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (0,1))=_ ∧
    affineFSPrimitive c _
      (manifoldMapDifferential (E := PlanePhase (Option (Fin 3))) (F := RealModel)
        (weightedPhaseInclusion D m ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (1,0))=_
  rw [weighted_phase_chart_derivative D m b hy,realPhaseDerivative_I]
  simp only [affineFSPrimitive,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,Function.comp_apply,
    realPhaseDerivative_I,phaseDot_J_right,phaseArea_J_right,coefficientNorm]
  constructor <;> field_simp [(fs_den_pos _).ne'] <;> ring

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Filter Function
open _root_.ContinuousLinearMap
open Hamiltonian

variable {ι E F : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 omit [Nonempty ι] [FiniteDimensional ℝ E] in
 theorem constrained_log_derivative {w : ι → E} {q d h : ι → ℝ} (_hq : ∀ i,0<q i)
    (hs : ∑ i,d i=0) (hm : ∑ i,d i • w i=0) {z : E} {C : ℝ}
    (he : ∀ i,d i/q i=h i+inner ℝ (w i) z-C) :
    (∑ i,d i*h i)=∑ i,(d i)^2/q i := by
  have hi : ∑ i,d i*inner ℝ (w i) z=0 := by
    simpa only [sum_inner,real_inner_smul_left,inner_zero_left] using congrArg (fun v => inner ℝ v z) hm
  have hh (i : ι) : d i*h i=(d i)^2/q i-d i*inner ℝ (w i) z+d i*C := by
    have hh : h i=d i/q i-inner ℝ (w i) z+C := by linarith [he i]
    rw [hh]
    ring
  simp_rw [hh]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,hi,←Finset.sum_mul,hs,zero_mul,sub_zero,add_zero]

 theorem selected_coeff_differentiableAt {w : ι → E} {a : F → ι → ℝ} {x : F}
    (ha : ∀ i,0<a x i) {p : E} (hp : Surrounds w p) (hA : DifferentiableAt ℝ a x) (i : ι) :
    DifferentiableAt ℝ (fun y => selected w (a y) p i) x := by
  have hs : DifferentiableAt ℝ (fun z : (ι → ℝ) × E => selected w z.1 z.2 i) (a x,p) :=
    (selected_contDiffAt ha hp i).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact hs.comp x (hA.prodMk (differentiableAt_const p))

 theorem selected_log_variation {w : ι → E} {a : F → ι → ℝ}
    (ha : ∀ y i,0<a y i) {p : E} (hp : Surrounds w p) {x : F}
    (hA : DifferentiableAt ℝ a x) (v : F) :
    (∑ i,(fderiv ℝ (fun y => selected w (a y) p i) x v)*
      (fderiv ℝ (fun y => Real.log (a y i)) x v))=
      ∑ i,(fderiv ℝ (fun y => selected w (a y) p i) x v)^2/selected w (a x) p i := by
  let q : F → ι → ℝ := fun y i => selected w (a y) p i
  let X : F → E := fun y => inverse w (a y) p
  let P : F → ℝ := fun y => partition w (a y) (X y)
  have hq (i : ι) : DifferentiableAt ℝ (fun y => q y i) x :=
    selected_coeff_differentiableAt (ha x) hp hA i
  have hX : DifferentiableAt ℝ X x := by
    have hi : DifferentiableAt ℝ (fun z : (ι → ℝ) × E => inverse w z.1 z.2) (a x,p) :=
      (inverse_contDiffAt (ha x) hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact hi.comp x (hA.prodMk (differentiableAt_const p))
  have ha' (i : ι) : DifferentiableAt ℝ (fun y => a y i) x :=
    (differentiableAt_pi.mp hA) i
  have hP : DifferentiableAt ℝ P x := DifferentiableAt.fun_sum
    (fun i _ => (ha' i).mul (((differentiableAt_const (w i)).inner ℝ hX).exp))
  have hs : ∑ i,fderiv ℝ (fun y => q y i) x v=0 := by
    have he : (fun y => ∑ i,q y i)=(fun _ : F => (1:ℝ)) := funext (fun y => selected_sum (ha y) p)
    have hd := congrArg (fun f : F → ℝ => fderiv ℝ f x v) he
    simpa only [fderiv_fun_sum (fun i _ => hq i),sum_apply,fderiv_fun_const,Pi.zero_apply,zero_apply] using hd
  have hm : ∑ i,(fderiv ℝ (fun y => q y i) x v) • w i=0 := by
    have he : (fun y => ∑ i,q y i • w i)=(fun _ : F => p) := funext (fun y => selected_mean (ha y) hp)
    have hd := congrArg (fun f : F → E => fderiv ℝ f x v) he
    have hsmi (i : ι) := (hq i).smul_const (w i)
    simpa only [fderiv_fun_sum (fun i _ => hsmi i),fderiv_smul_const (hq _),sum_apply,
      ContinuousLinearMap.smulRight_apply,fderiv_fun_const,Pi.zero_apply,zero_apply] using hd
  apply constrained_log_derivative (fun i => selected_pos (ha x) p i) hs hm
    (z := fderiv ℝ X x v) (C := fderiv ℝ (fun y => Real.log (P y)) x v)
  intro i
  have he : (fun y => Real.log (q y i))=(fun y => Real.log (a y i)+inner ℝ (w i) (X y)-Real.log (P y)) :=
    funext (fun y => gibbs_log (ha y) (X y) i)
  have hd := congrArg (fun f : F → ℝ => fderiv ℝ f x v) he
  have hql := (hq i).hasFDerivAt.log (selected_pos (ha x) p i).ne'
  have hal := (ha' i).log (ha x i).ne'
  have hpl := hP.log (partition_pos (ha x) (X x)).ne'
  have hinner := (innerSL ℝ (w i)).hasFDerivAt.comp x hX.hasFDerivAt
  change HasFDerivAt (fun y => inner ℝ (w i) (X y))
    ((innerSL ℝ (w i)).comp (fderiv ℝ X x)) x at hinner
  have hright := (hal.hasFDerivAt.add hinner).sub hpl.hasFDerivAt
  change HasFDerivAt (fun y => Real.log (a y i)+inner ℝ (w i) (X y)-Real.log (P y)) _ x at hright
  rw [hql.fderiv,hright.fderiv] at hd
  simpa only [smul_apply,smul_eq_mul,add_apply,sub_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,div_eq_inv_mul] using hd

 theorem selected_log_variation_nonneg {w : ι → E} {a : F → ι → ℝ}
    (ha : ∀ y i,0<a y i) {p : E} (hp : Surrounds w p) {x : F}
    (hA : DifferentiableAt ℝ a x) (v : F) :
    0≤∑ i,(fderiv ℝ (fun y => selected w (a y) p i) x v)*
      (fderiv ℝ (fun y => Real.log (a y i)) x v) := by
  rw [selected_log_variation ha hp hA v]
  exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (selected_pos (ha x) p i).le)

 theorem selected_exterior_apply {w : ι → E} {a : F → ι → ℝ}
    (ha : ∀ y i,0<a y i) {p : E} (hp : Surrounds w p) {x : F}
    (hA : DifferentiableAt ℝ a x) {α : ι → F → F →L[ℝ] ℝ}
    (hα : ∀ i,DifferentiableAt ℝ (α i) x) (v u : F) :
    euclideanExteriorOneForm (fun y => ∑ i,selected w (a y) p i • α i y) x v u=
      (∑ i,selected w (a x) p i * euclideanExteriorOneForm (α i) x v u)+
      ∑ i,((fderiv ℝ (fun y => selected w (a y) p i) x v)*α i x u-
        (fderiv ℝ (fun y => selected w (a y) p i) x u)*α i x v) := by
  have hq (i : ι) := selected_coeff_differentiableAt (ha x) hp hA i
  have hs (i : ι) := (hq i).hasFDerivAt.smul (hα i).hasFDerivAt
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply]
  have hs' := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hs i)
  change HasFDerivAt (fun y => ∑ i,selected w (a y) p i • α i y) _ x at hs'
  rw [hs'.fderiv]
  simp only [sum_apply,add_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.smulRight_apply]
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem selected_exterior_positive {w : ι → E} {a : F → ι → ℝ}
    (ha : ∀ y i,0<a y i) {p : E} (hp : Surrounds w p) {x : F}
    (hA : DifferentiableAt ℝ a x) {α : ι → F → F →L[ℝ] ℝ}
    (hα : ∀ i,DifferentiableAt ℝ (α i) x) {c : ℝ} (hc : 0 ≤ c) (v u : F)
    (hu : ∀ i,α i x u=c*(fderiv ℝ (fun y => Real.log (a y i)) x v))
    (hv : ∀ i,α i x v= -c*(fderiv ℝ (fun y => Real.log (a y i)) x u))
    (hpos : ∀ i,0<euclideanExteriorOneForm (α i) x v u) :
    0<euclideanExteriorOneForm (fun y => ∑ i,selected w (a y) p i • α i y) x v u := by
  rw [selected_exterior_apply ha hp hA hα]
  have hsum : 0<∑ i,selected w (a x) p i * euclideanExteriorOneForm (α i) x v u :=
    Finset.sum_pos (fun i _ => mul_pos (selected_pos (ha x) p i) (hpos i)) Finset.univ_nonempty
  have hnon : 0≤∑ i,((fderiv ℝ (fun y => selected w (a y) p i) x v)*α i x u-
      (fderiv ℝ (fun y => selected w (a y) p i) x u)*α i x v) := by
    have he : (∑ i,((fderiv ℝ (fun y => selected w (a y) p i) x v)*α i x u-
        (fderiv ℝ (fun y => selected w (a y) p i) x u)*α i x v))=
        c*((∑ i,(fderiv ℝ (fun y => selected w (a y) p i) x v)*
          (fderiv ℝ (fun y => Real.log (a y i)) x v))+
          ∑ i,(fderiv ℝ (fun y => selected w (a y) p i) x u)*
          (fderiv ℝ (fun y => Real.log (a y i)) x u)) := by
      rw [←Finset.sum_add_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hu i,hv i]
      ring
    rw [he]
    exact mul_nonneg hc (add_nonneg (selected_log_variation_nonneg ha hp hA v)
      (selected_log_variation_nonneg ha hp hA u))
  exact add_pos_of_pos_of_nonneg hsum hnon

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold _root_.ContinuousLinearMap
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open Filter
section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 omit [Nonempty ι] in
 theorem reducedPrimitive_chart (w : ι → MomentPlane) (D m : ι → ℕ) (c : ℝ)
    (p : MomentPlane) (b : BaseCurve) (y : RealModel) :
    chartOneForm (reducedPrimitive w D m c p) b y=
      ∑ i,selected w (fun j => coefficientNorm (D j) (m j)
        ((extChartAt 𝓘(ℝ,RealModel) b).symm y)) p i • chartOneForm (weightedFSPrimitive (D i) (m i) c) b y := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [chartOneForm,reducedPrimitive,reducedProbability,ContinuousLinearMap.comp_apply,sum_apply,smul_apply]

 theorem reducedForm_positive {w : ι → MomentPlane} {D m : ι → ℕ} (hm : ∀ i,m i<D i)
    {c : ℝ} (hc : 0 < c) {p : MomentPlane} (hp : Surrounds w p) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0 < chartTwoForm (reducedForm w D m c p) b y (1,0) (0,1) := by
  have hs := reducedPrimitive_smooth D m c hp
  have hsc (b : BaseCurve) : ContDiffOn ℝ ∞ (chartOneForm (reducedPrimitive w D m c p) b)
      (extChartAt 𝓘(ℝ,RealModel) b).target :=
    fun y hy => (hs.spatial_smooth 0 b hy).contDiffWithinAt
  rw [reducedForm,manifoldExteriorOneForm_chart hsc hy]
  rw [show chartOneForm (reducedPrimitive w D m c p) b=(fun z =>
      ∑ i,selected w (fun j => coefficientNorm (D j) (m j)
        ((extChartAt 𝓘(ℝ,RealModel) b).symm z)) p i • chartOneForm (weightedFSPrimitive (D i) (m i) c) b z)
      from funext (reducedPrimitive_chart w D m c p b)]
  apply selected_exterior_positive (fun z i => coefficientNorm_pos _ _ _) hp
    (differentiableAt_pi.mpr (fun i => (coefficientNorm_chart_hasFDerivAt (D i) (m i) b hy).differentiableAt))
    (fun i => ((weightedFSPrimitive_smooth (D i) (m i) c).spatial_smooth 0 b hy).differentiableAt (by simp))
    (c := c/4) (by positivity) (1,0) (0,1)
    (fun i => (weightedFSPrimitive_chart_log (D i) (m i) c b hy).1)
    (fun i => (weightedFSPrimitive_chart_log (D i) (m i) c b hy).2)
  intro i
  rw [← manifoldExteriorOneForm_chart (fun b y hy =>
    ((weightedFSPrimitive_smooth (D i) (m i) c).spatial_smooth 0 b hy).contDiffWithinAt) hy,
    weightedFSPrimitive_exterior]
  exact weightedFSForm_positive (hm i) hc b hy

end

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem selectedProbability_smooth {w : ι → E} (D m : ι → ℕ) {p : E}
    (hp : Surrounds w p) (i : ι) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (fun x => selectedProbability w D m p x i) := by
  have ha : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ι → ℝ) ∞
      (fun x : BaseCurve => fun j => coefficientNorm (D j) (m j) x) :=
    contMDiff_pi_space.mpr (fun j => coefficientNorm_smooth _ _)
  intro x
  exact (selected_contDiffAt (fun j => coefficientNorm_pos (D j) (m j) x) hp i).contMDiffAt.comp x
    ((ha.prodMk_space contMDiff_const).contMDiffAt)

 theorem selectedPrimitive_smooth {w : ι → E} (D m : ι → ℕ) (c : ℝ) {p : E}
    (hp : Surrounds w p) : SmoothOneFormFamily (fun _ : ℝ => selectedPrimitive w D m c p) := by
  have hs := SmoothOneFormFamily.sum Finset.univ (fun i _ =>
    (weightedFSPrimitive_smooth (D i) (m i) c).spatial_smul (selectedProbability_smooth D m hp i))
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext t x
  simp only [selectedPrimitive,Finset.sum_apply]

 omit [Nonempty ι] [FiniteDimensional ℝ E] in
 theorem selectedPrimitive_chart (w : ι → E) (D m : ι → ℕ) (c : ℝ)
    (p : E) (b : BaseCurve) (y : RealModel) :
    chartOneForm (selectedPrimitive w D m c p) b y=
      ∑ i,selected w (fun j => coefficientNorm (D j) (m j)
        ((extChartAt 𝓘(ℝ,RealModel) b).symm y)) p i • chartOneForm (weightedFSPrimitive (D i) (m i) c) b y := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [chartOneForm,selectedPrimitive,selectedProbability,ContinuousLinearMap.comp_apply,sum_apply,smul_apply]

 theorem selectedForm_positive {w : ι → E} {D m : ι → ℕ} (hm : ∀ i,m i<D i)
    {c : ℝ} (hc : 0 < c) {p : E} (hp : Surrounds w p) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0 < chartTwoForm (selectedForm w D m c p) b y (1,0) (0,1) := by
  have hs := selectedPrimitive_smooth D m c hp
  have hsc (b : BaseCurve) : ContDiffOn ℝ ∞ (chartOneForm (selectedPrimitive w D m c p) b)
      (extChartAt 𝓘(ℝ,RealModel) b).target :=
    fun y hy => (hs.spatial_smooth 0 b hy).contDiffWithinAt
  rw [selectedForm,manifoldExteriorOneForm_chart hsc hy]
  rw [show chartOneForm (selectedPrimitive w D m c p) b=(fun z =>
      ∑ i,selected w (fun j => coefficientNorm (D j) (m j)
        ((extChartAt 𝓘(ℝ,RealModel) b).symm z)) p i • chartOneForm (weightedFSPrimitive (D i) (m i) c) b z)
      from funext (selectedPrimitive_chart w D m c p b)]
  apply selected_exterior_positive (fun z i => coefficientNorm_pos _ _ _) hp
    (differentiableAt_pi.mpr (fun i => (coefficientNorm_chart_hasFDerivAt (D i) (m i) b hy).differentiableAt))
    (fun i => ((weightedFSPrimitive_smooth (D i) (m i) c).spatial_smooth 0 b hy).differentiableAt (by simp))
    (c := c/4) (by positivity) (1,0) (0,1)
    (fun i => (weightedFSPrimitive_chart_log (D i) (m i) c b hy).1)
    (fun i => (weightedFSPrimitive_chart_log (D i) (m i) c b hy).2)
  intro i
  rw [← manifoldExteriorOneForm_chart (fun b y hy =>
    ((weightedFSPrimitive_smooth (D i) (m i) c).spatial_smooth 0 b hy).contDiffWithinAt) hy,
    weightedFSPrimitive_exterior]
  exact weightedFSForm_positive (hm i) hc b hy

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem face_surrounds {k : ι → ℕ × ℕ} (h0 : ∃ i,k i=(0,0))
    {B : ℕ} (hB : ∃ i,k i=(0,B)) {p : ℝ} (hp : 0<p ∧ p<B) :
    Surrounds (faceWeight k) p := by
  obtain ⟨i0,hi0⟩ := h0
  obtain ⟨iB,hiB⟩ := hB
  exact interval_surrounds
    ⟨⟨i0,by simp [hi0]⟩,by simp [faceWeight,hi0]⟩
    ⟨⟨iB,by simp [hiB]⟩,by simp [faceWeight,hiB]⟩ hp

theorem inverse_axis {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : ℝ}
    (hp : Surrounds (faceWeight k) p) :
    nonnegativeInverse k a (0,p)=(0,Real.exp (inverse (faceWeight k) (fun i => a i.val) p)) := by
  obtain ⟨i0,hi0⟩ := h0
  let : Nonempty (Face k) := ⟨⟨i0,by simp [hi0]⟩⟩
  apply nonnegativeInverse_eq_of_moment ha ⟨i0,hi0⟩ he0 he1
    ⟨le_rfl,(Real.exp_pos _).le⟩
  rw [moment_face_exp,inverse_spec (fun i => ha i.val) hp]

theorem probability_axis_active (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : ℝ) (i : Face k) :
    probability k a (0,Real.exp x) i.val=gibbs (faceWeight k) (fun j => a j.val) x i := by
  rw [probability,polynomial_face_exp]
  simp [monomial, i.property,gibbs,faceWeight,← Real.exp_nat_mul,mul_comm]

theorem probability_axis_inactive {k : ι → ℕ × ℕ} (a : ι → ℝ) (t : ℝ) {i : ι}
    (hi : (k i).1≠0) : probability k a (0,t) i=0 := by
  simp [probability,monomial_axis,hi]

theorem selected_axis_active {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : ℝ}
    (hp : Surrounds (faceWeight k) p) (i : Face k) :
    selected k a (0,p) i.val=FiniteMoment.selected (faceWeight k) (fun j => a j.val) p i := by
  unfold selected
  rw [inverse_axis ha h0 he0 he1 hp,probability_axis_active]
  rfl

theorem selected_axis_inactive {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : ℝ}
    (hp : Surrounds (faceWeight k) p) {i : ι} (hi : (k i).1≠0) :
    selected k a (0,p) i=0 := by
  unfold selected
  rw [inverse_axis ha h0 he0 he1 hp]
  exact probability_axis_inactive a _ hi

theorem probability_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) (i : ι) :
    probability (fun j => (k j).swap) a r.swap i=probability k a r i := by
  rw [probability,polynomial_swap,probability]
  simp only [monomial,Prod.fst_swap,Prod.snd_swap,mul_comm]

theorem nonnegativeInverse_swap {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : ∃ r : Plane,(0 ≤ r.1 ∧ 0 ≤ r.2) ∧ moment k a r=p) :
    nonnegativeInverse (fun j => (k j).swap) a p.swap=(nonnegativeInverse k a p).swap := by
  have h0' : ∃ i,(k i).swap=(0,0) := by obtain ⟨i,hi⟩ := h0; exact ⟨i,by simp [hi]⟩
  have he0' : ∃ i,(k i).swap=(1,0) := by obtain ⟨i,hi⟩ := he1; exact ⟨i,by simp [hi]⟩
  have he1' : ∃ i,(k i).swap=(0,1) := by obtain ⟨i,hi⟩ := he0; exact ⟨i,by simp [hi]⟩
  apply nonnegativeInverse_eq_of_moment ha h0' he0' he1'
    ⟨(nonnegativeInverse_nonneg k a p).2,(nonnegativeInverse_nonneg k a p).1⟩
  rw [moment_swap,nonnegativeInverse_spec hp]

theorem selected_swap {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : ∃ r : Plane,(0 ≤ r.1 ∧ 0 ≤ r.2) ∧ moment k a r=p) (i : ι) :
    selected (fun j => (k j).swap) a p.swap i=selected k a p i := by
  unfold selected
  rw [nonnegativeInverse_swap ha h0 he0 he1 hp,probability_swap]

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι]

theorem radialPrimitive_eq_reduced [Nonempty ι] {k : ι → ℕ × ℕ}
    (h0 : ∃ i,k i=(0,0)) (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    (D m : ι → ℕ) (c : ℝ) {p : Radial.Plane}
    (hp : Surrounds (Radial.weight k) (planeVector p.1 p.2)) :
    radialPrimitive k D m c p=reducedPrimitive (Radial.weight k) D m c (planeVector p.1 p.2) := by
  funext x
  apply Finset.sum_congr rfl
  intro i _
  rw [radialProbability,Radial.selected_eq_exponential
    (fun j => coefficientNorm_pos (D j) (m j) x) h0 he0 he1 hp]
  rfl

theorem radialPrimitive_eq_face {k : ι → ℕ × ℕ}
    (h0 : ∃ i,k i=(0,0)) (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    (D m : ι → ℕ) (c : ℝ) {p : ℝ} (hp : Surrounds (Radial.faceWeight k) p) :
    radialPrimitive k D m c (0,p)=selectedPrimitive (Radial.faceWeight k)
      (fun i => D i.val) (fun i => m i.val) c p := by
  classical
  funext x
  change (∑ i,Radial.selected k (fun j => coefficientNorm (D j) (m j) x) (0,p) i •
    weightedFSPrimitive (D i) (m i) c x)=_
  have he : (∑ i,Radial.selected k (fun j => coefficientNorm (D j) (m j) x) (0,p) i •
      weightedFSPrimitive (D i) (m i) c x)=
      ∑ i,if (k i).1=0 then Radial.selected k (fun j => coefficientNorm (D j) (m j) x) (0,p) i •
        weightedFSPrimitive (D i) (m i) c x else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (k i).1=0
    · simp [hi]
    · simp [hi,Radial.selected_axis_inactive (fun j => coefficientNorm_pos (D j) (m j) x) h0 he0 he1 hp hi]
  rw [he,← Finset.sum_filter]
  rw [Finset.sum_subtype _ (p := fun i => (k i).1=0) (by simp)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Radial.selected_axis_active (fun j => coefficientNorm_pos (D j) (m j) x) h0 he0 he1 hp]
  rfl

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_CubicRadialEndSmooth
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

theorem latticeIndex_injective (A B : ℕ) : Injective (latticeIndex (A:=A) (B:=B)) := by
  intro i j h
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst h)
  · exact Fin.ext (congrArg Prod.snd h)

theorem monomial_origin (k : ℕ × ℕ) : monomial k (0,0)=if k=(0,0) then 1 else 0 := by
  classical
  by_cases h0 : k.1=0 <;> by_cases h1 : k.2=0
  · have hk : k=(0,0) := Prod.ext h0 h1
    simp [hk,monomial]
  · have hk : k≠(0,0) := fun h => h1 (congrArg Prod.snd h)
    simp [monomial,h0,h1,hk]
  · have hk : k≠(0,0) := fun h => h0 (congrArg Prod.fst h)
    simp [monomial,h0,h1,hk]
  · have hk : k≠(0,0) := fun h => h0 (congrArg Prod.fst h)
    simp [monomial,h0,h1,hk]

theorem lattice_monomial_origin {A B : ℕ} (i : TrapezoidWeight A B) :
    monomial (latticeIndex i) (0,0)=if i=latticeOrigin A B then 1 else 0 := by
  rw [monomial_origin]
  have he : latticeIndex i=(0,0) ↔ i=latticeOrigin A B :=
    ⟨fun h => latticeIndex_injective A B h,fun h => by simp [h,latticeOrigin,latticeIndex]⟩
  simp only [he]

theorem lattice_polynomial_origin {A B : ℕ} (a : TrapezoidWeight A B → ℝ) :
    polynomial latticeIndex a (0,0)=a (latticeOrigin A B) := by
  classical
  simp [polynomial,lattice_monomial_origin]

theorem lattice_probability_origin {A B : ℕ} {a : TrapezoidWeight A B → ℝ}
    (ha : 0<a (latticeOrigin A B)) (i : TrapezoidWeight A B) :
    probability latticeIndex a (0,0) i=if i=latticeOrigin A B then 1 else 0 := by
  rw [probability,lattice_monomial_origin,lattice_polynomial_origin]
  split_ifs with hi
  · subst i
    simp [ha.ne']
  · simp

theorem lattice_selected_origin {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) (i : TrapezoidWeight A B) :
    selected latticeIndex a (0,0) i=if i=latticeOrigin A B then 1 else 0 := by
  have hi := nonnegativeInverse_of_moment ha (lattice_zero A B)
    (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) (r:=(0,0)) ⟨le_rfl,le_rfl⟩
  rw [moment_origin] at hi
  rw [selected,hi]
  exact lattice_probability_origin (ha _) i

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
section

variable {ι : Type*} [Fintype ι]

theorem radialPrimitive_swap {k : ι → ℕ × ℕ}
    (h0 : ∃ i,k i=(0,0)) (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    (D m : ι → ℕ) (c : ℝ) {p : Radial.Plane}
    (hp : ∀ x : BaseCurve,∃ r : Radial.Plane,(0 ≤ r.1 ∧ 0 ≤ r.2) ∧
      Radial.moment k (fun j => coefficientNorm (D j) (m j) x) r=p) :
    radialPrimitive (fun j => (k j).swap) D m c p.swap=radialPrimitive k D m c p := by
  funext x
  apply Finset.sum_congr rfl
  intro i _
  rw [radialProbability,Radial.selected_swap
    (fun j => coefficientNorm_pos (D j) (m j) x) h0 he0 he1 (hp x)]
  rfl

theorem radialPrimitive_origin {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) (c : ℝ) :
    radialPrimitive Radial.latticeIndex D m c (0,0)=
      weightedFSPrimitive (D (Radial.latticeOrigin A B)) (m (Radial.latticeOrigin A B)) c := by
  classical
  funext x
  simp only [radialPrimitive,radialProbability,Radial.lattice_selected_origin hA hAB
    (fun j => coefficientNorm_pos (D j) (m j) x)]
  simp

theorem radialForm_face_positive {k : ι → ℕ × ℕ}
    (h0 : ∃ i,k i=(0,0)) (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    {D m : ι → ℕ} (hm : ∀ i,m i<D i) {c : ℝ} (hc : 0 < c)
    {p : ℝ} (hp : Surrounds (Radial.faceWeight k) p) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0 < chartTwoForm (radialForm k D m c (0,p)) b y (1,0) (0,1) := by
  obtain ⟨i0,hi0⟩ := h0
  let : Nonempty (Radial.Face k) := ⟨⟨i0,by simp [hi0]⟩⟩
  rw [radialForm,radialPrimitive_eq_face ⟨i0,hi0⟩ he0 he1 D m c hp]
  have hh := selectedForm_positive (D := fun i : Radial.Face k => D i.val)
    (m := fun i : Radial.Face k => m i.val) (fun i => hm i.val) hc hp b hy
  exact hh

theorem radialForm_positive_bp240_oai {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {D m : TrapezoidWeight A B → ℕ} (hm : ∀ i,m i<D i) {c : ℝ} (hc : 0 < c)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0 < chartTwoForm (radialForm Radial.latticeIndex D m c p) b y (1,0) (0,1) := by
  have h0 := Radial.lattice_zero A B
  have he0 := Radial.lattice_unit_fst hA hAB
  have he1 := Radial.lattice_unit_snd hA hAB
  by_cases hp0 : p.1=0
  · by_cases hp1 : p.2=0
    · have he : p=(0,0) := Prod.ext hp0 hp1
      rw [he,radialForm,radialPrimitive_origin hA hAB,weightedFSPrimitive_exterior]
      exact weightedFSForm_positive (hm _) hc b hy
    · have hpos : 0<p.2 := lt_of_le_of_ne hp.2.2.1 (Ne.symm hp1)
      have he : p=(0,p.2) := Prod.ext hp0 rfl
      rw [he]
      apply radialForm_face_positive h0 he0 he1 hm hc _ b hy
      exact Radial.face_surrounds h0 (Radial.lattice_end_snd A B)
        ⟨hpos,by simpa [hp0] using hp.2.2.2⟩
  · have hpos : 0<p.1 := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    by_cases hp1 : p.2=0
    · have h0' : ∃ i : TrapezoidWeight A B,(Radial.latticeIndex i).swap=(0,0) := by
        obtain ⟨i,hi⟩ := h0; exact ⟨i,by simp [hi]⟩
      have he0' : ∃ i : TrapezoidWeight A B,(Radial.latticeIndex i).swap=(1,0) := by
        obtain ⟨i,hi⟩ := he1; exact ⟨i,by simp [hi]⟩
      have he1' : ∃ i : TrapezoidWeight A B,(Radial.latticeIndex i).swap=(0,1) := by
        obtain ⟨i,hi⟩ := he0; exact ⟨i,by simp [hi]⟩
      have hend : ∃ i : TrapezoidWeight A B,(Radial.latticeIndex i).swap=(0,A) := by
        obtain ⟨i,hi⟩ := Radial.lattice_end_fst hAB; exact ⟨i,by simp [hi]⟩
      rw [radialForm,←radialPrimitive_swap h0 he0 he1 D m c
        (fun x => Radial.trapezoid_radial_surjective hAB
          (fun j => coefficientNorm_pos (D j) (m j) x) hp)]
      have he : p.swap=(0,p.1) := Prod.ext hp1 rfl
      rw [he]
      exact radialForm_face_positive h0' he0' he1' hm hc
        (Radial.face_surrounds h0' hend ⟨hpos,hp.2.1⟩) b hy
    · let : Nonempty (TrapezoidWeight A B) := ⟨Radial.latticeOrigin A B⟩
      have hs : Surrounds (Radial.weight Radial.latticeIndex) (planeVector p.1 p.2) :=
        trapezoidWeight_surrounds hAB ⟨hpos,hp.2.1,lt_of_le_of_ne hp.2.2.1 (Ne.symm hp1),hp.2.2.2⟩
      rw [radialForm,radialPrimitive_eq_reduced h0 he0 he1 D m c hs]
      exact reducedForm_positive hm hc hs b hy

end

end PackingSufficiencySupport.CubicModel
end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.CubicModel.radialForm_positive_bp240_oai := @OAI.PackingSufficiencySupport.CubicModel.radialForm_positive_bp240_oai
