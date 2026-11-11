-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.DiagonalQuadrics.normalHorizontalPrimitive_area_limit_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:50:59.527914+00:00
-- url     : https://prove2.me/submissions/a9942e47-cf84-492d-aa15-e22e746aeb8e

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_curveEndCutoff_partition_mass_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCorrection
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.coordinateForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Metric
open MeasureTheory Function
open scoped Classical

theorem bilinear_skew_plane (B : Plane →L[ℝ] Plane →L[ℝ] ℝ) (u v : Plane) :
    B u v - B v u = (B (1,0) (0,1)-B (0,1) (1,0))*planarArea u v := by
  have hu : u = u.1 • ((1:ℝ),(0:ℝ)) + u.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  conv_lhs => rw [hu,hv]
  simp only [map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,planarArea_apply]
  ring

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_BackgroundDensity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem euclideanExteriorOneForm_smooth {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) : ContDiff ℝ ∞ (euclideanExteriorOneForm α) := by
  have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ α x) := hα.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hflip : ContDiff ℝ ∞ (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ)
  have hf : ContDiff ℝ ∞ (fun x => (fderiv ℝ α x).flip) := hflip.comp hd
  exact hd.sub hf



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_DiagonalQuadric
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function

variable {m : ℕ}

 theorem infinityRegion_contains_ball (a : Fin m → ℂ) :
    ∃ r : ℝ,0 < r ∧ Metric.ball 0 r⊆infinityRegion a :=
  Metric.isOpen_iff.mp (infinityRegion_open a) 0 (zero_mem_infinityRegion a)

end PackingSufficiencySupport.DiagonalQuadrics
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

theorem affineFSForm_smooth (a : ℝ) : ContDiff ℝ ∞ (affineFSForm a : PlanePhase ι → _) := by
  rw [affineFSForm_eq_exterior]
  exact euclideanExteriorOneForm_smooth (affineFSPrimitive_smooth a)

theorem affineFSForm_skew (a : ℝ) (z v w : PlanePhase ι) :
    affineFSForm a z v w = -affineFSForm a z w v := by
  rw [affineFSForm_apply,affineFSForm_apply,phaseArea_skew v w]
  ring

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
open scoped ContDiff Topology
attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_bilinear_flip {P A B C : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : P → A →L[ℝ] B →L[ℝ] C} {p : P} (h : ContDiffAt ℝ ∞ f p) :
    ContDiffAt ℝ ∞ (fun q => (f q).flip) p := by
  have hflip : ContDiff ℝ ∞ (fun L : A →L[ℝ] B →L[ℝ] C => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := A →L[ℝ] B →L[ℝ] C)
      (F := B →L[ℝ] A →L[ℝ] C) (ContinuousLinearMap.flipₗᵢ ℝ A B C)
  exact hflip.contDiffAt.comp p h


end

section
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem staticPullbackOneForm_smoothAt {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (staticPullbackOneForm α g) x :=
  (ha.comp x hg).clm_comp (hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartTwoForm_apply_chart {Ω : ManifoldTwoForm E M} {c z : M}
    (hz : z ∈ (extChartAt 𝓘(ℝ,E) c).source) (v w : TangentSpace 𝓘(ℝ,E) z) :
    chartTwoForm Ω c (extChartAt 𝓘(ℝ,E) c z)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) z v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) z w) = Ω z v w := by
  change E at v w
  change chartTwoForm Ω c (extChartAt 𝓘(ℝ,E) c z)
    (chartDifferential c z v) (chartDifferential c z w) = Ω z v w
  simp only [chartTwoForm,(extChartAt 𝓘(ℝ,E) c).left_inv hz,
    ContinuousLinearMap.bilinearComp_apply]
  have hA : (chartDifferential (E := E) c z).IsInvertible := by
    convert! (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hz) using 1
    all_goals try with_reducible_and_instances rfl
  rw [hA.inverse_apply_eq.mpr rfl,hA.inverse_apply_eq.mpr rfl]



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ParametricMoser
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_J_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_J_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_single_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_single_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_J_J _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_J_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_J_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_fderiv _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory

theorem planar_det (A : Plane →L[ℝ] Plane) :
    A.det = planarArea (A (1,0)) (A (0,1)) := by
  let b : Module.Basis (Fin 2) ℝ Plane :=
    Module.Basis.ofEquivFun (LinearEquiv.finTwoArrow ℝ ℝ).symm
  change LinearMap.det A.toLinearMap = _
  rw [← LinearMap.det_toMatrix b,Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,b,Module.Basis.coe_ofEquivFun,
    LinearEquiv.finTwoArrow,planarArea_apply]
  ring

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_SpatialOneForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm_add _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul
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

theorem euclideanPullbackTwoForm_chart {Ω : ℝ → ManifoldTwoForm E M} {g : F → M}
    {p : ℝ × F} {c : M} (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
    (hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    euclideanPullbackTwoForm Ω g p =
      (chartTwoForm (Ω p.1) c (extChartAt 𝓘(ℝ,E) c (g p.2))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2)
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
  ext v w
  exact (chartTwoForm_apply_chart hc _ _).symm

theorem euclideanPullbackTwoForm_contDiffAt
    {Ω : ℝ → ManifoldTwoForm E M} {g : F → M} {p : ℝ × F}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) :
    ContDiffAt ℝ ∞ (euclideanPullbackTwoForm Ω g) p := by
  let c := g p.2
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2 := hch.contDiffAt
  have hcoord : ContDiffAt ℝ ∞ (fun q : ℝ × F => (q.1,extChartAt 𝓘(ℝ,E) c (g q.2))) p :=
    contDiffAt_fst.prodMk (hs.comp p contDiffAt_snd)
  have hform := ((hΩ c).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) c).map_source hc⟩)).comp p hcoord
  have hder := (hs.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp p contDiffAt_snd
  have hsm := smooth_bilinear_flip ((smooth_bilinear_flip (hform.clm_comp hder)).clm_comp hder)
  apply hsm.congr_of_eventuallyEq
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
    continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
  exact euclideanPullbackTwoForm_chart (hq.mdifferentiableAt (by simp)) hqc


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
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_J_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_J_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_single_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_single_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_J_J _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_J_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_J_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_fderiv _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

namespace SurfaceCoordinateBox

theorem isCompact_compactCarrier (B : SurfaceCoordinateBox M) : IsCompact B.compactCarrier := by
  exact (isCompact_closedBall B.point B.radius).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) B.center).mono B.closed_subset)

theorem carrier_subset_compactCarrier (B : SurfaceCoordinateBox M) :
    B.carrier ⊆ B.compactCarrier := by
  intro x hx
  exact ⟨extChartAt 𝓘(ℝ,Plane) B.center x,Metric.ball_subset_closedBall hx.2,
    (extChartAt 𝓘(ℝ,Plane) B.center).left_inv hx.1⟩

end SurfaceCoordinateBox

end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

theorem planar_skew_coefficient (B : Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = -B v u) (u v : Plane) :
    B u v = B (1,0) (0,1)*planarArea u v := by
  have he := bilinear_skew_plane B u v
  rw [hB v u,hB (0,1) (1,0)] at he
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem chartTwoForm_change {Ω : ManifoldTwoForm Plane M} {c b : M} {y : Plane}
    (hy : y ∈ (extChartAt 𝓘(ℝ,Plane) b).target)
    (hc : (extChartAt 𝓘(ℝ,Plane) b).symm y ∈ (extChartAt 𝓘(ℝ,Plane) c).source) :
    chartTwoForm Ω b y =
      (chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c ((extChartAt 𝓘(ℝ,Plane) b).symm y))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y)
        (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y) := by
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have he := euclideanPullbackTwoForm_chart (Ω := fun _ => Ω) (p := (0,y)) hi hc
  simpa only [euclideanPullbackTwoForm,chartTwoForm,chartDifferential_inverse hy] using he

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem chartTwoForm_skew {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) (c : M) (y u v : Plane) :
    chartTwoForm Ω c y u v = -chartTwoForm Ω c y v u := by
  exact hΩ _ _ _

theorem chartTwoForm_density_change {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) {c b : M} {y : Plane}
    (hy : y ∈ (extChartAt 𝓘(ℝ,Plane) b).target)
    (hc : (extChartAt 𝓘(ℝ,Plane) b).symm y ∈ (extChartAt 𝓘(ℝ,Plane) c).source) :
    chartTwoForm Ω b y (1,0) (0,1) =
      (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det *
        chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c ((extChartAt 𝓘(ℝ,Plane) b).symm y)) (1,0) (0,1) := by
  rw [chartTwoForm_change hy hc,ContinuousLinearMap.bilinearComp_apply,
    planar_skew_coefficient _ (chartTwoForm_skew hΩ _ _), ← planar_det,mul_comm]

theorem chart_area_integral_change {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) {c b : M} {K : Set M}
    (hK : IsCompact K)
    (hKb : K ⊆ (extChartAt 𝓘(ℝ,Plane) b).source)
    (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hpos : ∀ y ∈ extChartAt 𝓘(ℝ,Plane) b '' K,
      0 < (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det) :
    (∫ y in extChartAt 𝓘(ℝ,Plane) b '' K, chartTwoForm Ω b y (1,0) (0,1)) =
      ∫ y in extChartAt 𝓘(ℝ,Plane) c '' K, chartTwoForm Ω c y (1,0) (0,1) := by
  let g : Plane → Plane := extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm
  have hyb {y : Plane} (hy : y ∈ extChartAt 𝓘(ℝ,Plane) b '' K) :
      y ∈ (extChartAt 𝓘(ℝ,Plane) b).target := by
    obtain ⟨x,hx,rfl⟩ := hy
    exact (extChartAt 𝓘(ℝ,Plane) b).map_source (hKb hx)
  have hyK {y : Plane} (hy : y ∈ extChartAt 𝓘(ℝ,Plane) b '' K) :
      (extChartAt 𝓘(ℝ,Plane) b).symm y ∈ K := by
    obtain ⟨x,hx,rfl⟩ := hy
    simpa only [(extChartAt 𝓘(ℝ,Plane) b).left_inv (hKb hx)] using hx
  have hgs : ∀ y ∈ extChartAt 𝓘(ℝ,Plane) b '' K, ContDiffAt ℝ ∞ g y := by
    intro y hy
    have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) b).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) b).mem_nhds (hyb hy))
    have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,Plane)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hKc (hyK hy))
    exact (ho.comp y hi).contDiffAt
  have hgi : InjOn g (extChartAt 𝓘(ℝ,Plane) b '' K) := by
    intro y hy z hz he
    apply (extChartAt 𝓘(ℝ,Plane) b).symm.injOn (hyb hy) (hyb hz)
    exact (extChartAt 𝓘(ℝ,Plane) c).injOn (hKc (hyK hy)) (hKc (hyK hz)) he
  have him : g '' (extChartAt 𝓘(ℝ,Plane) b '' K) = extChartAt 𝓘(ℝ,Plane) c '' K := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(extChartAt 𝓘(ℝ,Plane) b).symm z,hyK hz,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      refine ⟨extChartAt 𝓘(ℝ,Plane) b x,⟨x,hx,rfl⟩,?_⟩
      exact congrArg (extChartAt 𝓘(ℝ,Plane) c) ((extChartAt 𝓘(ℝ,Plane) b).left_inv (hKb hx))
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume
    (hK.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) b).mono hKb)).measurableSet
    (f' := fderiv ℝ g)
    (fun y hy => ((hgs y hy).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
    hgi (fun y => chartTwoForm Ω c y (1,0) (0,1))
  rw [him] at hi
  rw [hi]
  apply setIntegral_congr_fun
    (hK.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) b).mono hKb)).measurableSet
  intro y hy
  dsimp only
  change chartTwoForm Ω b y (1,0) (0,1) =
    |(fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det| •
      chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c ((extChartAt 𝓘(ℝ,Plane) b).symm y)) (1,0) (0,1)
  rw [chartTwoForm_density_change hΩ (hyb hy) (hKc (hyK hy)),abs_of_pos (hpos y hy)]
  rfl


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem chartMass_eq_setIntegral {c : M} {Ω : ManifoldTwoForm Plane M} {K : Set M}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ x, x ∉ K → Ω x=0) :
    chartMass c Ω = ∫ y in extChartAt 𝓘(ℝ,Plane) c '' K, chartTwoForm Ω c y (1,0) (0,1) := by
  unfold chartMass
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy => extendedChartCoefficient_zero (fun _ x hx => hz x hx) (0:ℝ) hy)]
  apply setIntegral_congr_fun
    (hK.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) c).mono hKc)).measurableSet
  rintro y ⟨x,hx,rfl⟩
  exact ite_eq_left ((extChartAt 𝓘(ℝ,Plane) c).map_source (hKc hx))

variable [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem chartMass_change {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) {c b : M} {K : Set M}
    (hK : IsCompact K) (hKb : K ⊆ (extChartAt 𝓘(ℝ,Plane) b).source)
    (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ x, x ∉ K → Ω x=0)
    (hpos : ∀ y ∈ extChartAt 𝓘(ℝ,Plane) b '' K,
      0 < (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det) :
    chartMass b Ω = chartMass c Ω := by
  rw [chartMass_eq_setIntegral hK hKb hz,chartMass_eq_setIntegral hK hKc hz]
  exact chart_area_integral_change hΩ hK hKb hKc hpos


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricCurveManifold
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open Function
open scoped Topology
open Set Filter

theorem complex_real_conjugate_det (L : ℂ →L[ℂ] ℂ) :
    (Complex.equivRealProdCLM.toContinuousLinearMap.comp
      ((L.restrictScalars ℝ).comp Complex.equivRealProdCLM.symm.toContinuousLinearMap)).det=
      Complex.normSq L.det := by
  change LinearMap.det
    (Complex.equivRealProdCLM.toLinearEquiv.toLinearMap.comp
      ((L.toLinearMap.restrictScalars ℝ).comp Complex.equivRealProdCLM.symm.toLinearEquiv.toLinearMap))=_
  have h := LinearMap.det_conj (L.toLinearMap.restrictScalars ℝ)
    Complex.equivRealProdCLM.toLinearEquiv
  exact h.trans (by rw [LinearMap.det_restrictScalars,Algebra.norm_complex_eq]; rfl)

theorem holomorphic_plane_det_nonneg {f : ℂ → ℂ} {y : ℝ × ℝ}
    (hf : DifferentiableAt ℂ f (Complex.equivRealProdCLM.symm y)) :
    0≤(fderiv ℝ (Complex.equivRealProdCLM ∘ f ∘ Complex.equivRealProdCLM.symm) y).det := by
  have hd := Complex.equivRealProdCLM.hasFDerivAt.comp y
    ((hf.hasFDerivAt.restrictScalars ℝ).comp y Complex.equivRealProdCLM.symm.hasFDerivAt)
  rw [hd.fderiv,complex_real_conjugate_det]
  exact Complex.normSq_nonneg _

theorem partialHomeomorph_fderiv_det_ne_zero
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) {x : ℝ × ℝ} (hx : x∈e.source)
    (hf : DifferentiableAt ℝ e x) (hg : DifferentiableAt ℝ e.symm (e x)) :
    (fderiv ℝ e x).det≠0 := by
  have hd := hg.hasFDerivAt.comp x hf.hasFDerivAt
  have heq : e.symm ∘ e =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hi : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)=ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    have hh := hd.congr_of_eventuallyEq heq.symm
    simpa only [fderiv_id] using hh.fderiv.symm
  have hdet := congrArg ContinuousLinearMap.det hi
  change LinearMap.det ((fderiv ℝ e.symm (e x)).toLinearMap.comp
    (fderiv ℝ e x).toLinearMap)=LinearMap.det (LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) at hdet
  rw [LinearMap.det_comp,LinearMap.det_id] at hdet
  exact right_ne_zero_of_mul_eq_one hdet

theorem holomorphic_partialHomeomorph_orientation
    (e : OpenPartialHomeomorph ℂ ℂ) {y : ℝ × ℝ}
    (hy : Complex.equivRealProdCLM.symm y∈e.source)
    (hf : DifferentiableAt ℂ e (Complex.equivRealProdCLM.symm y))
    (hg : DifferentiableAt ℂ e.symm (e (Complex.equivRealProdCLM.symm y))) :
    0<(fderiv ℝ (Complex.equivRealProdCLM ∘ e ∘ Complex.equivRealProdCLM.symm) y).det := by
  let d := (Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph.trans e).trans
    Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph
  have hd : DifferentiableAt ℝ d y :=
    Complex.equivRealProdCLM.differentiableAt.comp y
      ((hf.restrictScalars ℝ).comp y Complex.equivRealProdCLM.symm.differentiableAt)
  have hs : DifferentiableAt ℝ d.symm (d y) := by
    have h0 := Complex.equivRealProdCLM.differentiableAt.comp (d y)
      ((hg.restrictScalars ℝ).comp (d y) Complex.equivRealProdCLM.symm.differentiableAt)
    convert h0 using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hn := partialHomeomorph_fderiv_det_ne_zero d (by exact ⟨⟨mem_univ _,hy⟩,mem_univ _⟩) hd hs
  exact lt_of_le_of_ne (holomorphic_plane_det_nonneg hf) (Ne.symm hn)

end PackingSufficiencySupport
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricOrientation
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContDiff Manifold Topology
open Set Function Manifold
namespace PackingSufficiencySupport.DiagonalQuadrics
variable {m : ℕ} (a : Fin m → ℂ) [ha : Fact (Injective a)] [ha0 : Fact (∀ j,a j≠0)]

theorem real_transition_positive (b c : locus a) {y : RealModel}
    (hy : y∈((realChart a b).symm.trans (realChart a c)).source) :
    0<(fderiv ℝ ((realChart a b).symm.trans (realChart a c)) y).det := by
  let e := ((normalChartAt a b).sliceChart b).symm.trans ((normalChartAt a c).sliceChart c)
  have hye : Complex.equivRealProdCLM.symm y∈e.source := ⟨hy.1.2,hy.2.1⟩
  have hf := ((normalChartAt a b).transition_smooth b (normalChartAt a c) c).contDiffAt
    (e.open_source.mem_nhds hye)
  have hg := ((normalChartAt a c).transition_smooth c (normalChartAt a b) b).contDiffAt
    (e.symm.open_source.mem_nhds (e.map_source hye))
  exact holomorphic_partialHomeomorph_orientation e hye
    (hf.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hg.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

theorem positivePlaneTransitions : Hamiltonian.PositivePlaneTransitions (locus a) := by
  intro b c y hy hc
  have hbchart : chartAt Hamiltonian.Plane b=realChart a b := rfl
  have hcchart : chartAt Hamiltonian.Plane c=realChart a c := rfl
  have hb : y∈(realChart a b).target := by simpa only [mfld_simps,hbchart] using hy
  have hc' : (realChart a b).symm y∈(realChart a c).source := by simpa only [mfld_simps,hbchart,hcchart] using hc
  have h := real_transition_positive a b c ⟨hb,hc'⟩
  simpa only [mfld_simps,hbchart,hcchart] using h

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricInfinityDiffeomorph
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
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

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter Bornology

theorem inverseComplementCutoff_one_near_zero {f : ℂ → ℝ} (hc : HasCompactSupport f) :
    inverseComplementCutoff f=ᶠ[𝓝 0] fun _ => 1 := by
  have he : f=ᶠ[cobounded ℂ] 0 := by
    simpa only [Metric.cobounded_eq_cocompact,coclosedCompact_eq_cocompact] using hasCompactSupport_iff_eventuallyEq.mp hc
  have hp := he.comp_tendsto (tendsto_inv₀_nhdsNE_zero (α := ℂ))
  filter_upwards [eventually_nhdsWithin_iff.mp hp] with z hz
  by_cases h : z=0
  · simp only [inverseComplementCutoff,h,↓reduceIte]
  · have hzero : f z⁻¹=0 := hz h
    simp only [inverseComplementCutoff,h,↓reduceIte,hzero,sub_zero]

theorem inverseComplementCutoff_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (inverseComplementCutoff f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z=0
  · subst z
    exact contDiffAt_const.congr_of_eventuallyEq (inverseComplementCutoff_one_near_zero hc)
  · have he : inverseComplementCutoff f=ᶠ[𝓝 z] fun w => 1-f w⁻¹ := by
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with w hw
      exact ite_eq_right (show w≠0 from hw)
    exact (contDiffAt_const.sub (hf.contDiffAt.comp z (contDiffAt_inv ℝ hz))).congr_of_eventuallyEq he

theorem inverseComplementCutoff_range {f : ℂ → ℝ} (hf : ∀ z,f z∈Icc (0:ℝ) 1) (z : ℂ) :
    inverseComplementCutoff f z∈Icc (0:ℝ) 1 := by
  by_cases hz : z=0
  · simp [inverseComplementCutoff,hz]
  · simp only [inverseComplementCutoff,hz,↓reduceIte,mem_Icc]
    have h := hf z⁻¹
    constructor <;> linarith [h.1,h.2]

theorem HasCompactSupport.comp_complex_normSq {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z : ℂ => g (Complex.normSq z)) := by
  obtain ⟨B,hB,hbound⟩ := hg.isBounded.exists_pos_norm_le
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (B+1))
  intro z hz
  by_contra hgz
  have hb := hbound (Complex.normSq z) (subset_tsupport g hgz)
  rw [Real.norm_eq_abs,abs_of_nonneg (Complex.normSq_nonneg z),Complex.normSq_eq_norm_sq] at hb
  apply hz
  rw [Metric.mem_closedBall,dist_zero_right]
  nlinarith [norm_nonneg z,sq_nonneg (‖z‖-1)]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem curveProjection_smooth :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℂ) ∞ (curveProjection a) :=
  (ContinuousLinearMap.fst ℝ ℂ (Fin m → ℂ)).contDiff.contMDiff.comp
    (real_inclusion_contMDiff a)

theorem curveEndCutoff_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (curveEndCutoff a g) :=
  (inverseComplementCutoff_smooth (hg.comp complex_normSq_smooth)
    (HasCompactSupport.comp_complex_normSq hc)).contMDiff.comp (curveProjection_smooth a)

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem curveEndCutoff_range {g : ℝ → ℝ} (hg : ∀ t,g t∈Icc (0:ℝ) 1) (x : locus a) :
    curveEndCutoff a g x∈Icc (0:ℝ) 1 :=
  inverseComplementCutoff_range (fun z => hg (Complex.normSq z)) _

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldMapDifferential
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
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

theorem manifoldPullbackTwoForm_smooth {Ω : ℝ → ManifoldTwoForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (b : N) :
    ContDiffOn ℝ ∞ (fun q : ℝ × F => chartTwoForm (manifoldPullbackTwoForm Ω e q.1) b q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,F) b).target) := by
  intro p hp
  have hg := he.contMDiffAt.comp p.2 ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2))
  apply ((euclideanPullbackTwoForm_contDiffAt hΩ hg).congr_of_eventuallyEq _).contDiffWithinAt
  have hh := continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2)
  filter_upwards [hh] with q hq
  exact chartTwoForm_manifoldPullback he hq

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vector_chartTwoForm (Ω : E → E →L[ℝ] E →L[ℝ] ℝ) (c y : E) :
    chartTwoForm Ω c y=Ω y := by
  ext v w
  simp only [chartTwoForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,id_eq,
    ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.id_apply]

theorem vector_twoForm_smooth {Ω : E → E →L[ℝ] E →L[ℝ] ℝ} (hΩ : ContDiff ℝ ∞ Ω) :
    SmoothTwoForm Ω := by
  intro c
  rw [show chartTwoForm Ω c=Ω from funext (vector_chartTwoForm Ω c)]
  exact hΩ.contDiffOn

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem phaseInclusion_smooth :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin m))) ∞ (phaseInclusion a) :=
  (affinePhase m).contDiff.contMDiff.comp (real_inclusion_contMDiff a)

theorem curveFSForm_smooth (c : ℝ) : SmoothTwoForm (curveFSForm a c) := by
  have hΩ : SmoothTwoForm (affineFSForm c : PlanePhase (Option (Fin m)) → _) :=
    vector_twoForm_smooth (affineFSForm_smooth c)
  have hΩf : SmoothTwoFormFamily (fun _ : ℝ =>
      (affineFSForm c : PlanePhase (Option (Fin m)) → _)) := SmoothTwoFormFamily.const hΩ
  have hs : SmoothTwoFormFamily (fun t : ℝ =>
      manifoldPullbackTwoForm (fun _ => (affineFSForm c : PlanePhase (Option (Fin m)) → _))
        (phaseInclusion a) t) :=
    manifoldPullbackTwoForm_smooth (Ω := fun _ =>
      (affineFSForm c : PlanePhase (Option (Fin m)) → _)) (phaseInclusion_smooth a) hΩf
  exact hs.eval 0

theorem curveFSForm_skew (c : ℝ) (x : locus a) (v w : RealModel) :
    curveFSForm a c x v w= -curveFSForm a c x w v :=
  affineFSForm_skew c _ _ _

theorem phase_chart_function (b : locus a) :
    (phaseInclusion a ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm)=
      affinePhase m ∘ (normalChartAt a b).inclusionChart b ∘ Complex.equivRealProdCLM.symm := by
  funext y
  have he : chartAt RealModel b=realChart a b := rfl
  simp only [mfld_simps,he,realChart,Function.comp_apply,phaseInclusion,
    NormalChart.inclusionChart]
  rfl

theorem realChart_complex_target (b : locus a) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    Complex.equivRealProdCLM.symm y∈((normalChartAt a b).sliceChart b).target := by
  have he : chartAt RealModel b=realChart a b := rfl
  simp only [mfld_simps,he,realChart] at hy
  exact hy

theorem phase_chart_derivative (b : locus a) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    manifoldMapDifferential (E := PlanePhase (Option (Fin m))) (F := RealModel)
      (phaseInclusion a ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y=
    realPhaseDerivative (fderiv ℂ ((normalChartAt a b).inclusionChart b)
      (Complex.equivRealProdCLM.symm y)) := by
  change mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin m))) _ y=_
  rw [mfderiv_eq_fderiv,phase_chart_function]
  have hdf := (((normalChartAt a b).inclusionChart_smooth b).contDiffAt
    (((normalChartAt a b).sliceChart b).open_target.mem_nhds
      (realChart_complex_target a b hy))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ((affinePhase m).hasFDerivAt.comp y
    ((hdf.hasFDerivAt.restrictScalars ℝ).comp y Complex.equivRealProdCLM.symm.hasFDerivAt)).fderiv

theorem curveFSForm_positive {c : ℝ} (hc : 0 < c) (b : locus a) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0 < chartTwoForm (curveFSForm a c) b y (1,0) (0,1) := by
  rw [curveFSForm,chartTwoForm_manifoldPullback (phaseInclusion_smooth a) (p := (0,y)) hy]
  change 0<affineFSForm c _
    (manifoldMapDifferential (E := PlanePhase (Option (Fin m))) (F := RealModel)
      (phaseInclusion a ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (1,0))
    (manifoldMapDifferential (E := PlanePhase (Option (Fin m))) (F := RealModel)
      (phaseInclusion a ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (0,1))
  rw [phase_chart_derivative a b hy]
  apply affineFSForm_holomorphic_positive hc
  exact (normalChartAt a b).inclusionChart_derivative_one_ne b (realChart_complex_target a b hy)

end PackingSufficiencySupport.DiagonalQuadrics
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

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function
open Hamiltonian
open scoped BigOperators ComplexConjugate
section

variable {m : ℕ} (a : Fin m → ℂ) (ε : Fin m → Bool)

theorem infinityRegularPoint_contDiffAt {s : ℂ} (hs : s∈infinityRegion a) :
    ContDiffAt ℂ ∞ (infinityRegularPoint a ε) s :=
  contDiffAt_id.prodMk (infinityRoot_contDiffAt a ε hs)

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_J_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_J_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_single_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_single_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_J_J _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_J_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_J_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_fderiv _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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

theorem planarCurl_contDiff {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (planarCurl β) :=
  (((hβ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).clm_apply contDiff_const).sub
    (((hβ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).clm_apply contDiff_const)

theorem planarCurl_compact {β : Plane → Plane →L[ℝ] ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (planarCurl β) := by
  exact ((hβ.fderiv_apply (𝕜 := ℝ) (1,0)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (0,1)) rfl).sub
    ((hβ.fderiv_apply (𝕜 := ℝ) (0,1)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (1,0)) rfl)

theorem shrinkingCutoff_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ContDiff ℝ ∞ (shrinkingCutoff g n) := hg.comp (contDiff_const.mul contDiff_id)

theorem shrinkingCutoff_compact {g : ℝ → ℝ} (hg : HasCompactSupport g) (n : ℕ) :
    HasCompactSupport (shrinkingCutoff g n) := by
  have hh := hg.comp_homeomorph (Homeomorph.smulOfNeZero (α := ℝ) ((n:ℝ)+1) (by positivity))
  change HasCompactSupport (fun t : ℝ => g (((n:ℝ)+1)*t))
  simpa only [Function.comp_def,Homeomorph.smulOfNeZero_apply,smul_eq_mul] using hh

theorem shrinkingCutoff_tsupport {g : ℝ → ℝ} {R : ℝ}
    (hR : 0≤R) (h0 : tsupport g⊆Iic R) (n : ℕ) :
    tsupport (shrinkingCutoff g n)⊆Iic R := by
  apply closure_minimal _ isClosed_Iic
  intro t ht
  by_contra hn
  have htR : R<t := lt_of_not_ge hn
  have hnt : R<((n:ℝ)+1)*t := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  change g (((n:ℝ)+1)*t)≠0 at ht
  exact ht (image_eq_zero_of_notMem_tsupport (f := g) (fun hx => not_le_of_gt hnt (h0 hx)))

theorem shrinkingCutoff_eventually_zero {g : ℝ → ℝ} (hc : HasCompactSupport g)
    {t : ℝ} (ht : 0<t) : ∀ᶠ n in atTop,shrinkingCutoff g n t=0 := by
  obtain ⟨B,_hB,hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hz : ∀ᶠ s : ℝ in atTop,g s=0 := by
    filter_upwards [eventually_gt_atTop B] with s hs
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hb := hbound s h
    have hsn := le_abs_self s
    rw [Real.norm_eq_abs] at hb
    linarith
  have hseq : Tendsto (fun n : ℕ => ((n:ℝ)+1)*t) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_mul_const ht
  exact hseq.eventually hz

theorem radiusSq_pos {z : Plane} (hz : z≠0) : 0 < radiusSq z := by
  have hn := radiusSq_nonneg z
  by_contra hh
  have he : radiusSq z=0 := le_antisymm (le_of_not_gt hh) hn
  apply hz
  apply Prod.ext <;> change _=0 <;> dsimp only [radiusSq] at he <;>
    nlinarith [sq_nonneg z.1,sq_nonneg z.2]

theorem tendsto_shrinking_regular_residue {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hbound : ∀ t,g t∈Icc (0:ℝ) 1)
    {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β) :
    Tendsto (fun n => ∫ z : Plane,shrinkingCutoff g n (radiusSq z)*planarCurl β z)
      atTop (𝓝 0) := by
  have hi : Integrable (planarCurl β) := (planarCurl_contDiff hβ).continuous.integrable_of_hasCompactSupport (planarCurl_compact hβc)
  have h := tendsto_integral_of_dominated_convergence (fun z => ‖planarCurl β z‖)
    (f := fun _ : Plane => (0:ℝ))
    (fun n => (((shrinkingCutoff_smooth hg n).comp radiusSq_smooth).mul
      (planarCurl_contDiff hβ)).continuous.aestronglyMeasurable) hi.norm
    (fun n => Filter.Eventually.of_forall (fun z => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by
        rw [Real.norm_eq_abs]
        change |g (((n:ℝ)+1)*radiusSq z)|≤1
        rw [abs_of_nonneg (hbound _).1]
        exact (hbound _).2))) (by
      have hne : ∀ᵐ z : Plane,z≠0 := by
        apply ae_iff.mpr
        simp
      filter_upwards [hne] with z hz
      apply tendsto_const_nhds.congr'
      filter_upwards [shrinkingCutoff_eventually_zero hc (radiusSq_pos hz)] with n hn
      change 0=shrinkingCutoff g n (radiusSq z)*planarCurl β z
      rw [hn,zero_mul])
  simpa only [integral_zero,Function.comp_apply] using h

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

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem exists_end_cutoff : ∃ (g : ℝ → ℝ) (r R : ℝ),0 < r ∧ 0<R ∧
    ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ t,g t∈Icc (0:ℝ) 1) ∧
    (∀ t∈Ioo (-r) r,g t=1) ∧ tsupport g⊆Iic R ∧
    {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a := by
  obtain ⟨d,hd,hdb⟩ := infinityRegion_contains_ball a
  let R := (d/2)^2
  have hR : 0<R := sq_pos_of_pos (by linarith)
  have hreg : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a := by
    intro s hs
    apply hdb
    rw [Metric.mem_ball,dist_zero_right]
    have hn : ‖s‖≤d/2 := (sq_le_sq₀ (norm_nonneg s) (by linarith : 0≤d/2)).mp (by
      simpa only [Complex.normSq_eq_norm_sq,R,mem_ofPred_eq] using hs)
    linarith
  obtain ⟨g,hg,hgc,hgs,hg1,hgb⟩ := exists_smooth_cutoff
    (isCompact_Icc : IsCompact (Icc (-R/2) (R/2))) isOpen_Ioo
    (show Icc (-R/2) (R/2)⊆Ioo (-R) R by intro t ht; constructor <;> linarith [ht.1,ht.2])
  refine ⟨g,R/2,R,by linarith,hR,hg,hgc,hgb,?_,?_,hreg⟩
  · intro t ht
    have he : g=ᶠ[𝓝 t] fun _ => 1 := hg1.filter_mono
      (nhds_le_nhdsSet (show t∈Icc (-R/2) (R/2) by
        constructor <;> linarith [ht.1,ht.2]))
    exact he.eq_of_nhds
  · exact fun t ht => (hgs ht).2.le

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem curveEndCutoff_eventually_one_on_compact {g : ℝ → ℝ} {R : ℝ}
    (hR : 0≤R) (h0 : tsupport g⊆Iic R) {K : Set (locus a)} (hK : IsCompact K) :
    ∀ᶠ n in atTop,∀ x∈K,curveEndCutoff a (shrinkingCutoff g n) x=1 := by
  obtain ⟨B,hB,hbound⟩ := (hK.image (curveProjection_continuous a)).isBounded.exists_pos_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R*B^2)
  filter_upwards [eventually_ge_atTop N] with n hn
  intro x hx
  by_cases hz : curveProjection a x=0
  · simp only [curveEndCutoff,inverseComplementCutoff,hz,↓reduceIte]
  · have ht : Complex.normSq (curveProjection a x)>0 := Complex.normSq_pos.mpr hz
    have hb : Complex.normSq (curveProjection a x)≤B^2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_le_sq₀ (norm_nonneg _) hB.le).mpr (hbound _ ⟨x,hx,rfl⟩)
    have hnn : (N:ℝ)≤n := by exact_mod_cast hn
    have hnt : R<((n:ℝ)+1)*Complex.normSq ((curveProjection a x)⁻¹) := by
      rw [Complex.normSq_inv]
      apply (lt_mul_inv_iff₀ ht).mpr
      nlinarith [mul_le_mul_of_nonneg_left hb hR]
    have hg0 : g (((n:ℝ)+1)*Complex.normSq ((curveProjection a x)⁻¹))=0 :=
      image_eq_zero_of_notMem_tsupport (fun hg => not_le_of_gt hnt (h0 hg))
    simp only [curveEndCutoff,inverseComplementCutoff,hz,↓reduceIte,shrinkingCutoff,hg0,sub_zero]

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_QuadricInfinityPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
variable {m : ℕ} (a : Fin m → ℂ) (ε : Fin m → Bool)

theorem infinityRegularPhase_contDiffAt {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈infinityRegion a) :
    ContDiffAt ℝ ∞ (infinityRegularPhase a ε) y :=
  (affinePhase m).contDiff.contDiffAt.comp y
    (((infinityRegularPoint_contDiffAt a ε hy).restrict_scalars ℝ).comp y
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt)

theorem infinityRegularPrimitive_contDiffAt (c : ℝ) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈infinityRegion a) :
    ContDiffAt ℝ ∞ (infinityRegularPrimitive a ε c) y :=
  staticPullbackOneForm_smoothAt (affineFSPrimitive_smooth c).contDiffAt
    (infinityRegularPhase_contDiffAt a ε hy)

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_ConvexWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem extendedChartCoefficient_zero_form (c : M) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => (0 : ManifoldTwoForm Plane M)) (0,y)=0 := by
  unfold extendedChartCoefficient spatialZeroExtension
  split_ifs <;> simp only [chartTwoForm_zero,zero_apply]

theorem extendedChartCoefficient_sum {I : Type*} (s : Finset I) (c : M)
    (Ω : I → ManifoldTwoForm Plane M) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => ∑ i ∈ s, Ω i) (0,y) =
      ∑ i ∈ s, extendedChartCoefficient c (fun _ : ℝ => Ω i) (0,y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,extendedChartCoefficient_zero_form]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,extendedChartCoefficient_add,ih]

theorem chartMass_sum {I : Type*} (s : Finset I) (c : M)
    (Ω : I → ManifoldTwoForm Plane M)
    (hΩ : ∀ i ∈ s, Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω i) (0,y))) :
    chartMass c (∑ i ∈ s, Ω i) = ∑ i ∈ s, chartMass c (Ω i) := by
  unfold chartMass
  simp_rw [extendedChartCoefficient_sum]
  exact integral_finsetSum s hΩ

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfaceIntegralIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory Classical
open scoped ContDiff Manifold Topology ENNReal

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
  {I J : Type*} [Fintype I] [Fintype J] {K : Set M}

omit [T2Space M] in

theorem partitionFormMass_independent (hpos : PositivePlaneTransitions M)
    (hK : IsCompact K) (B : I → SurfaceCoordinateBox M) (C : J → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (ν : SmoothPartitionOfUnity J 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hν : ν.IsSubordinate (fun j => (C j).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (hskew : ∀ x u v, Ω x u v = -Ω x v u) (hz : ∀ x, x ∉ K → Ω x=0) :
    partitionFormMass B ρ Ω = partitionFormMass C ν Ω := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let D : I → J → ManifoldTwoForm Plane M := fun i j x => ρ i x • (ν j x • Ω x)
  let L : I → J → Set M := fun i j => K ∩ tsupport (ρ i) ∩ tsupport (ν j)
  have hL (i : I) (j : J) : IsCompact (L i j) :=
    (hK.inter_right (isClosed_tsupport (ρ i))).inter_right (isClosed_tsupport (ν j))
  have hLB (i : I) (j : J) : L i j ⊆ (extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.1.2).1
  have hLC (i : I) (j : J) : L i j ⊆ (extChartAt 𝓘(ℝ,Plane) (C j).center).source :=
    fun _ hx => (hν j hx.2).1
  have hDz (i : I) (j : J) (x : M) (hx : x ∉ L i j) : D i j x=0 := by
    by_cases hk : x ∈ K
    · by_cases hi : x ∈ tsupport (ρ i)
      · have hj : x ∉ tsupport (ν j) := fun hj => hx ⟨⟨hk,hi⟩,hj⟩
        simp only [D,image_eq_zero_of_notMem_tsupport hj,zero_smul,smul_zero]
      · simp only [D,image_eq_zero_of_notMem_tsupport hi,zero_smul]
    · simp only [D,hz x hk,smul_zero]
  have hDs (i : I) (j : J) : SmoothTwoForm (D i j) :=
    (((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ν j).contMDiff).spatial_smul
      (ρ i).contMDiff).eval 0
  have hDa (i : I) (j : J) (x : M) (u v : Plane) : D i j x u v = -D i j x v u := by
    change ρ i x * (ν j x * Ω x u v) = -(ρ i x * (ν j x * Ω x v u))
    rw [hskew x u v]; ring
  have hsumJ (i : I) : (∑ j, D i j) = fun x => ρ i x • Ω x := by
    funext x
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    simp only [Finset.sum_apply,D,sum_apply,smul_apply,smul_eq_mul]
    rw [← Finset.mul_sum,← Finset.sum_mul]
    by_cases hx : x ∈ K
    · have hh : (∑ j, ν j x)=1 := by simpa only [finsum_eq_sum_of_fintype] using ν.sum_eq_one hx
      rw [hh,one_mul]
    · simp only [hz x hx,zero_apply,mul_zero]
  have hsumI (j : J) : (∑ i, D i j) = fun x => ν j x • Ω x := by
    funext x
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    simp only [Finset.sum_apply,D,sum_apply,smul_apply,smul_eq_mul]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ K
    · have hh : (∑ i, ρ i x)=1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hh,one_mul]
    · simp only [hz x hx,zero_apply,mul_zero]
  have hchange (i : I) (j : J) : chartMass (B i).center (D i j)=chartMass (C j).center (D i j) := by
    apply chartMass_change (hDa i j) (hL i j) (hLB i j) (hLC i j) (hDz i j)
    rintro y ⟨x,hx,rfl⟩
    apply hpos (B i).center (C j).center _ ((extChartAt 𝓘(ℝ,Plane) (B i).center).map_source (hLB i j hx))
    simpa only [(extChartAt 𝓘(ℝ,Plane) (B i).center).left_inv (hLB i j hx)] using hLC i j hx
  unfold partitionFormMass
  calc
    (∑ i, chartMass (B i).center (fun x => ρ i x • Ω x)) =
        ∑ i, ∑ j, chartMass (B i).center (D i j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hsumJ i]
      exact chartMass_sum Finset.univ (B i).center (D i)
        (fun j _ => (hDs i j).coefficient_integrable _ (hL i j) (hLB i j) (hDz i j))
    _ = ∑ i, ∑ j, chartMass (C j).center (D i j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => hchange i j)
    _ = ∑ j, ∑ i, chartMass (C j).center (D i j) := Finset.sum_comm
    _ = ∑ j, chartMass (C j).center (fun x => ν j x • Ω x) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hsumI j]
      exact (chartMass_sum Finset.univ (C j).center (fun i => D i j)
        (fun i _ => (hDs i j).coefficient_integrable _ (hL i j) (hLC i j) (hDz i j))).symm

end

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [MeasurableSpace M] [BorelSpace M]

theorem chartInverseExtension_measurable (c : M) : Measurable (chartInverseExtension c) := by
  classical
  exact (continuousOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) c).measurable_piecewise
    continuousOn_const (isOpen_extChartAt_target c).measurableSet

omit [MeasurableSpace M] [BorelSpace M] in
theorem chartInverseExtension_eq {c : M} {y : Plane}
    (hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target) :
    chartInverseExtension c y=(extChartAt 𝓘(ℝ,Plane) c).symm y := ite_eq_left hy

theorem integral_chartAreaMeasure (c : M) {w : Plane → ℝ}
    (hw : Measurable w) (hpos : ∀ y,0≤w y)
    (hz : ∀ y,y∉(extChartAt 𝓘(ℝ,Plane) c).target→w y=0)
    {f : M → ℝ} (hf : Measurable f) :
    (∫ x, f x ∂chartAreaMeasure c w)=
      ∫ y, w y*f ((extChartAt 𝓘(ℝ,Plane) c).symm y) := by
  rw [chartAreaMeasure,integral_map (chartInverseExtension_measurable c).aemeasurable
    hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul (hw.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [ENNReal.toReal_ofReal (hpos y)]
  change w y*f (chartInverseExtension c y)=_
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
  · rw [chartInverseExtension_eq hy]
  · rw [hz y hy,zero_mul,zero_mul]

theorem integrable_chartAreaMeasure (c : M) {w : Plane → ℝ}
    (hw : Measurable w) (hpos : ∀ y,0≤w y)
    (hz : ∀ y,y∉(extChartAt 𝓘(ℝ,Plane) c).target→w y=0)
    {f : M → ℝ} (hf : Measurable f) :
    Integrable f (chartAreaMeasure c w) ↔
      Integrable (fun y => w y*f ((extChartAt 𝓘(ℝ,Plane) c).symm y)) := by
  rw [chartAreaMeasure,integrable_map_measure hf.aestronglyMeasurable
    (chartInverseExtension_measurable c).aemeasurable,
    integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [] with y
  rw [ENNReal.toReal_ofReal (hpos y)]
  change w y*f (chartInverseExtension c y)=_
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
  · rw [chartInverseExtension_eq hy]
  · rw [hz y hy,zero_mul,zero_mul]

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {I : Type*} {K : Set M}

theorem partitionChartDensity_off_target (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Λ : ManifoldTwoForm Plane M) (i : I) {y : Plane}
    (hy : y∉(extChartAt 𝓘(ℝ,Plane) (B i).center).target) :
    partitionChartDensity B ρ Λ i y=0 := ite_eq_right hy

theorem partitionChartDensity_nonneg (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Λ : ManifoldTwoForm Plane M}
    (hΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm Λ c y (1,0) (0,1)) (i : I) (y : Plane) :
    0≤partitionChartDensity B ρ Λ i y := by
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) (B i).center).target
  · unfold partitionChartDensity extendedChartCoefficient spatialZeroExtension
    rw [ite_eq_left hy]
    change 0 ≤ chartTwoForm (fun x => ρ i x • Λ x) (B i).center y (1,0) (0,1)
    rw [chartTwoForm_spatial_smul]
    exact mul_nonneg (ρ.nonneg i _) (hΛ _ _ hy)
  · rw [partitionChartDensity_off_target B ρ Λ i hy]

theorem partitionChartDensity_spatial_smul (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Λ : ManifoldTwoForm Plane M) (f : M → ℝ) (i : I) (y : Plane) :
    partitionChartDensity B ρ (fun x => f x • Λ x) i y=
      partitionChartDensity B ρ Λ i y * f ((extChartAt 𝓘(ℝ,Plane) (B i).center).symm y) := by
  unfold partitionChartDensity extendedChartCoefficient spatialZeroExtension
  split_ifs
  · change chartTwoForm (fun x => ρ i x • (f x • Λ x)) (B i).center y (1,0) (0,1) =
      chartTwoForm (fun x => ρ i x • Λ x) (B i).center y (1,0) (0,1) * _
    rw [chartTwoForm_spatial_smul,chartTwoForm_spatial_smul,chartTwoForm_spatial_smul]
    simp only [smul_apply, smul_eq_mul]
    ring
  · exact (zero_mul _).symm

variable [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem partitionChartDensity_properties (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ) (i : I) :
    ContDiff ℝ ∞ (partitionChartDensity B ρ Λ i) ∧
      HasCompactSupport (partitionChartDensity B ρ Λ i) ∧
      Integrable (partitionChartDensity B ρ Λ i) := by
  let L := tsupport (ρ i)
  have hL : IsCompact L := (B i).isCompact_compactCarrier.of_isClosed_subset
    (isClosed_tsupport _) ((hρ i).trans (B i).carrier_subset_compactCarrier)
  have hLc : L⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source := fun _ hx => (hρ i hx).1
  have hs : SmoothTwoFormFamily (fun _ : ℝ => fun x => ρ i x • Λ x) :=
    (SmoothTwoFormFamily.const hΛ).spatial_smul (ρ i).contMDiff
  have hz : ∀ (p : ℝ) x,x∉L→ρ i x • Λ x=0 := by
    intro _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (0:ℝ) * _ = 0
    exact zero_mul _
  have hfull : ContDiff ℝ ∞ (extendedChartCoefficient (B i).center
      (fun _ : ℝ => fun x => ρ i x • Λ x)) :=
    extendedChartCoefficient_smooth (Ω := fun _ : ℝ => fun x => ρ i x • Λ x)
      (c := (B i).center) (hs (B i).center) hL hLc hz
  have hsm : ContDiff ℝ ∞ (partitionChartDensity B ρ Λ i) :=
    hfull.comp (f := fun y : Plane => ((0 : ℝ),y))
      (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (partitionChartDensity B ρ Λ i) := by
    apply HasCompactSupport.intro (hL.image_of_continuousOn
      ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) (B i).center).mono hLc))
    exact fun _ hy => extendedChartCoefficient_zero hz 0 hy
  exact ⟨hsm,hc,hsm.continuous.integrable_of_hasCompactSupport hc⟩

variable [Fintype I] [MeasurableSpace M] [BorelSpace M]

theorem integral_partitionAreaMeasure (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm Λ c y (1,0) (0,1))
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ f) :
    (∫ x, f x ∂partitionAreaMeasure B ρ Λ)=
      partitionFormMass B ρ (fun x => f x • Λ x) := by
  have hfp : SmoothTwoForm (fun x => f x • Λ x) :=
    ((SmoothTwoFormFamily.const (P := ℝ) hΛ).spatial_smul hf).eval 0
  have hmeas (i : I) : Measurable (partitionChartDensity B ρ Λ i) :=
    (partitionChartDensity_properties B ρ hρ hΛ i).1.continuous.measurable
  have hint (i : I) : Integrable f
      (chartAreaMeasure (B i).center (partitionChartDensity B ρ Λ i)) := by
    rw [integrable_chartAreaMeasure _ (hmeas i) (partitionChartDensity_nonneg B ρ hpos i)
      (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy) hf.continuous.measurable]
    simpa only [← partitionChartDensity_spatial_smul] using
      (partitionChartDensity_properties B ρ hρ hfp i).2.2
  rw [partitionAreaMeasure,integral_finsetSum_measure (fun i _ => hint i)]
  unfold partitionFormMass chartMass
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_chartAreaMeasure _ (hmeas i) (partitionChartDensity_nonneg B ρ hpos i)
    (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy) hf.continuous.measurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => (partitionChartDensity_spatial_smul B ρ Λ f i y).symm)

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [MeasurableSpace M] [BorelSpace M]

theorem integral_chartAreaMeasure_restrict (c : M) {w : Plane → ℝ}
    (hw : Measurable w) (hpos : ∀ y,0≤w y)
    (hz : ∀ y,y∉(extChartAt 𝓘(ℝ,Plane) c).target→w y=0)
    {C : Set M} (hC : MeasurableSet C) {f : M → ℝ} (hf : Measurable f) :
    (∫ x in C, f x ∂chartAreaMeasure c w)=
      ∫ y in (extChartAt 𝓘(ℝ,Plane) c).target ∩
        (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C,
        w y*f ((extChartAt 𝓘(ℝ,Plane) c).symm y) := by
  rw [← integral_indicator hC, integral_chartAreaMeasure c hw hpos hz (hf.indicator hC)]
  have hD : MeasurableSet ((extChartAt 𝓘(ℝ,Plane) c).target ∩
      (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C) :=
    by
      have he : (extChartAt 𝓘(ℝ,Plane) c).target ∩
          (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C =
          (extChartAt 𝓘(ℝ,Plane) c).target ∩ chartInverseExtension c ⁻¹' C := by
        ext y
        by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
        · simp only [mem_inter_iff,mem_preimage,hy,true_and,chartInverseExtension_eq hy]
        · simp only [mem_inter_iff,hy,false_and]
      rw [he]
      exact (isOpen_extChartAt_target c).measurableSet.inter
        (chartInverseExtension_measurable c hC)
  rw [← integral_indicator hD]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
  · by_cases hc : (extChartAt 𝓘(ℝ,Plane) c).symm y∈C
    · simp only [Set.indicator,mem_inter_iff,mem_preimage,hy,hc,and_self,↓reduceIte]
    · simp only [Set.indicator,mem_inter_iff,mem_preimage,hy,hc,and_false,↓reduceIte,mul_zero]
  · simp only [Set.indicator,mem_inter_iff,mem_preimage,hy,false_and,↓reduceIte,hz y hy,zero_mul]

variable {I : Type*} [Fintype I] {K : Set M}

variable [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem smooth_integrable_partitionAreaMeasure (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm Λ c y (1,0) (0,1))
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ f) :
    Integrable f (partitionAreaMeasure B ρ Λ) := by
  have hfp : SmoothTwoForm (fun x => f x • Λ x) :=
    ((SmoothTwoFormFamily.const (P := ℝ) hΛ).spatial_smul hf).eval 0
  apply integrable_finsetSum_measure.mpr
  intro i _
  rw [integrable_chartAreaMeasure _
    (partitionChartDensity_properties B ρ hρ hΛ i).1.continuous.measurable
    (partitionChartDensity_nonneg B ρ hpos i)
    (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy) hf.continuous.measurable]
  simpa only [← partitionChartDensity_spatial_smul] using
    (partitionChartDensity_properties B ρ hρ hfp i).2.2

theorem integral_partitionAreaMeasure_restrict (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm Λ c y (1,0) (0,1))
    {C : Set M} (hC : MeasurableSet C)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ f) :
    (∫ x in C, f x ∂partitionAreaMeasure B ρ Λ)=
      restrictedPartitionFormMass B ρ C (fun x => f x • Λ x) := by
  have hh := (smooth_integrable_partitionAreaMeasure B ρ hρ hΛ hpos hf).indicator hC
  have hint : ∀ i ∈ (Finset.univ : Finset I), Integrable (C.indicator f)
      (chartAreaMeasure (B i).center (partitionChartDensity B ρ Λ i)) :=
    integrable_finsetSum_measure.mp hh
  rw [← integral_indicator hC,partitionAreaMeasure,
    integral_finsetSum_measure hint]
  unfold restrictedPartitionFormMass
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator hC, integral_chartAreaMeasure_restrict _
    (partitionChartDensity_properties B ρ hρ hΛ i).1.continuous.measurable
    (partitionChartDensity_nonneg B ρ hpos i)
    (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy) hC hf.continuous.measurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => (partitionChartDensity_spatial_smul B ρ Λ f i y).symm)

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]

 theorem chartRegion_measurable (c : M) {C : Set M} (hC : MeasurableSet C) :
    MeasurableSet ((extChartAt 𝓘(ℝ,Plane) c).target ∩
      (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C) := by
  have he : (extChartAt 𝓘(ℝ,Plane) c).target ∩
      (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C =
      (extChartAt 𝓘(ℝ,Plane) c).target ∩ chartInverseExtension c ⁻¹' C := by
    ext y
    by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
    · simp only [mem_inter_iff,mem_preimage,hy,true_and,chartInverseExtension_eq hy]
    · simp only [mem_inter_iff,hy,false_and]
  rw [he]
  exact (isOpen_extChartAt_target c).measurableSet.inter (chartInverseExtension_measurable c hC)

 omit [MeasurableSpace M] [BorelSpace M] in
 theorem extendedChartCoefficient_indicator (c : M) (C : Set M)
    (Ω : ManifoldTwoForm Plane M) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => C.indicator Ω) (0,y)=
      ((extChartAt 𝓘(ℝ,Plane) c).target ∩ (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C).indicator
        (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)) y := by
  classical
  unfold extendedChartCoefficient spatialZeroExtension chartTwoForm
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
  · by_cases hc : (extChartAt 𝓘(ℝ,Plane) c).symm y∈C
    · simp only [Set.indicator,hy,hc,mem_inter_iff,mem_preimage,and_self,↓reduceIte]
    · simp only [Set.indicator,hy,hc,mem_inter_iff,mem_preimage,and_false,↓reduceIte]
      simp only [ContinuousLinearMap.bilinearComp_apply,zero_apply]
  · simp only [Set.indicator,hy,mem_inter_iff,false_and,↓reduceIte]

 theorem extendedChartCoefficient_indicator_integrable (c : M) {C : Set M}
    (hC : MeasurableSet C) {Ω : ManifoldTwoForm Plane M}
    (hΩ : Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y))) :
    Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => C.indicator Ω) (0,y)) := by
  simpa only [extendedChartCoefficient_indicator] using hΩ.indicator (chartRegion_measurable c hC)

 theorem restrictedPartitionFormMass_eq_indicator {I : Type*} [Fintype I] {K : Set M}
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {C : Set M} (hC : MeasurableSet C) (Ω : ManifoldTwoForm Plane M) :
    restrictedPartitionFormMass B ρ C Ω=partitionFormMass B ρ (C.indicator Ω) := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  unfold restrictedPartitionFormMass partitionFormMass chartMass
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun x => ρ i x • C.indicator Ω x)=C.indicator (fun x => ρ i x • Ω x) := by
    funext x
    by_cases hx : x∈C <;> simp only [Set.indicator,hx,↓reduceIte,smul_zero]
  rw [he]
  simp_rw [extendedChartCoefficient_indicator]
  rw [integral_indicator (chartRegion_measurable (B i).center hC)]
  rfl

end

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
  {I J : Type*} [Fintype I] [Fintype J] {K : Set M}

omit [T2Space M] in

theorem partitionFormMass_independent_integrable (hpos : PositivePlaneTransitions M)
    (hK : IsCompact K) (B : I → SurfaceCoordinateBox M) (C : J → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (ν : SmoothPartitionOfUnity J 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hν : ν.IsSubordinate (fun j => (C j).carrier))
    {Ω : ManifoldTwoForm Plane M}
    (hskew : ∀ x u v, Ω x u v = -Ω x v u) (hz : ∀ x, x ∉ K → Ω x=0)
    (hB : ∀ i j,Integrable (fun y => extendedChartCoefficient (B i).center
      (fun _ : ℝ => fun x => ρ i x • (ν j x • Ω x)) (0,y)))
    (hC : ∀ i j,Integrable (fun y => extendedChartCoefficient (C j).center
      (fun _ : ℝ => fun x => ρ i x • (ν j x • Ω x)) (0,y))) :
    partitionFormMass B ρ Ω = partitionFormMass C ν Ω := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let D : I → J → ManifoldTwoForm Plane M := fun i j x => ρ i x • (ν j x • Ω x)
  let L : I → J → Set M := fun i j => K ∩ tsupport (ρ i) ∩ tsupport (ν j)
  have hL (i : I) (j : J) : IsCompact (L i j) :=
    (hK.inter_right (isClosed_tsupport (ρ i))).inter_right (isClosed_tsupport (ν j))
  have hLB (i : I) (j : J) : L i j ⊆ (extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.1.2).1
  have hLC (i : I) (j : J) : L i j ⊆ (extChartAt 𝓘(ℝ,Plane) (C j).center).source :=
    fun _ hx => (hν j hx.2).1
  have hDz (i : I) (j : J) (x : M) (hx : x ∉ L i j) : D i j x=0 := by
    by_cases hk : x ∈ K
    · by_cases hi : x ∈ tsupport (ρ i)
      · have hj : x ∉ tsupport (ν j) := fun hj => hx ⟨⟨hk,hi⟩,hj⟩
        simp only [D,image_eq_zero_of_notMem_tsupport hj,zero_smul,smul_zero]
      · simp only [D,image_eq_zero_of_notMem_tsupport hi,zero_smul]
    · simp only [D,hz x hk,smul_zero]
  have hDa (i : I) (j : J) (x : M) (u v : Plane) : D i j x u v = -D i j x v u := by
    change ρ i x * (ν j x * Ω x u v) = -(ρ i x * (ν j x * Ω x v u))
    rw [hskew x u v]; ring
  have hsumJ (i : I) : (∑ j, D i j) = fun x => ρ i x • Ω x := by
    funext x
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    simp only [Finset.sum_apply,D,sum_apply,smul_apply,smul_eq_mul]
    rw [← Finset.mul_sum,← Finset.sum_mul]
    by_cases hx : x ∈ K
    · have hh : (∑ j, ν j x)=1 := by simpa only [finsum_eq_sum_of_fintype] using ν.sum_eq_one hx
      rw [hh,one_mul]
    · simp only [hz x hx,zero_apply,mul_zero]
  have hsumI (j : J) : (∑ i, D i j) = fun x => ν j x • Ω x := by
    funext x
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    simp only [Finset.sum_apply,D,sum_apply,smul_apply,smul_eq_mul]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ K
    · have hh : (∑ i, ρ i x)=1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hh,one_mul]
    · simp only [hz x hx,zero_apply,mul_zero]
  have hchange (i : I) (j : J) : chartMass (B i).center (D i j)=chartMass (C j).center (D i j) := by
    apply chartMass_change (hDa i j) (hL i j) (hLB i j) (hLC i j) (hDz i j)
    rintro y ⟨x,hx,rfl⟩
    apply hpos (B i).center (C j).center _ ((extChartAt 𝓘(ℝ,Plane) (B i).center).map_source (hLB i j hx))
    simpa only [(extChartAt 𝓘(ℝ,Plane) (B i).center).left_inv (hLB i j hx)] using hLC i j hx
  unfold partitionFormMass
  calc
    (∑ i, chartMass (B i).center (fun x => ρ i x • Ω x)) =
        ∑ i, ∑ j, chartMass (B i).center (D i j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hsumJ i]
      exact chartMass_sum Finset.univ (B i).center (D i)
        (fun j _ => hB i j)
    _ = ∑ i, ∑ j, chartMass (C j).center (D i j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => hchange i j)
    _ = ∑ j, ∑ i, chartMass (C j).center (D i j) := Finset.sum_comm
    _ = ∑ j, chartMass (C j).center (fun x => ν j x • Ω x) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hsumI j]
      exact (chartMass_sum Finset.univ (C j).center (fun i => D i j)
        (fun i _ => hC i j)).symm

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  {I J : Type*} [Fintype I] [Fintype J] {K : Set M}

 theorem restrictedPartitionFormMass_independent (hpos : PositivePlaneTransitions M)
    (hK : IsCompact K) (B : I → SurfaceCoordinateBox M) (C : J → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (ν : SmoothPartitionOfUnity J 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hν : ν.IsSubordinate (fun j => (C j).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (hskew : ∀ x u v,Ω x u v= -Ω x v u) :
    restrictedPartitionFormMass B ρ K Ω=restrictedPartitionFormMass C ν K Ω := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let L : I → J → Set M := fun i j => tsupport (ρ i) ∩ tsupport (ν j)
  have hL (i : I) (j : J) : IsCompact (L i j) :=
    ((B i).isCompact_compactCarrier.of_isClosed_subset (isClosed_tsupport _)
      ((hρ i).trans (B i).carrier_subset_compactCarrier)).inter_right (isClosed_tsupport _)
  have hLB (i : I) (j : J) : L i j⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.1).1
  have hLC (i : I) (j : J) : L i j⊆(extChartAt 𝓘(ℝ,Plane) (C j).center).source :=
    fun _ hx => (hν j hx.2).1
  have hint (i : I) (j : J) (c : M) (hc : L i j⊆(extChartAt 𝓘(ℝ,Plane) c).source) :
      Integrable (fun y => extendedChartCoefficient c
        (fun _ : ℝ => fun x => ρ i x • (ν j x • K.indicator Ω x)) (0,y)) := by
    let D : ManifoldTwoForm Plane M := fun x => ρ i x • (ν j x • Ω x)
    have hDs : SmoothTwoForm D :=
      (((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ν j).contMDiff).spatial_smul
        (ρ i).contMDiff).eval 0
    have hDz : ∀ x,x∉L i j → D x=0 := by
      intro x hx
      by_cases hi : x∈tsupport (ρ i)
      · have hj : x∉tsupport (ν j) := fun hj => hx ⟨hi,hj⟩
        simp only [D,image_eq_zero_of_notMem_tsupport hj,zero_smul,smul_zero]
      · simp only [D,image_eq_zero_of_notMem_tsupport hi,zero_smul]
    have he : (fun x => ρ i x • (ν j x • K.indicator Ω x))=K.indicator D := by
      funext x
      by_cases hx : x∈K <;> simp only [Set.indicator,hx,↓reduceIte,D,smul_zero]
    rw [he]
    exact extendedChartCoefficient_indicator_integrable c hK.measurableSet
      (hDs.coefficient_integrable c (hL i j) hc hDz)
  rw [restrictedPartitionFormMass_eq_indicator B ρ hK.measurableSet,
    restrictedPartitionFormMass_eq_indicator C ν hK.measurableSet]
  apply partitionFormMass_independent_integrable hpos hK B C ρ ν hρ hν
  · intro x u v
    by_cases hx : x∈K
    · simpa only [Set.indicator_of_mem hx] using hskew x u v
    · simp only [Set.indicator_of_notMem hx,zero_apply,neg_zero]
  · exact fun x hx => Set.indicator_of_notMem hx Ω
  · exact fun i j => hint i j (B i).center (hLB i j)
  · exact fun i j => hint i j (C j).center (hLC i j)

end
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]

 theorem compactSurfacePartition_subordinate {D : Set M} (hD : IsCompact D) :
    (compactSurfacePartition hD).IsSubordinate
      (fun B : compactSurfaceBoxes hD => B.1.carrier) :=
  Classical.choose_spec (Classical.choose_spec (SurfaceCoordinateBox.finite_partition hD))

 variable [MeasurableSpace M] [BorelSpace M]
 theorem compactSurfaceFormIntegral_eq {I : Type*} [Fintype I] {D : Set M}
    (hD : IsCompact D) (hor : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M D)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (hskew : ∀ x u v,Ω x u v= -Ω x v u) :
    compactSurfaceFormIntegral hD Ω=restrictedPartitionFormMass B ρ D Ω :=
  restrictedPartitionFormMass_independent hor hD _ B _ ρ
    (compactSurfacePartition_subordinate hD) hρ hΩ hskew

end
section

section Integral
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem restrictedPartitionFormMass_smul {I : Type*} [Fintype I] {K : Set M}
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (D : Set M) (a : ℝ) (Ω : ManifoldTwoForm Plane M) :
    restrictedPartitionFormMass B ρ D (a • Ω) = a * restrictedPartitionFormMass B ρ D Ω := by
  unfold restrictedPartitionFormMass
  simp_rw [show a • Ω = fun x => a • Ω x from rfl,
    partitionChartDensity_spatial_smul B ρ Ω (fun _ => a)]
  simp_rw [integral_mul_const]
  rw [← Finset.sum_mul, mul_comm]

variable [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem compactSurfaceFormIntegral_smul {D : Set M} (hD : IsCompact D)
    (a : ℝ) (Ω : ManifoldTwoForm Plane M) :
    compactSurfaceFormIntegral hD (a • Ω)=a * compactSurfaceFormIntegral hD Ω :=
  restrictedPartitionFormMass_smul _ _ _ _ _

end Integral

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialFamilyExtension
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold Filter

theorem radialAnnulus_compact (r R : ℝ) : IsCompact (radialAnnulus r R) := by
  have hc : IsClosed (radialAnnulus r R) :=
    (isClosed_le continuous_const radiusSq_smooth.continuous).inter
      (isClosed_le radiusSq_smooth.continuous continuous_const)
  apply ((isCompact_Icc : IsCompact (Icc (-(|R|+1)) (|R|+1))).prod
    (isCompact_Icc : IsCompact (Icc (-(|R|+1)) (|R|+1)))).of_isClosed_subset hc
  intro z hz
  have hb : z.1^2+z.2^2≤|R| := hz.2.trans (le_abs_self R)
  constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2,abs_nonneg R]

theorem radialAnnulus_ne_zero {r R : ℝ} (hr : 0 < r) {z : Plane}
    (hz : z∈radialAnnulus r R) : z≠0 := by
  intro h
  subst z
  have : r≤0 := by simpa [radiusSq] using hz.1
  linarith

theorem radiusSq_complex (z : Plane) : Complex.normSq (Complex.equivRealProdCLM.symm z)=radiusSq z := by
  change z.1*z.1+z.2*z.2=z.1^2+z.2^2
  ring

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricEndAnnuli
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
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
variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem radialAnnulus_in_end {r R : ℝ} (hr : 0 < r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) (ε : Fin m → Bool) :
    radialAnnulus r R⊆(infinityDiffeomorph a ε).source := by
  intro y hy
  rw [infinityDiffeomorph_source]
  refine ⟨?_,hR (by change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R; rw [radiusSq_complex];exact hy.2)⟩
  intro he
  have hey : y=0 := by
    apply Complex.equivRealProdCLM.symm.injective
    simpa only [map_zero] using he
  exact radialAnnulus_ne_zero hr hy hey

theorem curveEndAnnulus_compact {r R : ℝ} (hr : 0 < r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) (ε : Fin m → Bool) :
    IsCompact (curveEndAnnulus a ε r R) :=
  (radialAnnulus_compact r R).image_of_continuousOn
    ((infinityDiffeomorph a ε).contMDiffOn.continuousOn.mono (radialAnnulus_in_end a hr hR ε))

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfaceCutoffDefect
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

variable {m : ℕ} (a : Fin m → ℂ)

theorem exists_infinityRegularPrimitive_extension {R : ℝ}
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) (ε : Fin m → Bool) (c : ℝ) :
    ∃ β : Plane → Plane →L[ℝ] ℝ,ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      β=ᶠ[𝓝ˢ (radialAnnulus 0 R)] infinityRegularPrimitive a ε c := by
  let U : Set Plane := Complex.equivRealProdCLM.symm ⁻¹' infinityRegion a
  have hU : IsOpen U := (infinityRegion_open a).preimage Complex.equivRealProdCLM.symm.continuous
  have hKU : radialAnnulus 0 R⊆U := by
    intro y hy
    apply hR
    change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R
    rw [radiusSq_complex]
    exact hy.2
  have hf : ContDiffOn ℝ ∞ (infinityRegularPrimitive a ε c) U :=
    fun y hy => (infinityRegularPrimitive_contDiffAt a ε c hy).contDiffWithinAt
  obtain ⟨χ,_hχ,_hχc,_hχU,_hr,_h1,hf,hc,he⟩ :=
    exists_smooth_compact_extension (radialAnnulus_compact 0 R) hU hKU hf
  exact ⟨fun y => χ y • infinityRegularPrimitive a ε c y,hf,hc,he⟩

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricEndResidueMass
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

omit [T2Space M] in
theorem partitionFormMass_independent_support {I J : Type*} [Fintype I] [Fintype J]
    {K D L : Set M} (hor : PositivePlaneTransitions M) (hL : IsCompact L)
    (hLK : L⊆K) (hLD : L⊆D)
    (B : I → SurfaceCoordinateBox M) (C : J → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (ν : SmoothPartitionOfUnity J 𝓘(ℝ,Plane) M D)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hν : ν.IsSubordinate (fun j => (C j).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) (hz : ∀ x,x∉L→Ω x=0) :
    partitionFormMass B ρ Ω=partitionFormMass C ν Ω :=
  partitionFormMass_independent hor hL B C (partitionOnSubset ρ hLK)
    (partitionOnSubset ν hLD) hρ hν hΩ ha hz

variable [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

theorem compactSurfaceFormIntegral_eq_larger_partition {I : Type*} [Fintype I]
    {K D : Set M} (hD : IsCompact D) (hor : PositivePlaneTransitions M) (hDK : D⊆K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) :
    compactSurfaceFormIntegral hD Ω=restrictedPartitionFormMass B ρ D Ω :=
  compactSurfaceFormIntegral_eq hD hor B (partitionOnSubset ρ hDK) hρ hΩ ha

theorem compactSurfaceFormIntegral_eq_setIntegral {I : Type*} [Fintype I]
    {K D : Set M} (hD : IsCompact D) (hor : PositivePlaneTransitions M) (hDK : D⊆K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0 ≤ chartTwoForm Ω c y (1,0) (0,1)) :
    compactSurfaceFormIntegral hD Ω=∫ _ in D,(1:ℝ) ∂partitionAreaMeasure B ρ Ω := by
  rw [compactSurfaceFormIntegral_eq_larger_partition hD hor hDK B ρ hρ hΩ ha,
    integral_partitionAreaMeasure_restrict B ρ hρ hΩ hp hD.measurableSet contMDiff_const]
  congr 1
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change Ω x u v=(1:ℝ)*Ω x u v
  ring

omit [MeasurableSpace M] [BorelSpace M] in
theorem surfaceCutoffMass_eq {I : Type*} [Fintype I] {K : Set M}
    (hor : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {κ : M → ℝ} (hκc : HasCompactSupport κ) (hκK : tsupport κ⊆K)
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) :
    surfaceCutoffMass hκc Ω=partitionFormMass B ρ (fun x => κ x • Ω x) := by
  apply partitionFormMass_independent_support hor hκc Subset.rfl hκK _ B _ ρ
    (compactSurfacePartition_subordinate hκc) hρ
    (((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul hκ).eval 0)
  · intro x u v
    change κ x*Ω x u v= -(κ x*Ω x v u)
    rw [ha x u v]
    ring
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (0:ℝ)*Ω x u v=0
    exact zero_mul _

theorem surfaceCutoffMass_le_compactIntegral {D : Set M}
    (hor : PositivePlaneTransitions M) (hD : IsCompact D)
    {κ : M → ℝ} (hκc : HasCompactSupport κ) (hκD : tsupport κ⊆D)
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ) (hb : ∀ x,κ x≤1)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0 ≤ chartTwoForm Ω c y (1,0) (0,1)) :
    surfaceCutoffMass hκc Ω ≤ compactSurfaceFormIntegral hD Ω := by
  let B := fun b : compactSurfaceBoxes hD => b.1
  let ρ := compactSurfacePartition hD
  have hρ := compactSurfacePartition_subordinate hD
  rw [surfaceCutoffMass_eq hor B ρ hρ hκc hκD hκ hΩ ha,
    ← integral_partitionAreaMeasure B ρ hρ hΩ hp hκ,
    compactSurfaceFormIntegral_eq_setIntegral hD hor Subset.rfl B ρ hρ hΩ ha hp,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := D) (fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun hn => hx (hκD hn)))]
  exact integral_mono_ae
    (smooth_integrable_partitionAreaMeasure B ρ hρ hΩ hp hκ).integrableOn
    (smooth_integrable_partitionAreaMeasure B ρ hρ hΩ hp contMDiff_const).integrableOn
    (Filter.Eventually.of_forall hb)

theorem compactIntegral_le_surfaceCutoffMass {D : Set M}
    (hor : PositivePlaneTransitions M) (hD : IsCompact D)
    {κ : M → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ) (hn : ∀ x,0≤κ x)
    (h1 : ∀ x∈D,κ x=1)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0 ≤ chartTwoForm Ω c y (1,0) (0,1)) :
    compactSurfaceFormIntegral hD Ω≤ surfaceCutoffMass hκc Ω := by
  have hDK : D⊆tsupport κ := by
    intro x hx
    apply subset_tsupport κ
    change κ x≠0
    rw [h1 x hx]
    exact one_ne_zero
  let B := fun b : compactSurfaceBoxes hκc => b.1
  let ρ := compactSurfacePartition hκc
  have hρ := compactSurfacePartition_subordinate hκc
  rw [compactSurfaceFormIntegral_eq_setIntegral hD hor hDK B ρ hρ hΩ ha hp]
  change (∫ x in D,(1:ℝ) ∂partitionAreaMeasure B ρ Ω)≤partitionFormMass B ρ (fun x => κ x • Ω x)
  rw [← integral_partitionAreaMeasure B ρ hρ hΩ hp hκ]
  calc
    _ = ∫ x in D,κ x ∂partitionAreaMeasure B ρ Ω :=
      setIntegral_congr_fun hD.measurableSet (fun x hx => (h1 x hx).symm)
    _ ≤ _ := setIntegral_le_integral
      (smooth_integrable_partitionAreaMeasure B ρ hρ hΩ hp hκ) (Filter.Eventually.of_forall hn)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open Hamiltonian
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

attribute [local instance] OAI.PackingSufficiencySupport.DiagonalQuadrics.quadricEndResidueMassSigmaCompact
theorem curveEndCutoff_surface_mass
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0 < r) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hκc : HasCompactSupport (curveEndCutoff a g)) (c : ℝ)
    (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
    (hβ : ∀ ε,ContDiff ℝ ∞ (β ε))
    (he : ∀ ε,β ε=ᶠ[𝓝ˢ (radialAnnulus 0 R)] infinityRegularPrimitive a ε c) :
    surfaceCutoffMass hκc (curveFSForm a c)=
      (2:ℝ)^m*c*Real.pi-∑ ε : Fin m → Bool,∫ z : Plane,g (radiusSq z)*planarCurl (β ε) z := by
  let K := tsupport (curveEndCutoff a g)∪⋃ ε : Fin m → Bool,curveEndAnnulus a ε r R
  have hK : IsCompact K := hκc.union (isCompact_iUnion (curveEndAnnulus_compact a hr hR))
  let B := fun b : compactSurfaceBoxes hK => b.1
  let ρ := compactSurfacePartition hK
  have hρ := compactSurfacePartition_subordinate hK
  rw [surfaceCutoffMass_eq (positivePlaneTransitions a) B ρ hρ hκc subset_union_left
    (curveEndCutoff_smooth a hg hc) (curveFSForm_smooth a c) (curveFSForm_skew a c)]
  exact curveEndCutoff_partition_mass_bp240 a hK B ρ hρ hg hc hr hR h1 h0 subset_union_left
    (fun ε => (subset_iUnion (curveEndAnnulus a · r R) ε).trans subset_union_right) c β hβ he

theorem tendsto_curveEndCutoff_mass
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0 < r) (hRp : 0≤R) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hb : ∀ t,g t∈Icc (0:ℝ) 1) (c : ℝ) :
    Tendsto (fun n => surfaceCutoffMass (shrinking_curveEndCutoff_compact a hr h1 n)
      (curveFSForm a c)) atTop (𝓝 ((2:ℝ)^m*c*Real.pi)) := by
  classical
  choose β hβ hβc he using fun ε : Fin m → Bool => exists_infinityRegularPrimitive_extension a hR ε c
  have hmass (n : ℕ) : surfaceCutoffMass (shrinking_curveEndCutoff_compact a hr h1 n) (curveFSForm a c)=
      (2:ℝ)^m*c*Real.pi-∑ ε : Fin m → Bool,∫ z : Plane,shrinkingCutoff g n (radiusSq z)*planarCurl (β ε) z :=
    curveEndCutoff_surface_mass a (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hc n)
      (div_pos hr (by positivity : 0<(n:ℝ)+1)) hR (shrinkingCutoff_one h1 n)
      (shrinkingCutoff_tsupport hRp h0 n) _ c β hβ he
  simp_rw [hmass]
  have hs := tendsto_finsetSum Finset.univ (fun ε _ => tendsto_shrinking_regular_residue hg hc hb (hβ ε) (hβc ε))
  have hh := (tendsto_const_nhds (x := (2:ℝ)^m*c*Real.pi)).sub hs
  simpa only [Finset.sum_const_zero,sub_zero] using hh

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricSmoothExhaustion
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter MeasureTheory
open Hamiltonian
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

attribute [local instance] OAI.PackingSufficiencySupport.DiagonalQuadrics.instSigmaCompactSpaceElemAffineLocus
omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem compact_eventually_subset_projectionDomain {K : Set (locus a)} (hK : IsCompact K) :
    ∀ᶠ ℓ in atTop,K⊆projectionDomain a (exhaustionRadius a ℓ) := by
  obtain ⟨B,_hB,hbound⟩ := (hK.image (curveProjection_continuous a)).isBounded.exists_pos_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt B
  filter_upwards [eventually_ge_atTop N] with ℓ hℓ
  intro x hx
  have hnx : ‖x.val.1‖≤B := hbound _ ⟨x,hx,rfl⟩
  have hn : (N:ℝ)≤ℓ := by exact_mod_cast hℓ
  change ‖x.val.1‖≤2+∑ j,‖a j‖+ℓ
  have hp : 0≤∑ j,‖a j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg (a j))
  linarith

theorem compact_area_le_degree {c : ℝ} (hc : 0 < c) {D : Set (locus a)} (hD : IsCompact D) :
    compactSurfaceFormIntegral hD (curveFSForm a c)≤(2:ℝ)^m*c*Real.pi := by
  obtain ⟨g,r,R,hr,hR,hg,hgc,hb,h1,h0,hreg⟩ := exists_end_cutoff a
  apply ge_of_tendsto (tendsto_curveEndCutoff_mass a hg hgc hr hR.le hreg h1 h0 hb c)
  filter_upwards [curveEndCutoff_eventually_one_on_compact a hR.le h0 hD] with n hn
  exact compactIntegral_le_surfaceCutoffMass (positivePlaneTransitions a) hD
    (shrinking_curveEndCutoff_compact a hr h1 n)
    (curveEndCutoff_smooth a (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n))
    (fun x => (curveEndCutoff_range a (fun t => hb _) x).1) hn
    (curveFSForm_smooth a c) (curveFSForm_skew a c)
    (fun b y hy => (curveFSForm_positive a hc b hy).le)

theorem tendsto_exhaustion_area {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ℓ => compactSurfaceFormIntegral
      (projectionDomain_compact a (exhaustionRadius a ℓ)) (curveFSForm a c))
      atTop (𝓝 ((2:ℝ)^m*c*Real.pi)) := by
  obtain ⟨g,r,R,hr,hR,hg,hgc,hb,h1,h0,hreg⟩ := exists_end_cutoff a
  have ht := tendsto_curveEndCutoff_mass a hg hgc hr hR.le hreg h1 h0 hb c
  apply tendsto_order.mpr
  constructor
  · intro b hbdeg
    obtain ⟨n,hn⟩ := ((tendsto_order.mp ht).1 b hbdeg).exists
    filter_upwards [compact_eventually_subset_projectionDomain a
      (shrinking_curveEndCutoff_compact a hr h1 n)] with ℓ hℓ
    apply hn.trans_le
    exact surfaceCutoffMass_le_compactIntegral (positivePlaneTransitions a)
      (projectionDomain_compact a _) (shrinking_curveEndCutoff_compact a hr h1 n) hℓ
      (curveEndCutoff_smooth a (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n))
      (fun x => (curveEndCutoff_range a (fun t => hb _) x).2)
      (curveFSForm_smooth a c) (curveFSForm_skew a c)
      (fun b y hy => (curveFSForm_positive a hc b hy).le)
  · intro b hb
    exact Eventually.of_forall (fun ℓ => (compact_area_le_degree a hc
      (projectionDomain_compact a (exhaustionRadius a ℓ))).trans_lt hb)

theorem tendsto_normalized_exhaustion_area :
    Tendsto (fun ℓ => compactSurfaceFormIntegral
      (projectionDomain_compact a (exhaustionRadius a ℓ)) (curveFSForm a (1/Real.pi)))
      atTop (𝓝 ((2:ℝ)^m)) := by
  have ht := tendsto_exhaustion_area a (one_div_pos.mpr Real.pi_pos)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CubicAreaExhaustion
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory
open Filter

@[simp] theorem diagonalScale_det (a b : ℝ) : (diagonalScale a b).det = a*b := by
  rw [planar_det]
  simp [planarArea_apply]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_EqualNormalModelConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold MeasureTheory Filter

theorem equalNormalCoefficient_pos {m : ℕ} {b d : ℝ} (hb : 0≤b) (hbd : b*d<1)
    {p : Fin m → ℝ} (hp : (∑ j,p j)≤d) : 0<equalNormalCoefficient m b p := by
  unfold equalNormalCoefficient
  have hle := mul_le_mul_of_nonneg_left hp hb
  linarith

theorem equalNormalCoefficient_le_one {m : ℕ} {b : ℝ} (hb : 0≤b)
    {p : Fin m → ℝ} (hp : ∀ j,0≤p j) : equalNormalCoefficient m b p≤1 := by
  unfold equalNormalCoefficient
  exact sub_le_self _ (mul_nonneg hb (Finset.sum_nonneg (fun j _ => hp j)))

theorem equalNormalCoefficient_uniform_limit {m : ℕ} {b d a : ℝ}
    (hb : 0≤b) (hbd : b*d<1) {P : Set (Fin m → ℝ)}
    (hP : ∀ p∈P,(∀ j,0≤p j) ∧ (∑ j,p j)≤d)
    {mass : ℕ → ℝ} (hmass : Tendsto mass atTop (𝓝 a)) :
    TendstoUniformlyOn (fun ℓ p => equalNormalCoefficient m b p * mass ℓ)
      (fun p => a * equalNormalCoefficient m b p) atTop P := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hm : ∀ᶠ ℓ in atTop,dist (mass ℓ) a<ε :=
    hmass.eventually (Metric.ball_mem_nhds a hε)
  filter_upwards [hm] with ℓ hℓ p hp
  have hc0 := equalNormalCoefficient_pos hb hbd (hP p hp).2
  have hc1 := equalNormalCoefficient_le_one hb (hP p hp).1
  rw [Real.dist_eq,show a*equalNormalCoefficient m b p-
    equalNormalCoefficient m b p*mass ℓ = equalNormalCoefficient m b p*(a-mass ℓ) by ring,
    abs_mul,abs_of_pos hc0]
  calc
    equalNormalCoefficient m b p * |a-mass ℓ| ≤ |a-mass ℓ| :=
      mul_le_of_le_one_left (abs_nonneg _) hc1
    _ < ε := by simpa only [Real.dist_eq,abs_sub_comm] using hℓ

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold MeasureTheory
open Hamiltonian

variable {m q : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 attribute [local instance] OAI.PackingSufficiencySupport.DiagonalQuadrics.instSigmaCompactSpaceElemAffineLocus_2
theorem normalHorizontalPrimitive_area_limit_bp240_oai {b d : ℝ} (hb : 0≤b) (hbd : b*d<1)
    {P : Set (Fin q → ℝ)} (hP : ∀ p∈P,(∀ j,0≤p j) ∧ (∑ j,p j)≤d) :
    TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral
      (projectionDomain_compact a (exhaustionRadius a ℓ))
      (fun x => equalNormalCoefficient q b p • curveFSForm a (1/Real.pi) x))
      (fun p => (2:ℝ)^m*equalNormalCoefficient q b p) atTop P := by
  have he p : (fun x => equalNormalCoefficient q b p • curveFSForm a (1/Real.pi) x)=
      equalNormalCoefficient q b p • curveFSForm a (1/Real.pi) := rfl
  simp_rw [he,compactSurfaceFormIntegral_smul]
  exact equalNormalCoefficient_uniform_limit hb hbd hP (tendsto_normalized_exhaustion_area a)

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.DiagonalQuadrics.normalHorizontalPrimitive_area_limit_bp240_oai := @OAI.PackingSufficiencySupport.DiagonalQuadrics.normalHorizontalPrimitive_area_limit_bp240_oai
