-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.hasPacking_dim_ge_four_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:27.395964+00:00
-- url     : https://prove2.me/submissions/f29214e8-8e81-4973-a1e9-0bd260a33313

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_actual_small_normal_packing_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_actual_normal_transfer_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_polynomial_target_embedding_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_thin_planar_embedding_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_actual_complement_packing_bp240

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

theorem polar_deriv_first (p : Plane) :
    fderiv ℝ polarCoord.symm p (1,0) = (Real.cos p.2,Real.sin p.2) := by
  rw [(hasFDerivAt_polarCoord_symm p).fderiv]
  simp [fderivPolarCoordSymm,Matrix.toLin_finTwoProd_toContinuousLinearMap]

theorem polar_deriv_second (p : Plane) :
    fderiv ℝ polarCoord.symm p (0,1) = (-p.1*Real.sin p.2,p.1*Real.cos p.2) := by
  rw [(hasFDerivAt_polarCoord_symm p).fderiv]
  simp [fderivPolarCoordSymm,Matrix.toLin_finTwoProd_toContinuousLinearMap]

theorem polar_area (p : Plane) :
    planarArea (fderiv ℝ polarCoord.symm p (1,0)) (fderiv ℝ polarCoord.symm p (0,1)) = p.1 := by
  rw [polar_deriv_first,polar_deriv_second,planarArea_apply]
  have ht := Real.cos_sq_add_sin_sq p.2
  dsimp
  linear_combination p.1 * ht

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ParametricMoser
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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
-- module Solutions.OAIQ240_BP.BallPacking_Moser_DiskMoser
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

 theorem planarArea_map (A : Plane →L[ℝ] Plane) (v w : Plane) :
    planarArea (A v) (A w) = A.det * planarArea v w := by
  have hd (u : Plane) : A u = u.1 • A (1,0) + u.2 • A (0,1) := by
    rw [← map_smul,← map_smul,← map_add]
    congr 1
    ext <;> simp
  rw [planar_det,hd v,hd w]
  simp only [planarArea_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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

theorem areaPolarRadial_smoothAt {p : Plane} (hp : 0 < p.1) :
    ContDiffAt ℝ ∞ areaPolarRadial p := by
  exact ((contDiffAt_fst.div_const Real.pi).sqrt (div_pos hp Real.pi_pos).ne').prodMk
    (contDiffAt_const.mul (contDiffAt_snd.sub contDiffAt_const))

theorem areaPolar_smoothAt {p : Plane} (hp : 0 < p.1) :
    ContDiffAt ℝ ∞ areaPolar p :=
  polar_smooth.contDiffAt.comp p (areaPolarRadial_smoothAt hp)

theorem areaPolarRadial_target {p : Plane} (hp : p ∈ areaPolarDomain) :
    areaPolarRadial p ∈ polarCoord.target := by
  change 0 < Real.sqrt (p.1/Real.pi) ∧
    -Real.pi < 2*Real.pi*(p.2-1/2) ∧ 2*Real.pi*(p.2-1/2) < Real.pi
  refine ⟨Real.sqrt_pos.mpr (div_pos hp.1 Real.pi_pos),?_,?_⟩
  · nlinarith [mul_pos Real.pi_pos hp.2.1]
  · nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hp.2.2)]

theorem areaPolar_injOn : InjOn areaPolar areaPolarDomain := by
  intro p hp q hq he
  have he' := polarCoord.symm.injOn (areaPolarRadial_target hp) (areaPolarRadial_target hq) he
  have ha := congrArg (fun x : Plane => x.1^2) he'
  have hb := congrArg Prod.snd he'
  change (Real.sqrt (p.1/Real.pi))^2 = (Real.sqrt (q.1/Real.pi))^2 at ha
  rw [Real.sq_sqrt (div_nonneg hp.1.le Real.pi_pos.le),
    Real.sq_sqrt (div_nonneg hq.1.le Real.pi_pos.le)] at ha
  change 2*Real.pi*(p.2-1/2) = 2*Real.pi*(q.2-1/2) at hb
  exact Prod.ext ((div_left_inj' Real.pi_ne_zero).mp ha)
    (by nlinarith [Real.pi_pos])

theorem areaPolarRadial_fderiv {p : Plane} (hp : 0 < p.1) (v : Plane) :
    fderiv ℝ areaPolarRadial p v =
      (v.1/(2*Real.pi*Real.sqrt (p.1/Real.pi)),2*Real.pi*v.2) := by
  have hq := ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul_const Real.pi⁻¹).sqrt
    (mul_pos hp (inv_pos.mpr Real.pi_pos)).ne'
  have ht := ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).sub_const (1/2:ℝ)).const_mul (2*Real.pi)
  change fderiv ℝ (fun q : Plane => (Real.sqrt (q.1/Real.pi),2*Real.pi*(q.2-1/2))) p v = _
  erw [(hq.prodMk ht).fderiv]
  ext <;> simp [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]

theorem areaPolar_det {p : Plane} (hp : 0 < p.1) : (fderiv ℝ areaPolar p).det = 1 := by
  have hr := Real.sqrt_pos.mpr (div_pos hp Real.pi_pos)
  have hd : (fderiv ℝ areaPolarRadial p).det =
      1/Real.sqrt (p.1/Real.pi) := by
    rw [planar_det,areaPolarRadial_fderiv hp,areaPolarRadial_fderiv hp,planarArea_apply]
    dsimp
    field_simp <;> norm_num
  have hdp : (fderiv ℝ polarCoord.symm (areaPolarRadial p)).det = Real.sqrt (p.1/Real.pi) := by
    rw [planar_det,polar_area]
    rfl
  change (fderiv ℝ (polarCoord.symm ∘ areaPolarRadial) p).det = _
  rw [fderiv_comp p (polar_smooth.differentiable (by simp) _)
    ((areaPolarRadial_smoothAt hp).differentiableAt (by simp)),
    ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
  change (fderiv ℝ polarCoord.symm (areaPolarRadial p)).det *
    (fderiv ℝ areaPolarRadial p).det = _
  rw [hdp,hd,mul_one_div_cancel hr.ne']

theorem areaPolar_capacity {p : Plane} (hp : 0 ≤ p.1) :
    Real.pi * radiusSq (areaPolar p) = p.1 := by
  have hs : (Real.sqrt (p.1/Real.pi))^2 = p.1/Real.pi :=
    Real.sq_sqrt (div_nonneg hp Real.pi_pos.le)
  have ht := Real.cos_sq_add_sin_sq (2*Real.pi*(p.2-1/2))
  change Real.pi * ((Real.sqrt (p.1/Real.pi)*Real.cos (2*Real.pi*(p.2-1/2)))^2+
    (Real.sqrt (p.1/Real.pi)*Real.sin (2*Real.pi*(p.2-1/2)))^2) = _
  calc
    _ = Real.pi*(Real.sqrt (p.1/Real.pi))^2 := by linear_combination Real.pi * (Real.sqrt (p.1/Real.pi))^2 * ht
    _ = p.1 := by rw [hs]; field_simp

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

theorem isBallEmbedding_id (n : ℕ) (r : ℝ) :
    IsBallEmbedding r (id : Ambient n → Ambient n) := by
  refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, contDiff_id.contDiffOn, ?_, ?_⟩
  · simpa only [id_eq] using (Topology.IsEmbedding.subtypeVal (p := fun x : Ambient n => x ∈ (Set.univ : Set (Ambient n))))
  · intro x _ v w
    simp

theorem matrix_J_pairing {n : ℕ} (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (i j : Fin n ⊕ Fin n) :
    (A.transpose * Matrix.J (Fin n) ℝ * A) i j =
      ∑ k, (A (Sum.inr k) i * A (Sum.inl k) j -
        A (Sum.inl k) i * A (Sum.inr k) j) := by
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Matrix.fromBlocks,
    Matrix.one_apply, Finset.sum_add_distrib, sub_eq_add_neg]

theorem det_eq_one_of_preserves_standardForm {n : ℕ}
    (L : Ambient n →ₗ[ℝ] Ambient n)
    (hL : ∀ v w, standardForm (L v) (L w) = standardForm v w) :
    LinearMap.det L = 1 := by
  let b := realBasis n
  let M := LinearMap.toMatrix b b L
  have pair (T : Ambient n →ₗ[ℝ] Ambient n) (i j : Fin n ⊕ Fin n) :
      ((LinearMap.toMatrix b b T).transpose * Matrix.J (Fin n) ℝ *
        LinearMap.toMatrix b b T) i j = - standardForm (T (b i)) (T (b j)) := by
    rw [matrix_J_pairing]
    simp only [LinearMap.toMatrix_apply, b, realBasis_repr]
    change (∑ k, ((T (realBasis n i) k).im * (T (realBasis n j) k).re -
      (T (realBasis n i) k).re * (T (realBasis n j) k).im)) =
      -(∑ k, ((T (realBasis n i) k).re * (T (realBasis n j) k).im -
        (T (realBasis n i) k).im * (T (realBasis n j) k).re))
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hM : M ∈ Matrix.symplecticGroup (Fin n) ℝ := by
    apply SymplecticGroup.mem_iff'.mpr
    ext i j
    change (M.transpose * Matrix.J (Fin n) ℝ * M) i j = _
    rw [show (M.transpose * Matrix.J (Fin n) ℝ * M) i j =
      -standardForm (L (b i)) (L (b j)) from pair L i j, hL]
    simpa using (pair LinearMap.id i j).symm
  rw [← LinearMap.det_toMatrix b L]
  exact SymplecticGroup.det_eq_one hM

theorem closedBall_isClosed (n : ℕ) (R : ℝ) : IsClosed (closedBall n R) :=
  isClosed_le (continuous_capacity n) continuous_const

theorem openBall_isOpen (n : ℕ) (R : ℝ) : IsOpen (openBall n R) :=
  isOpen_lt (continuous_capacity n) continuous_const

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

theorem IsBallEmbedding.volume_image {n : ℕ} {r : ℝ}
    {f : Ambient n → Ambient n} (hf : IsBallEmbedding r f) :
    volume (f '' closedBall n r) = volume (closedBall n r) := by
  rcases hf with ⟨U, hU, hsub, hsmooth, hembed, hform⟩
  have hdiff : ∀ x ∈ closedBall n r,
      HasFDerivWithinAt f (fderiv ℝ f x) (closedBall n r) x := by
    intro x hx
    exact ((hsmooth.differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds (hsub hx))).hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn f (closedBall n r) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hembed.injective
      (show f (⟨x, hsub hx⟩ : U) = f (⟨y, hsub hy⟩ : U) from hxy))
  have hs := (closedBall_isClosed n r).measurableSet
  calc
    volume (f '' closedBall n r) = ∫⁻ x in closedBall n r,
        ENNReal.ofReal |(fderiv ℝ f x).det| :=
      (lintegral_abs_det_fderiv_eq_addHaar_image volume hs hdiff hinj).symm
    _ = ∫⁻ _ in closedBall n r, (1 : ℝ≥0∞) := by
      apply setLIntegral_congr_fun hs
      intro x hx
      have hd := det_eq_one_of_preserves_standardForm (fderiv ℝ f x).toLinearMap
        (hform x (hsub hx))
      simp [show (fderiv ℝ f x).det = 1 from hd]
    _ = volume (closedBall n r) := by simp

theorem capacity_smul {n : ℕ} (t : ℝ) (z : Ambient n) :
    capacity (t • z) = t ^ 2 * capacity z := by
  simp only [capacity, Pi.smul_apply, Complex.normSq_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, ← Finset.mul_sum]
  ring

theorem closedBall_eq_smul {n : ℕ} {r : ℝ} (hr : 0 < r) :
    closedBall n r = Real.sqrt r • closedBall n 1 := by
  ext z
  constructor
  · intro hz
    refine ⟨(Real.sqrt r)⁻¹ • z, ?_, ?_⟩
    · change capacity ((Real.sqrt r)⁻¹ • z) ≤ 1
      rw [capacity_smul, inv_pow, Real.sq_sqrt hr.le, ← div_eq_inv_mul,
        div_le_iff₀ hr]
      simpa [closedBall] using hz
    · simp [smul_smul, ne_of_gt (Real.sqrt_pos.mpr hr)]
  · rintro ⟨w, hw, rfl⟩
    change capacity (Real.sqrt r • w) ≤ r
    rw [capacity_smul, Real.sq_sqrt hr.le]
    simpa using mul_le_mul_of_nonneg_left hw hr.le

theorem volume_closedBall {n : ℕ} {r : ℝ} (hr : 0 < r) :
    volume (closedBall n r) = ENNReal.ofReal (r ^ n) * volume (closedBall n 1) := by
  rw [closedBall_eq_smul hr, Measure.addHaar_smul]
  have hd : Module.finrank ℝ (Ambient n) = 2 * n := by
    simp [Ambient, Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  rw [hd, pow_mul, Real.sq_sqrt hr.le, abs_of_pos (pow_pos hr n)]

theorem capacity_nonneg {n : ℕ} (z : Ambient n) : 0 ≤ capacity z :=
  mul_nonneg Real.pi_pos.le (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (z j))

theorem unitBall_volume_pos (n : ℕ) : 0 < volume (closedBall n 1) := by
  have hp : 0 < volume (openBall n 1) :=
    (openBall_isOpen n 1).measure_pos volume ⟨0, by simp [openBall]⟩
  exact hp.trans_le (measure_mono (fun _ hx => (show capacity _ < 1 from hx).le))

theorem unitBall_volume_ne_top (n : ℕ) : volume (closedBall n 1) ≠ ⊤ :=
  (closedBall_isCompact n 1).measure_lt_top.ne

theorem IsBallEmbedding.closedBall_continuousOn {n : ℕ} {r : ℝ}
    {f : Ambient n → Ambient n} (hf : IsBallEmbedding r f) :
    ContinuousOn f (closedBall n r) := by
  rcases hf with ⟨U, _, hsub, hsmooth, _, _⟩
  exact hsmooth.continuousOn.mono hsub

theorem IsBallEmbedding.isCompact_image {n : ℕ} {r : ℝ}
    {f : Ambient n → Ambient n} (hf : IsBallEmbedding r f) :
    IsCompact (f '' closedBall n r) :=
  (closedBall_isCompact n r).image_of_continuousOn hf.closedBall_continuousOn

theorem HasPacking.exists_smaller_target {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hR : 0 < R) (hp : HasPacking n k R r) :
    ∃ σ, 0 < σ ∧ σ < R ∧ HasPacking n k σ r := by
  rcases hp with ⟨f, hf, htarget, hdisj⟩
  let S : Set (Ambient n) := ⋃ i, f i '' closedBall n (r i)
  have hc : IsCompact (insert 0 S) :=
    (isCompact_iUnion (fun i => (hf i).isCompact_image)).insert 0
  obtain ⟨z, hz, hmax⟩ := hc.exists_isMaxOn (Set.insert_nonempty 0 S)
    (continuous_capacity n).continuousOn
  have hS : insert (0 : Ambient n) S ⊆ openBall n R := by
    intro y hy
    rcases hy with rfl | hy
    · simpa [openBall] using hR
    · rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
      exact htarget i hi
  have hzR : capacity z < R := hS hz
  refine ⟨(capacity z + R) / 2, ?_, ?_, f, hf, ?_, hdisj⟩
  · linarith [capacity_nonneg z]
  · linarith
  · intro i y hy
    have hm : capacity y ≤ capacity z := hmax (Set.mem_insert_of_mem 0
      (Set.mem_iUnion.mpr ⟨i, hy⟩))
    change capacity y < (capacity z + R) / 2
    linarith

theorem HasPacking.volume_le {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hR : 0 < R) (hr : ∀ i, 0 < r i) (hp : HasPacking n k R r) :
    ∑ i, (r i) ^ n ≤ R ^ n := by
  rcases hp with ⟨f, hf, htarget, hdisj⟩
  have hm : volume (⋃ i, f i '' closedBall n (r i)) ≤ volume (closedBall n R) := by
    apply measure_mono
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    exact (show capacity z < R from htarget i hi).le
  rw [measure_iUnion hdisj (fun i => (hf i).isCompact_image.measurableSet),
    tsum_fintype] at hm
  simp_rw [(hf _).volume_image, volume_closedBall (hr _)] at hm
  rw [volume_closedBall hR, ← Finset.sum_mul] at hm
  have he := (ENNReal.mul_le_mul_iff_left (unitBall_volume_pos n).ne'
    (unitBall_volume_ne_top n)).mp hm
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg (hr i).le n)] at he
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hR.le n)).mp he

theorem HasPacking.volume_lt {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hn : 0 < n) (hR : 0 < R) (hr : ∀ i, 0 < r i)
    (hp : HasPacking n k R r) : ∑ i, (r i) ^ n < R ^ n := by
  obtain ⟨σ, hσ, hσR, hpσ⟩ := hp.exists_smaller_target hR
  exact (hpσ.volume_le hσ hr).trans_lt (pow_lt_pow_left₀ hσR hσ.le hn.ne')

theorem IsBallEmbedding.dilate {n : ℕ} {r t : ℝ} {f : Ambient n → Ambient n}
    (hf : IsBallEmbedding r f) (ht : t ≠ 0) :
    IsBallEmbedding (t ^ 2 * r) (fun z => t • f (t⁻¹ • z)) := by
  let e := dilation n t ht
  rcases hf with ⟨U, hU, hsub, hsmooth, hembed, hform⟩
  have hmaps : Set.MapsTo e.symm (e '' U) U := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  refine ⟨e '' U, e.isOpenMap _ hU, ?_, ?_, ?_, ?_⟩
  · intro z hz
    refine ⟨e.symm z, hsub ?_, e.apply_symm_apply z⟩
    change capacity (t⁻¹ • z) ≤ r
    rw [capacity_smul, inv_pow, ← div_eq_inv_mul, div_le_iff₀ (sq_pos_of_ne_zero ht)]
    simpa [closedBall, mul_comm] using hz
  · exact (hsmooth.comp e.symm.contDiff.contDiffOn hmaps).const_smul t
  · exact e.toHomeomorph.isEmbedding.comp (hembed.comp (e.toHomeomorph.image U).symm.isEmbedding)
  · intro z hz v w
    have hd := ((hsmooth.differentiableOn (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
      (hU.mem_nhds (hmaps hz))).hasFDerivAt
    have hchain := (e.hasFDerivAt.comp z (hd.comp z e.symm.hasFDerivAt))
    have heq : e.toContinuousLinearMap.comp
        ((fderiv ℝ f (e.symm z)).comp e.symm.toContinuousLinearMap) =
        fderiv ℝ f (e.symm z) := by
      apply ContinuousLinearMap.ext
      intro a
      change t • (fderiv ℝ f (e.symm z) (t⁻¹ • a)) = _
      rw [map_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]
    rw [heq] at hchain
    have hdg : fderiv ℝ (fun z => t • f (t⁻¹ • z)) z = fderiv ℝ f (e.symm z) :=
      hchain.fderiv
    rw [hdg]
    exact hform _ (hmaps hz) v w

theorem HasPacking.dilate {n k : ℕ} {R t : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) (ht : t ≠ 0) :
    HasPacking n k (t ^ 2 * R) (fun i => t ^ 2 * r i) := by
  rcases hp with ⟨f, hf, htarget, hdisj⟩
  have hsource {a : ℝ} {z : Ambient n} (hz : z ∈ closedBall n (t ^ 2 * a)) :
      t⁻¹ • z ∈ closedBall n a := by
    change capacity (t⁻¹ • z) ≤ a
    rw [capacity_smul, inv_pow, ← div_eq_inv_mul, div_le_iff₀ (sq_pos_of_ne_zero ht)]
    simpa [closedBall, mul_comm] using hz
  refine ⟨fun i z => t • f i (t⁻¹ • z), fun i => (hf i).dilate ht, ?_, ?_⟩
  · intro i z hz
    rcases hz with ⟨x, hx, rfl⟩
    change capacity (t • f i (t⁻¹ • x)) < t ^ 2 * R
    rw [capacity_smul]
    exact mul_lt_mul_of_pos_left (htarget i ⟨_, hsource hx, rfl⟩) (sq_pos_of_ne_zero ht)
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have heq' : f j (t⁻¹ • y) = f i (t⁻¹ • x) := by
      have := congrArg (fun z : Ambient n => t⁻¹ • z) heq
      simpa [smul_smul, ht] using this
    exact Set.disjoint_left.mp (hdisj i j hij)
      ⟨_, hsource hx, rfl⟩ ⟨_, hsource hy, heq'⟩

theorem hasPacking_normalize {n k : ℕ} {R : ℝ} {r : Fin k → ℝ} (hR : 0 < R) :
    HasPacking n k R r ↔ HasPacking n k 1 (fun i => r i / R) := by
  constructor
  · intro hp
    have ht : Real.sqrt R⁻¹ ≠ 0 := (Real.sqrt_pos.mpr (inv_pos.mpr hR)).ne'
    have h := hp.dilate ht
    simpa only [Real.sq_sqrt (inv_nonneg.mpr hR.le), inv_mul_cancel₀ hR.ne',
      div_eq_inv_mul] using h
  · intro hp
    have ht : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
    have h := hp.dilate ht
    simpa only [Real.sq_sqrt hR.le, mul_one, mul_div_cancel₀ _ hR.ne'] using h

theorem hasPacking_one_iff {n : ℕ} {R r : ℝ} (hn : 0 < n)
    (hR : 0 < R) (hr : 0 < r) :
    HasPacking n 1 R (fun _ => r) ↔ r < R := by
  constructor
  · intro hp
    have h := hp.volume_lt hn hR (fun _ => hr)
    simp only [Fin.sum_univ_one] at h
    exact lt_of_pow_lt_pow_left₀ n hR.le h
  · intro h
    refine ⟨fun _ => id, fun _ => isBallEmbedding_id n r, ?_, ?_⟩
    · intro i z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact lt_of_le_of_lt hx h
    · intro i j hij
      exact False.elim (hij (Subsingleton.elim i j))

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
-- module Solutions.OAIQ240_BP.BallPacking_Models_RationalSlack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped BigOperators
open Set
open scoped Pointwise
open MeasureTheory

theorem exists_rational_above_in_open {ι : Type*} [Fintype ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) {r : ι → ℝ} (hr : r ∈ U) :
    ∃ q : ι → ℚ, (∀ i, r i < q i) ∧ (fun i => (q i : ℝ)) ∈ U := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.1 hU r hr
  have hinterval (i : ι) : ∃ q : ℚ, r i < q ∧ (q : ℝ) < r i+ε/2 :=
    exists_rat_btwn (by linarith)
  choose q hlo hhi using hinterval
  refine ⟨q,hlo,hball ?_⟩
  rw [Metric.mem_ball]
  apply (dist_pi_lt_iff hε).2
  intro i
  rw [Real.dist_eq,abs_of_pos (sub_pos.mpr (hlo i))]
  linarith [hhi i]

theorem rational_small_slack {ι : Type*} [Fintype ι] (n : ℕ) (r : ι → ℝ)
    (hhalf : ∀ i, r i < 1/2) (hvol : ∑ i,r i^n < 1) :
    ∃ q : ι → ℚ, (∀ i, r i < q i) ∧ (∀ i, (q i : ℝ) < 1/2) ∧
      ∑ i,(q i : ℝ)^n < 1 := by
  let U : Set (ι → ℝ) := {s | (∀ i,s i<1/2) ∧ ∑ i,s i^n<1}
  have hU : IsOpen U := by
    have ha : IsOpen {s : ι → ℝ | ∀ i,s i<1/2} := by
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
    exact ha.inter (isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).pow n)
      continuous_const)
  obtain ⟨q,hq,hUq⟩ := exists_rational_above_in_open hU (show r∈U from ⟨hhalf,hvol⟩)
  exact ⟨q,hq,hUq⟩

theorem rational_packing_slack {ι : Type*} [Fintype ι] (n : ℕ) (R : ℝ) (r : ι → ℝ)
    (hvol : ∑ i,r i^n < R^n) (hpair : ∀ i j, i≠j → r i+r j<R) :
    ∃ q : ι → ℚ, (∀ i,r i<q i) ∧ (∑ i,(q i:ℝ)^n)<R^n ∧
      ∀ i j, i≠j → (q i:ℝ)+(q j:ℝ)<R := by
  let U : Set (ι → ℝ) := {s | (∑ i,s i^n)<R^n ∧ ∀ i j,i≠j → s i+s j<R}
  have hpairOpen : IsOpen {s : ι → ℝ | ∀ i j,i≠j → s i+s j<R} := by
    simp only [ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    refine isOpen_iInter_of_finite fun _h => ?_
    exact isOpen_lt ((continuous_apply i).add (continuous_apply j)) continuous_const
  have hU : IsOpen U := (isOpen_lt
    (continuous_finsetSum _ fun i _ => (continuous_apply i).pow n) continuous_const).inter hpairOpen
  obtain ⟨q,hq,hUq⟩ := exists_rational_above_in_open hU (show r∈U from ⟨hvol,hpair⟩)
  exact ⟨q,hq,hUq⟩

end PackingSufficiencySupport

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

end PackingSufficiencySupport.Hamiltonian

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

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

 theorem exists_shifted_planar_embedding {A δ b : ℝ} (hA : 0≤A) (hδ : 0<δ) (hb : 0≤b) :
    ∃ p : Plane → Plane,
      (∀ x,radialArea x≤A → ContDiffAt ℝ ∞ p x) ∧
      InjOn p {x | radialArea x≤A} ∧
      (∀ x,radialArea x≤A → ∀ v w,
        planarArea (fderiv ℝ p x v) (fderiv ℝ p x w)=planarArea v w) ∧
      ∀ x,radialArea x≤A → b < radialArea (p x) ∧ radialArea (p x) < radialArea x+b+δ := by
  obtain ⟨q,hq,_hqi,hqform,hqbound⟩ := exists_thin_planar_embedding_bp240 hA hδ
  let l : Plane → Plane := fun x => q x+(b,0)
  have hl : ContDiff ℝ ∞ l := hq.add contDiff_const
  have hlD (x v : Plane) : fderiv ℝ l x v=fderiv ℝ q x v := by
    rw [show l=(fun x => q x+(b,0)) from rfl,fderiv_add_const]
  let p : Plane → Plane := areaPolar ∘ l
  have hldom {x : Plane} (hx : radialArea x≤A) : l x∈areaPolarDomain := by
    obtain ⟨hx0,_hxu,hxθ⟩ := hqbound x hx
    exact ⟨by change 0<(q x).1+b; linarith,by simpa only [l,Prod.snd_add,add_zero] using hxθ⟩
  refine ⟨p,fun x hx => (areaPolar_smoothAt (hldom hx).1).comp x hl.contDiffAt,?_,?_,?_⟩
  · intro x hx y hy he
    have hh := areaPolar_injOn (hldom hx) (hldom hy) he
    exact q.injective (add_right_cancel hh)
  · intro x hx v w
    rw [show p=areaPolar ∘ l from rfl,
      fderiv_comp x ((areaPolar_smoothAt (hldom hx).1).differentiableAt (by simp))
        (hl.differentiable (by simp) x)]
    change planarArea (fderiv ℝ areaPolar (l x) (fderiv ℝ l x v))
      (fderiv ℝ areaPolar (l x) (fderiv ℝ l x w))=_
    rw [planarArea_map,areaPolar_det (hldom hx).1,one_mul,hlD,hlD,hqform]
  · intro x hx
    have hc : radialArea (p x)=(q x).1+b := areaPolar_capacity (hldom hx).1.le
    rw [hc]
    obtain ⟨hq0,hqδ,_⟩ := hqbound x hx
    constructor <;> linarith

 theorem headComplexAmbient_split_capacity (n : ℕ) (x : Ambient (n+1)) :
    capacity ((headComplexAmbient n).symm x).1+radialArea ((headComplexAmbient n).symm x).2=capacity x := by
  rw [← headComplexAmbient_capacity,(headComplexAmbient n).apply_symm_apply]

 theorem headComplexAmbient_head_le {n : ℕ} {A : ℝ} {x : Ambient (n+1)}
    (hx : x∈closedBall (n+1) A) : radialArea ((headComplexAmbient n).symm x).2≤A := by
  have hc := capacity_nonneg ((headComplexAmbient n).symm x).1
  have hs := headComplexAmbient_split_capacity n x
  change capacity x≤A at hx
  linarith

 theorem headPlanarMap_capacity (n : ℕ) (p : Plane → Plane) (x : Ambient (n+1)) :
    capacity (headPlanarMap n p x)=
      capacity ((headComplexAmbient n).symm x).1+radialArea (p ((headComplexAmbient n).symm x).2) :=
  headComplexAmbient_capacity n _

 theorem headPlanarMap_first (n : ℕ) (p : Plane → Plane) (x : Ambient (n+1)) :
    Real.pi*Complex.normSq (headPlanarMap n p x 0)=radialArea (p ((headComplexAmbient n).symm x).2) := by
  change Real.pi*Complex.normSq (⟨(p ((headComplexAmbient n).symm x).2).1,
    (p ((headComplexAmbient n).symm x).2).2⟩ : ℂ)=_
  simp only [Complex.normSq_apply,radialArea,radiusSq,pow_two]

 theorem headPlanarMap_smoothAt {n : ℕ} {p : Plane → Plane} {x : Ambient (n+1)}
    (hp : ContDiffAt ℝ ∞ p ((headComplexAmbient n).symm x).2) :
    ContDiffAt ℝ ∞ (headPlanarMap n p) x :=
  (headComplexAmbient n).contDiff.contDiffAt.comp _
    ((contDiffAt_fst.prodMk (hp.comp _ contDiffAt_snd)).comp x
      (headComplexAmbient n).symm.contDiff.contDiffAt)

 theorem headPlanarMap_fderiv {n : ℕ} {p : Plane → Plane} {x : Ambient (n+1)}
    (hp : ContDiffAt ℝ ∞ p ((headComplexAmbient n).symm x).2) (v : Ambient (n+1)) :
    fderiv ℝ (headPlanarMap n p) x v=headComplexAmbient n
      (((headComplexAmbient n).symm v).1,
        fderiv ℝ p ((headComplexAmbient n).symm x).2 ((headComplexAmbient n).symm v).2) := by
  let e := headComplexAmbient n
  have hdF := (hasFDerivAt_fst (𝕜 := ℝ) (p := e.symm x)).prodMk
    ((hp.differentiableAt (by simp)).hasFDerivAt.comp _ (hasFDerivAt_snd (𝕜 := ℝ) (p := e.symm x)))
  have hdf := e.hasFDerivAt.comp x (hdF.comp x e.symm.hasFDerivAt)
  change HasFDerivAt (headPlanarMap n p) _ x at hdf
  rw [hdf.fderiv]
  rfl

 theorem headPlanarMap_injOn {n : ℕ} {p : Plane → Plane} {A : ℝ}
    (hp : InjOn p {x | radialArea x≤A}) : InjOn (headPlanarMap n p) (closedBall (n+1) A) := by
  intro x hx y hy he
  let e := headComplexAmbient n
  have hF : ((e.symm x).1,p (e.symm x).2)=((e.symm y).1,p (e.symm y).2) := e.injective he
  have hfst := congrArg (fun z : Ambient n × Plane => z.1) hF
  have hsnd := congrArg (fun z : Ambient n × Plane => z.2) hF
  apply e.symm.injective
  exact Prod.ext hfst (hp (headComplexAmbient_head_le hx) (headComplexAmbient_head_le hy) hsnd)

 theorem headPlanarMap_form {n : ℕ} {p : Plane → Plane} {x : Ambient (n+1)}
    (hp : ContDiffAt ℝ ∞ p ((headComplexAmbient n).symm x).2)
    (hf : ∀ v w,planarArea (fderiv ℝ p ((headComplexAmbient n).symm x).2 v)
      (fderiv ℝ p ((headComplexAmbient n).symm x).2 w)=planarArea v w) (v w : Ambient (n+1)) :
    standardForm (fderiv ℝ (headPlanarMap n p) x v) (fderiv ℝ (headPlanarMap n p) x w)=standardForm v w := by
  rw [headPlanarMap_fderiv hp,headPlanarMap_fderiv hp,headComplexAmbient_form,hf]
  change standardForm ((headComplexAmbient n).symm v).1 ((headComplexAmbient n).symm w).1+
    planarArea ((headComplexAmbient n).symm v).2 ((headComplexAmbient n).symm w).2=_
  rw [← headComplexAmbient_form]
  simp only [(headComplexAmbient n).apply_symm_apply]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport
open scoped ContDiff Topology
open Set Function
open Hamiltonian

 theorem exists_distinguished_ball_embedding (n : ℕ) {A b : ℝ}
    (hA : 0≤A) (hb : 0≤b) (hAb : A+b<1) :
    ∃ f : Ambient (n+1) → Ambient (n+1),IsBallEmbedding A f ∧
      f '' closedBall (n+1) A ⊆ openBall (n+1) 1 ∧
      ∀ x∈closedBall (n+1) A,b<Real.pi*Complex.normSq (f x 0) := by
  obtain ⟨A',hAA',hA'b⟩ := exists_between (show A<1-b by linarith)
  obtain ⟨δ,hδ,hδb⟩ := exists_between (show (0:ℝ)<1-b-A' by linarith)
  obtain ⟨p,hp,hpInj,hpform,hpcap⟩ := exists_shifted_planar_embedding (hA.trans hAA'.le) hδ hb
  let f := headPlanarMap n p
  have hf {x : Ambient (n+1)} (hx : x∈closedBall (n+1) A') : ContDiffAt ℝ ∞ f x :=
    headPlanarMap_smoothAt (hp _ (headComplexAmbient_head_le hx))
  have hfemb : Topology.IsEmbedding (fun x : closedBall (n+1) A' => f x.val) := by
    let : CompactSpace (closedBall (n+1) A') := isCompact_iff_compactSpace.mp (closedBall_isCompact _ _)
    have hc : ContinuousOn f (closedBall (n+1) A') := fun x hx => (hf hx).continuousAt.continuousWithinAt
    exact (hc.domRestrict.isClosedEmbedding (fun x y he =>
      Subtype.ext (headPlanarMap_injOn hpInj x.property y.property he))).isEmbedding
  refine ⟨f,⟨openBall (n+1) A',openBall_isOpen _ _,?_,?_,?_,?_⟩,?_,?_⟩
  · intro x hx
    exact (show capacity x≤A from hx).trans_lt hAA'
  · intro x hx
    exact (hf (show capacity x≤A' from le_of_lt hx)).contDiffWithinAt
  · exact hfemb.comp (Topology.IsEmbedding.inclusion (fun x hx => (show capacity x<A' from hx).le))
  · intro x hx v w
    have hh := headComplexAmbient_head_le (show capacity x≤A' from (show capacity x<A' from hx).le)
    exact headPlanarMap_form (hp _ hh) (hpform _ hh) v w
  · rintro y ⟨x,hx,rfl⟩
    have hx' : x∈closedBall (n+1) A' := (show capacity x≤A from hx).trans hAA'.le
    change capacity (headPlanarMap n p x)<1
    rw [headPlanarMap_capacity]
    have hbq := (hpcap _ (headComplexAmbient_head_le hx')).2
    have hs := headComplexAmbient_split_capacity n x
    change capacity x≤A at hx
    linarith
  · intro x hx
    have hx' : x∈closedBall (n+1) A' := (show capacity x≤A from hx).trans hAA'.le
    change b<Real.pi*Complex.normSq (headPlanarMap n p x 0)
    rw [headPlanarMap_first]
    exact (hpcap _ (headComplexAmbient_head_le hx')).1

end PackingSufficiencySupport

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open Hamiltonian MomentPolytope

 theorem actual_small_polynomial_packing (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+3)<1) :
    ∃ d t : ℝ,0<d ∧ d<1/2 ∧ 0<t ∧
      ∃ f : Fin N → Ambient (m+3) → Affine (m+2),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+3) (r' i))
          (fun _ => successorStandardForm (m+2))
          (normalAmbientForm (parameters m) (1/Real.pi) d t) (f i)) ∧
        Pairwise (fun i j => Disjoint (f i '' closedBall (m+3) (r' i))
          (f j '' closedBall (m+3) (r' j))) := by
  classical
  obtain ⟨h,d,hrh,hhd,hdhalf,ℓ,φ,hφ,hφK,hdisj⟩ :=
    actual_small_normal_packing_bp240 m r r' hr hr' hrr hhalf hvol
  let K : Set (NormalSpace (parameters m)) := ⋃ i,φ i '' closedBall (m+3) (r' i)
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hφ i
    exact (closedBall_isCompact (m+3) (r' i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hhdR : (h:ℝ)<d := by exact_mod_cast hhd
  have hd : 0<(d:ℝ) := by
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    exact ((hr i).trans (hrh i)).trans hhdR
  have hKd (p : NormalSpace (parameters m)) (hp : p∈K) : phaseSq p.2<(d:ℝ)/Real.pi := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    have hm := (interior_subset (hφK i hx)).2.2
    have he : (∑ j,planeMoments (φ i x).2 j)=Real.pi*phaseSq (φ i x).2 := by
      simp only [planeMoments,radialArea,radiusSq,phaseSq,phaseDot_apply,pow_two,← Finset.mul_sum]
    rw [he] at hm
    exact (lt_div_iff₀ Real.pi_pos).mpr (by simpa only [mul_comm] using hm.trans_lt hhdR)
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,hgform⟩ :=
    exists_actual_normal_transfer_bp240 (parameters m) hd hdhalf hK hKd
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall (m+3) (r' i))
    (fun _ => successorStandardForm (m+2))
    (globalHorizontalCoupling phaseArea (normalHorizontalPrimitive (parameters m) 2 ∘ planeMoments))
    (normalAmbientForm (parameters m) (1/Real.pi) d t)
    hW g hg.contMDiffOn hgemb hgform φ hφ
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hdisj
  exact ⟨d,t,hd,hdhalf,ht,fun i => g ∘ φ i,hf,hdj⟩

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open Hamiltonian DiagonalQuadrics DiagonalQuadrics.Explicit
open CubicModel

 theorem hasPacking_small_enlarged (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+3)<1) : HasPacking (m+3) N 1 r' := by
  obtain ⟨d,t,hd,hdhalf,_ht,φ,hφ,hdisj⟩ :=
    actual_small_polynomial_packing m r r' hr hr' hrr hhalf hvol
  obtain ⟨g,hg,hgemb,hgmem,hgform⟩ :=
    exists_polynomial_target_embedding_bp240 (parameters m) t
      (one_div_pos.mpr Real.pi_pos) hd.le hdhalf
  have hform (x : Affine (m+2)) (_hx : x∈(univ : Set (Affine (m+2)))) (v w) :
      successorStandardForm (m+2) (mfderiv 𝓘(ℝ,Affine (m+2)) 𝓘(ℝ,Ambient (m+3)) g x v)
        (mfderiv 𝓘(ℝ,Affine (m+2)) 𝓘(ℝ,Ambient (m+3)) g x w)=
      normalAmbientForm (parameters m) (1/Real.pi) d t x v w := by
    rw [mfderiv_eq_fderiv]
    exact (successorStandardForm_apply _ _ _).trans (hgform x v w)
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall (m+3) (r' i))
    (fun _ => successorStandardForm (m+2))
    (normalAmbientForm (parameters m) (1/Real.pi) d t)
    (fun _ => successorStandardForm (m+2)) isOpen_univ g hg.contMDiff.contMDiffOn
    (hgemb.comp Topology.IsEmbedding.subtypeVal) hform φ hφ
    (fun _ _ _ => mem_univ _) hdisj
  refine ⟨fun i => g ∘ φ i,fun i => isBallEmbedding_iff_formNeighborhoodEmbedding.mpr (hf i),?_,?_⟩
  · intro i y hy
    obtain ⟨x,_hx,rfl⟩ := hy
    simpa only [mul_one_div_cancel Real.pi_ne_zero,Function.comp_apply] using hgmem (φ i x)
  · intro i j hij
    exact hdj hij

 theorem hasPacking_small_normalized {n N : ℕ} (hn : 3≤n) (hN : 1≤N)
    (r : Fin N → ℝ) (hr : ∀ i,0 < r i) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^n<1) : HasPacking n N 1 r := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  have hs : 3+m=m+3 := Nat.add_comm _ _
  simp only [hs] at hvol ⊢
  let : NeZero N := ⟨by omega⟩
  obtain ⟨q,hq,hqhalf,hqvol⟩ := rational_small_slack (m+3) r hhalf hvol
  exact hasPacking_small_enlarged m (fun i => (q i:ℝ)) r
    (fun i => (hr i).trans (hq i)) (fun i => (hr i).le) hq hqhalf hqvol

 theorem hasPacking_large_enlarged (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin (N+1) → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) (hlarge : 1/2 ≤ r 0)
    (hvol : ∑ i,r i^(m+4)<1) (hpair : ∀ i j,i≠j → r i+r j<1) :
    HasPacking (m+4) (N+1) 1 r' := by
  have ha : r 0<1 := by
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    have hp := hpair 0 i.succ (Fin.succ_ne_zero i).symm
    linarith [hr i.succ]
  have htail (i : Fin N) : r i.succ<1-r 0 := by
    have := hpair 0 i.succ (Fin.succ_ne_zero i).symm
    linarith
  have htvol : ∑ i : Fin N,r i.succ^(m+4)<1-r 0^(m+4) := by
    rw [Fin.sum_univ_succ] at hvol
    linarith
  obtain ⟨b,hb,f,hf,hfmem,hfb,hfd⟩ := actual_complement_packing_bp240 m
    (fun i => r i.succ) (fun i => r' i.succ) (fun i => hr i.succ)
    (fun i => hr' i.succ) (fun i => hrr i.succ) (hr 0) ha htail
    (fun i => by linarith [htail i]) htvol
  have hb0 : 0≤b := by
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    have hzero : (0 : Ambient (m+4))∈closedBall (m+4) (r' i.succ) := by
      simpa only [closedBall,mem_ofPred_eq,capacity,Pi.zero_apply,Complex.normSq_zero,
        Finset.sum_const_zero,mul_zero] using hr' i.succ
    have h := hfb i 0 hzero
    exact (mul_nonneg Real.pi_pos.le (Complex.normSq_nonneg _)).trans h.le
  obtain ⟨g,hg,hgmem,hgb⟩ := exists_distinguished_ball_embedding (m+3) (hr' 0) hb0
    (by linarith [hrr 0])
  let F : Fin (N+1) → Ambient (m+4) → Ambient (m+4) := Fin.cons g f
  refine ⟨F,?_,?_,?_⟩
  · intro i
    exact Fin.cases hg hf i
  · intro i
    exact Fin.cases hgmem hfmem i
  · have hgf (i : Fin N) : Disjoint (g '' closedBall (m+4) (r' 0))
        (f i '' closedBall (m+4) (r' i.succ)) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨x,hx,rfl⟩ ⟨z,hz,he⟩
      have hl := hgb x hx
      have hu := hfb i z hz
      rw [he] at hu
      exact (not_lt_of_ge hl.le) hu
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j _ => hgf j) j
      intro hij
      exact False.elim (hij rfl)
    · intro j
      refine Fin.cases (fun _ => Disjoint.symm (hgf i)) (fun j hij => ?_) j
      apply hfd
      intro he
      exact hij (congrArg Fin.succ he)

 theorem HasPacking.reindex {n N : ℕ} {R : ℝ} {r : Fin N → ℝ}
    (hp : HasPacking n N R r) (e : Equiv.Perm (Fin N)) :
    HasPacking n N R (r ∘ e) := by
  obtain ⟨f,hf,hm,hd⟩ := hp
  exact ⟨f ∘ e,fun i => hf (e i),fun i => hm (e i),
    fun i j hij => hd (e i) (e j) (fun h => hij (e.injective h))⟩

 theorem hasPacking_large_normalized (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r : Fin (N+1) → ℝ) (hr : ∀ i,0 < r i) (hlarge : 1/2 ≤ r 0)
    (hvol : ∑ i,r i^(m+4)<1) (hpair : ∀ i j,i≠j → r i+r j<1) :
    HasPacking (m+4) (N+1) 1 r := by
  obtain ⟨q,hq,hqvol,hqpair⟩ := rational_packing_slack (m+4) 1 r (by simpa using hvol) hpair
  exact hasPacking_large_enlarged m (fun i => (q i:ℝ)) r (fun i => (hr i).trans (hq i))
    (fun i => (hr i).le) hq (hlarge.trans (hq 0).le) (by simpa using hqvol) hqpair

 theorem hasPacking_dim_ge_four_normalized {n N : ℕ} (hn : 4≤n) (hN : 1≤N)
    (r : Fin N → ℝ) (hr : ∀ i,0 < r i)
    (hvol : ∑ i,r i^n<1) (hpair : ∀ i j,i≠j → r i+r j<1) : HasPacking n N 1 r := by
  classical
  by_cases hsmall : ∀ i,r i<1/2
  · exact hasPacking_small_normalized (by omega) hN r hr hsmall hvol
  obtain ⟨j,hj⟩ := not_forall.mp hsmall
  have hj : 1/2 ≤ r j := le_of_not_gt hj
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n=m+4 := by omega
  clear hm
  subst n
  cases N with
  | zero => omega
  | succ K =>
    cases K with
    | zero =>
      have heqr : r=(fun _ => r 0) := funext fun i => congrArg r (Fin.eq_zero i)
      rw [heqr] at hvol ⊢
      apply (hasPacking_one_iff (by omega) zero_lt_one (hr 0)).mpr
      exact lt_of_pow_lt_pow_left₀ (m+4) zero_le_one (by simpa using hvol)
    | succ K =>
      let e : Equiv.Perm (Fin (K+1+1)) := Equiv.swap 0 j
      have hrvol : ∑ i,(r (e i))^(m+4)<1 := by
        rw [show (∑ i,r (e i)^(m+4))=(∑ i,r i^(m+4)) from
          Equiv.sum_comp e (fun i => r i^(m+4))]
        exact hvol
      have hrlarge : 1/2≤(r ∘ e) 0 := by
        simpa only [Function.comp_apply,e,Equiv.swap_apply_left] using hj
      have hp := hasPacking_large_normalized m (r ∘ e) (fun i => hr (e i))
        hrlarge hrvol (fun i j hij => hpair (e i) (e j) (fun h => hij (e.injective h)))
      have hh := hp.reindex e.symm
      simpa only [Function.comp_def,Equiv.apply_symm_apply] using hh

 theorem hasPacking_dim_ge_four_bp240_oai {n N : ℕ} (hn : 4≤n) (hN : 1≤N)
    {R : ℝ} (hR : 0<R) (r : Fin N → ℝ) (hr : ∀ i,0 < r i)
    (hvol : ∑ i,r i^n<R^n) (hpair : ∀ i j,i≠j → r i+r j<R) : HasPacking n N R r := by
  apply (hasPacking_normalize hR).mpr
  apply hasPacking_dim_ge_four_normalized hn hN (fun i => r i/R) (fun i => div_pos (hr i) hR)
  · simp only [div_pow,← Finset.sum_div]
    exact (div_lt_one (pow_pos hR n)).mpr hvol
  · intro i j hij
    rw [← add_div]
    exact (div_lt_one hR).mpr (hpair i j hij)

end PackingSufficiencySupport

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.hasPacking_dim_ge_four_bp240_oai := @OAI.PackingSufficiencySupport.hasPacking_dim_ge_four_bp240_oai
