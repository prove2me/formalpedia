-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_rounded_intervals_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:13.798198+00:00
-- url     : https://prove2.me/submissions/89c253df-f5e6-4e1b-8bfd-f47ea493bff9

import Mathlib
import Definitions.Def_OAIQ240Bp015
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_hamiltonian_disk_germs_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCorrection
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.coordinateForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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
-- module Solutions.OAIQ240_BP.BallPacking_Moser_CircleCorrection
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Metric
open scoped Classical
open Function MeasureTheory

theorem closedRoundDisk_isCompact (R : ℝ) : IsCompact (closedRoundDisk R) := by
  apply (isCompact_closedBall (0 : Plane) (R^2+1)).of_isClosed_subset
    (isClosed_le radiusSq_smooth.continuous continuous_const)
  intro p hp
  rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff,
    Real.norm_eq_abs,Real.norm_eq_abs]
  change p.1^2+p.2^2 ≤ R^2 at hp
  constructor
  · apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg p.2,sq_nonneg (p.1-1),sq_nonneg (p.1+1)]
  · apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg p.1,sq_nonneg (p.2-1),sq_nonneg (p.2+1)]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ParametricMoser
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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

theorem areaPolar_image_volume {S : Set Plane} (hS : MeasurableSet S)
    (hsub : S ⊆ areaPolarDomain) : volume (areaPolar '' S) = volume S := by
  have he := lintegral_abs_det_fderiv_eq_addHaar_image volume hS
    (f' := fderiv ℝ areaPolar)
    (fun x hx => ((areaPolar_smoothAt (hsub hx).1).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
    (areaPolar_injOn.mono hsub)
  rw [← he]
  calc
    (∫⁻ x in S, ENNReal.ofReal |(fderiv ℝ areaPolar x).det|) = ∫⁻ _ in S, (1 : ℝ≥0∞) := by
      apply setLIntegral_congr_fun hS
      intro x hx
      change ENNReal.ofReal |(fderiv ℝ areaPolar x).det| = 1
      rw [areaPolar_det (hsub hx).1]
      simp
    _ = volume S := by simp

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CubicAreaExhaustion
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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

theorem tanh_smooth : ContDiff ℝ ∞ Real.tanh := by
  have ht : Real.tanh = fun y => Real.sinh y / Real.cosh y :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [ht]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun y => (Real.cosh_pos y).ne')

theorem tanh_hasDerivAt (x : ℝ) :
    HasDerivAt Real.tanh (1/(Real.cosh x)^2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have ht : Real.tanh = Real.sinh / Real.cosh := funext Real.tanh_eq_sinh_div_cosh
  have he : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  simpa only [← ht,he] using h

theorem squareSqueeze_smooth (k : ℝ) : ContDiff ℝ ∞ (squareSqueeze k) := by
  exact (tanh_smooth.comp (contDiff_const.mul contDiff_fst)).prodMk
    (tanh_smooth.comp (contDiff_const.mul contDiff_snd))

theorem squareSqueeze_injective {k : ℝ} (hk : k ≠ 0) : Injective (squareSqueeze k) := by
  intro x y h
  have ha := Real.tanh_injective (congrArg Prod.fst h)
  have hb := Real.tanh_injective (congrArg Prod.snd h)
  exact Prod.ext (mul_left_cancel₀ hk ha) (mul_left_cancel₀ hk hb)

theorem squareSqueeze_fderiv (k : ℝ) (x v : Plane) :
    fderiv ℝ (squareSqueeze k) x v =
      (k/(Real.cosh (k*x.1))^2*v.1,k/(Real.cosh (k*x.2))^2*v.2) := by
  have h1 := (tanh_hasDerivAt (k*x.1)).comp_hasFDerivAt x
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).const_mul k)
  have h2 := (tanh_hasDerivAt (k*x.2)).comp_hasFDerivAt x
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).const_mul k)
  change fderiv ℝ (fun z : Plane => (Real.tanh (k*z.1),Real.tanh (k*z.2))) x v = _
  erw [(h1.prodMk h2).fderiv]
  ext <;> simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

theorem squareSqueeze_det_pos {k : ℝ} (hk : 0 < k) (x : Plane) :
    0 < (fderiv ℝ (squareSqueeze k) x).det := by
  rw [planar_det]
  simp only [squareSqueeze_fderiv]
  change 0 < (k/(Real.cosh (k*x.1))^2*1)*(k/(Real.cosh (k*x.2))^2*1) -
    (k/(Real.cosh (k*x.2))^2*0)*(k/(Real.cosh (k*x.1))^2*0)
  simp only [mul_one,mul_zero,sub_zero]
  exact mul_pos (div_pos hk (sq_pos_of_ne_zero (Real.cosh_pos _).ne'))
    (div_pos hk (sq_pos_of_ne_zero (Real.cosh_pos _).ne'))

theorem squeezedDisk_compact (k : ℝ) : IsCompact (squeezedDisk k) :=
  (closedRoundDisk_isCompact 1).image (squareSqueeze_smooth k).continuous

theorem squeezedDisk_subset (k : ℝ) : squeezedDisk k ⊆ Ioo (-1) 1 ×ˢ Ioo (-1) 1 := by
  rintro _ ⟨x,_,rfl⟩
  exact ⟨⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩,
    ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩⟩

theorem exists_squeezedDisk_contains {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ k : ℝ, 0 < k ∧ Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k := by
  let M := max |Real.artanh (-q)| |Real.artanh q|
  have hM : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  let k := 2*(M+1)
  have hk : 0 < k := by dsimp [k] <;> positivity
  have hb (a : ℝ) (ha : a ∈ Icc (-q) q) : |Real.artanh a| ≤ M := by
    have hlo := Real.artanh_le_artanh (by linarith : -1 < -q) (by linarith [ha.2] : a < 1) ha.1
    have hhi := Real.artanh_le_artanh (by linarith [ha.1] : -1 < a) hq1 ha.2
    apply abs_le.mpr
    constructor
    · exact ((neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)).trans hlo
    · exact hhi.trans ((le_abs_self _).trans (le_max_right _ _))
  refine ⟨k,hk,?_⟩
  intro x hx
  refine ⟨(Real.artanh x.1/k,Real.artanh x.2/k),?_,?_⟩
  · have h1 := hb x.1 hx.1
    have h2 := hb x.2 hx.2
    have hb1 : |Real.artanh x.1/k| < 1/2 := by
      rw [abs_div,abs_of_pos hk,div_lt_iff₀ hk]
      dsimp [k] <;> linarith
    have hb2 : |Real.artanh x.2/k| < 1/2 := by
      rw [abs_div,abs_of_pos hk,div_lt_iff₀ hk]
      dsimp [k] <;> linarith
    change (Real.artanh x.1/k)^2+(Real.artanh x.2/k)^2 ≤ 1^2
    have ha1 := (abs_lt.mp hb1)
    have ha2 := (abs_lt.mp hb2)
    nlinarith [sq_nonneg (Real.artanh x.1/k),sq_nonneg (Real.artanh x.2/k)]
  · ext <;> simp only [squareSqueeze,mul_div_cancel₀ _ hk.ne']
    · exact Real.tanh_artanh ⟨by linarith [hx.1.1],by linarith [hx.1.2]⟩
    · exact Real.tanh_artanh ⟨by linarith [hx.2.1],by linarith [hx.2.2]⟩

theorem squeezedArea_nonneg (k : ℝ) : 0 ≤ squeezedArea k := ENNReal.toReal_nonneg

theorem planar_closed_square_volume {q : ℝ} (hq : 0 ≤ q) :
    volume (Icc (-q) q ×ˢ Icc (-q) q : Set Plane) = ENNReal.ofReal (4*q^2) := by
  change (volume.prod volume) (Icc (-q) q ×ˢ Icc (-q) q) = _
  rw [Measure.prod_prod,Real.volume_Icc,← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

theorem squeezedArea_le (k : ℝ) : squeezedArea k ≤ 4 := by
  have hm : volume (squeezedDisk k) ≤ volume (Ioo (-1) 1 ×ˢ Ioo (-1) 1 : Set Plane) :=
    measure_mono (squeezedDisk_subset k)
  have hv : volume (Ioo (-1) 1 ×ˢ Ioo (-1) 1 : Set Plane) = ENNReal.ofReal 4 := by
    change (volume.prod volume) (Ioo (-1) 1 ×ˢ Ioo (-1) 1) = _
    rw [Measure.prod_prod,Real.volume_Ioo]
    norm_num
  rw [hv] at hm
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  simpa only [squeezedArea,ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 4)] using hh

theorem squeezedArea_lower {q k : ℝ} (hq : 0 ≤ q)
    (hsub : Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k) : 4*q^2 ≤ squeezedArea k := by
  have hm : volume (Icc (-q) q ×ˢ Icc (-q) q : Set Plane) ≤ volume (squeezedDisk k) :=
    measure_mono hsub
  rw [planar_closed_square_volume hq] at hm
  have hh := ENNReal.toReal_mono (squeezedDisk_compact k).measure_ne_top hm
  simpa only [squeezedArea,ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*q^2)] using hh

theorem exists_rounded_square {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ k : ℝ, 0 < k ∧ Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k ∧
      0 < squeezedArea k ∧ 4*q^2 ≤ squeezedArea k ∧ squeezedArea k ≤ 4 := by
  obtain ⟨k,hk,hs⟩ := exists_squeezedDisk_contains hq0.le hq1
  have hl := squeezedArea_lower hq0.le hs
  exact ⟨k,hk,hs,lt_of_lt_of_le (by positivity) hl,hl,squeezedArea_le k⟩

@[simp] theorem diagonalScale_det (a b : ℝ) : (diagonalScale a b).det = a*b := by
  rw [planar_det]
  simp [planarArea_apply]

theorem affineRectangle_image_volume (c : Plane) (a b : ℝ) (S : Set Plane) :
    volume (affineRectangle c a b '' S) = ENNReal.ofReal |a*b| * volume S := by
  change volume (((fun x : Plane => c+x) ∘ diagonalScale a b) '' S) = _
  rw [Set.image_comp]
  simp only [image_add_left,MeasureTheory.measure_preimage_add]
  rw [Measure.addHaar_image_continuousLinearMap]
  change ENNReal.ofReal |(diagonalScale a b).det| * volume S = _
  rw [diagonalScale_det]

theorem affineRectangle_squeezedArea {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (c : Plane) (k : ℝ) :
    (volume (affineRectangle c a b '' squeezedDisk k)).toReal = a*b*squeezedArea k := by
  rw [affineRectangle_image_volume,ENNReal.toReal_mul,abs_of_nonneg (mul_nonneg ha hb),
    ENNReal.toReal_ofReal (mul_nonneg ha hb)]
  rfl

variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]

theorem exists_rounded_square_with_control {Y : Set P} (hY : IsCompact Y)
    {F : Plane × P → E} (hF : Continuous F) {W : Set E} (hW : IsOpen W)
    (hbase : ∀ y ∈ Y, F ((1,1),y) ∈ W) :
    ∃ q k : ℝ, 0 < q ∧ q < 1 ∧ 0 < k ∧
      Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k ∧
      0 < squeezedArea k ∧
      ∀ y ∈ Y, F ((q,4/squeezedArea k),y) ∈ W := by
  have hsub : ({(1,1)} : Set Plane) ×ˢ Y ⊆ F ⁻¹' W := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have he : x = (1,1) := hx
    subst x
    exact hbase y hy
  obtain ⟨U,V,hU,_,h1U,hYV,hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hY (hW.preimage hF) hsub
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h1U rfl))
  have hqcont : ContinuousAt (fun q : ℝ => 1/q^2) 1 :=
    continuousAt_const.div (continuousAt_id.pow 2) (by norm_num)
  have hevent : ∀ᶠ q : ℝ in 𝓝 1,
      0 < q ∧ |q-1| < δ ∧ |1/q^2-1| < δ := by
    have ha : ∀ᶠ q : ℝ in 𝓝 1, 0 < q := isOpen_Ioi.mem_nhds (by norm_num)
    have hb : ∀ᶠ q : ℝ in 𝓝 1, |q-1| < δ := by
      filter_upwards [Metric.ball_mem_nhds (1:ℝ) hδ] with q hq
      exact hq
    have hc : ∀ᶠ q : ℝ in 𝓝 1, |1/q^2-1| < δ := by
      have hct : Tendsto (fun q : ℝ => 1/q^2) (𝓝 1) (𝓝 1) := by
        simpa only [one_pow,div_one] using hqcont.tendsto
      filter_upwards [hct.eventually (Metric.ball_mem_nhds (1:ℝ) hδ)] with q hq
      exact hq
    filter_upwards [ha,hb,hc] with q ha hb hc using ⟨ha,hb,hc⟩
  obtain ⟨q,hq,hq1⟩ := ((hevent.filter_mono
    (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)).and self_mem_nhdsWithin).exists
  obtain ⟨k,hk,hs,hA,hAl,hAu⟩ := exists_rounded_square hq.1 hq1
  have htlo : 1 ≤ 4/squeezedArea k := (le_div_iff₀ hA).mpr (by simpa using hAu)
  have hthi : 4/squeezedArea k ≤ 1/q^2 := by
    apply (div_le_div_iff₀ hA (sq_pos_of_pos hq.1)).mpr
    simpa using hAl
  have htd : |4/squeezedArea k-1| < δ := by
    rw [abs_of_nonneg (sub_nonneg.mpr htlo)]
    exact (sub_le_sub_right hthi 1).trans_lt ((le_abs_self _).trans_lt hq.2.2)
  refine ⟨q,k,hq.1,hq1,hk,hs,hA,?_⟩
  intro y hy
  apply hUV ⟨hδU ?_,hYV hy⟩
  rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
  exact ⟨by simpa only [Real.dist_eq] using hq.2.1,
    by simpa only [Real.dist_eq] using htd⟩

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_SmoothConvexSelection
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function
variable {P : Type*} [TopologicalSpace P]

theorem roundedMargins_open {n : ℕ} (C : P → Fin n → ℝ) (hC : Continuous C)
    (L w : Fin n → ℝ) (V : P → Fin n → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i}) :
    IsOpen {p : Plane × P | RoundedMargins C L w V p.1.1 p.1.2 p.2} := by
  have hlo (i : Fin n) : IsOpen {p : Plane × P | C p.2 i-p.1.2*L i/2 ∈ V p.2 i} :=
    (hV i).preimage (continuous_snd.prodMk
      (((continuous_apply i).comp (hC.comp continuous_snd)).sub
        ((continuous_fst.snd.mul continuous_const).div_const 2)))
  have hhi (i : Fin n) : IsOpen {p : Plane × P | C p.2 i+p.1.2*L i/2 ∈ V p.2 i} :=
    (hV i).preimage (continuous_snd.prodMk
      (((continuous_apply i).comp (hC.comp continuous_snd)).add
        ((continuous_fst.snd.mul continuous_const).div_const 2)))
  have hpair (i j : Fin n) : IsOpen {p : Plane × P | i < j →
      C p.2 j-p.1.1*p.1.2*L j/2 < C p.2 i-p.1.2*L i/2 ∧
      C p.2 i+p.1.2*L i/2 < C p.2 j+p.1.1*p.1.2*L j/2 ∧ w i < p.1.1*w j} := by
    by_cases hij : i < j
    · simp only [hij,true_implies,ofPred_and]
      exact (isOpen_lt (by fun_prop) (by fun_prop)).inter
        ((isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop)))
    · simp only [hij,false_implies,ofPred_true,isOpen_univ]
  change IsOpen {p : Plane × P | 0 < p.1.2 ∧
    (∀ i, C p.2 i-p.1.2*L i/2 ∈ V p.2 i ∧ C p.2 i+p.1.2*L i/2 ∈ V p.2 i) ∧
    ∀ i j, i < j → _}
  simp only [ofPred_and,ofPred_forall]
  exact (isOpen_lt continuous_const continuous_fst.snd).inter
    ((isOpen_iInter_of_finite (fun i => (hlo i).inter (hhi i))).inter
      (isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j => by
        simpa only [ofPred_forall,ofPred_and] using hpair i j))))

theorem exists_exact_area_rounded_margins {n : ℕ} {Y : Set P} (hY : IsCompact Y)
    (c : P → Fin n → ℝ) (hc : Continuous c) (L w : Fin n → ℝ)
    (hw : StrictMono w) (V : P → Fin n → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i})
    (hplace : ∀ y ∈ Y, (∀ i, c y i ∈ V y i ∧ c y i+L i ∈ V y i) ∧
      StrictNestedStarts L (c y)) :
    ∃ q k : ℝ, 0 < q ∧ q < 1 ∧ 0 < k ∧
      Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k ∧ 0 < squeezedArea k ∧
      ∀ y ∈ Y, RoundedMargins (fun y i => c y i+L i/2) L w V q (4/squeezedArea k) y := by
  let C : P → Fin n → ℝ := fun y i => c y i+L i/2
  have hC : Continuous C := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp hc).add continuous_const
  apply exists_rounded_square_with_control hY continuous_id
    (roundedMargins_open C hC L w V hV)
  intro y hy
  change RoundedMargins C L w V 1 1 y
  refine ⟨by norm_num,?_,?_⟩
  · intro i
    simpa only [C,one_mul,add_sub_cancel_right,add_assoc,add_halves] using (hplace y hy).1 i
  · intro i j hij
    dsimp [C]
    simp only [one_mul,add_sub_cancel_right,add_assoc,add_halves]
    exact ⟨((hplace y hy).2 hij).1,((hplace y hy).2 hij).2,hw hij⟩


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory

theorem affineRectangle_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (c : Plane) :
    Injective (affineRectangle c a b) := by
  intro x y he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  exact Prod.ext (mul_left_cancel₀ ha (add_left_cancel h1))
    (mul_left_cancel₀ hb (add_left_cancel h2))

theorem affineRectangle_smooth (c : Plane) (a b : ℝ) :
    ContDiff ℝ ∞ (affineRectangle c a b) :=
  contDiff_const.add (diagonalScale a b).contDiff

theorem roundedMap_smooth (k : ℝ) (c : Plane) (a b : ℝ) :
    ContDiff ℝ ∞ (roundedMap k c a b) :=
  (affineRectangle_smooth c a b).comp (squareSqueeze_smooth k)

theorem roundedMap_injective {k a b : ℝ} (hk : k ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (c : Plane) : Injective (roundedMap k c a b) :=
  (affineRectangle_injective ha hb c).comp (squareSqueeze_injective hk)

theorem affineRectangle_fderiv (c : Plane) (a b : ℝ) (x : Plane) :
    fderiv ℝ (affineRectangle c a b) x = diagonalScale a b := by
  exact ((diagonalScale a b).hasFDerivAt.const_add c).fderiv

theorem roundedMap_det {k a b : ℝ} (c : Plane) (x : Plane) :
    (fderiv ℝ (roundedMap k c a b) x).det = a*b*(fderiv ℝ (squareSqueeze k) x).det := by
  change (fderiv ℝ (affineRectangle c a b ∘ squareSqueeze k) x).det = _
  rw [fderiv_comp x ((affineRectangle_smooth c a b).differentiable (by simp) _)
    ((squareSqueeze_smooth k).differentiable (by simp) _),affineRectangle_fderiv,
    ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
  change (diagonalScale a b).det * _ = _
  rw [diagonalScale_det]

theorem roundedMap_det_pos {k a b : ℝ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (c : Plane) (x : Plane) : 0 < (fderiv ℝ (roundedMap k c a b) x).det := by
  rw [roundedMap_det]
  exact mul_pos (mul_pos ha hb) (squareSqueeze_det_pos hk x)

theorem roundedMap_mem_openBox {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (x : Plane) : roundedMap k c a b x ∈ openBox c a b := by
  have hx1 := Real.neg_one_lt_tanh (k*x.1)
  have hx2 := Real.tanh_lt_one (k*x.1)
  have hy1 := Real.neg_one_lt_tanh (k*x.2)
  have hy2 := Real.tanh_lt_one (k*x.2)
  change (c.1-a < c.1+a*Real.tanh (k*x.1) ∧ c.1+a*Real.tanh (k*x.1) < c.1+a) ∧
    (c.2-b < c.2+b*Real.tanh (k*x.2) ∧ c.2+b*Real.tanh (k*x.2) < c.2+b)
  constructor <;> constructor <;> nlinarith

theorem box_subset_roundedBox {q k a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k) (c : Plane) :
    box c (q*a) (q*b) ⊆ roundedBox k c a b := by
  intro x hx
  let z : Plane := ((x.1-c.1)/a,(x.2-c.2)/b)
  have hz : z ∈ Icc (-q) q ×ˢ Icc (-q) q := by
    change (-q ≤ (x.1-c.1)/a ∧ (x.1-c.1)/a ≤ q) ∧
      (-q ≤ (x.2-c.2)/b ∧ (x.2-c.2)/b ≤ q)
    constructor <;> constructor
    · apply (le_div_iff₀ ha).mpr; linarith [hx.1.1]
    · apply (div_le_iff₀ ha).mpr; linarith [hx.1.2]
    · apply (le_div_iff₀ hb).mpr; linarith [hx.2.1]
    · apply (div_le_iff₀ hb).mpr; linarith [hx.2.2]
  obtain ⟨u,hu,he⟩ := hs hz
  refine ⟨u,hu,?_⟩
  change affineRectangle c a b (squareSqueeze k u) = x
  rw [he]
  ext <;> simp [affineRectangle,z,mul_div_cancel₀ _ ha.ne',mul_div_cancel₀ _ hb.ne']

theorem openBox_subset_interior_roundedBox {q k a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k) (c : Plane) :
    openBox c (q*a) (q*b) ⊆ interior (roundedBox k c a b) := by
  apply (isOpen_Ioo.prod isOpen_Ioo).subset_interior_iff.mpr
  exact (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self).trans
    (box_subset_roundedBox ha hb hs c)

theorem roundedBox_compact (k : ℝ) (c : Plane) (a b : ℝ) :
    IsCompact (roundedBox k c a b) :=
  (closedRoundDisk_isCompact 1).image (roundedMap_smooth k c a b).continuous

theorem roundedBox_volume {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (k : ℝ) (c : Plane) :
    (volume (roundedBox k c a b)).toReal = a*b*squeezedArea k := by
  change (volume ((affineRectangle c a b ∘ squareSqueeze k) '' closedRoundDisk 1)).toReal = _
  rw [image_comp]
  exact affineRectangle_squeezedArea ha hb c k


end

section
open scoped ContDiff Topology
open Set Function Filter
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E]

theorem isInvertible_of_det_ne_zero {A : E →L[ℝ] E} (hA : A.det ≠ 0) : A.IsInvertible :=
  ⟨(A.toLinearMap.equivOfDetNeZero hA).toContinuousLinearEquiv,rfl⟩

theorem smooth_map_nhds_eq {f : E → E} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hd : (fderiv ℝ f x).det ≠ 0) : map f (𝓝 x) = 𝓝 (f x) := by
  obtain ⟨e,he⟩ := isInvertible_of_det_ne_zero hd
  have hs := hf.hasStrictFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [← he] at hs
  exact hs.map_nhds_eq_of_equiv

theorem image_interior_subset_of_det_ne_zero {f : E → E} {S : Set E}
    (hf : ∀ x ∈ interior S, ContDiffAt ℝ ∞ f x)
    (hd : ∀ x ∈ interior S, (fderiv ℝ f x).det ≠ 0) :
    f '' interior S ⊆ interior (f '' S) := by
  rintro _ ⟨x,hx,rfl⟩
  apply mem_interior_iff_mem_nhds.mpr
  have hh := Filter.image_mem_map (m := f) (mem_interior_iff_mem_nhds.mp hx)
  rwa [smooth_map_nhds_eq (hf x hx) (hd x hx)] at hh

variable [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem det_fderiv_conjugate (e : E ≃L[ℝ] F) {f : F → F} {x : E}
    (hf : DifferentiableAt ℝ f (e x)) :
    (fderiv ℝ (fun x => e.symm (f (e x))) x).det = (fderiv ℝ f (e x)).det := by
  have hd := e.symm.hasFDerivAt.comp x (hf.hasFDerivAt.comp x e.hasFDerivAt)
  change (fderiv ℝ (e.symm ∘ f ∘ e) x).det = _
  rw [hd.fderiv]
  change LinearMap.det (e.symm.toLinearEquiv.toLinearMap ∘ₗ
    (fderiv ℝ f (e x)).toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap) = _
  exact LinearMap.det_conj _ e.symm.toLinearEquiv


end

open scoped ContDiff Topology
open Set Function MeasureTheory

theorem openBox_subset_polar {c : Plane} {a b : ℝ} (hfit : FitsPolar c a b) :
    openBox c a b ⊆ areaPolarDomain := by
  intro x hx
  exact ⟨hfit.1.trans hx.1.1,hfit.2.2.1.trans hx.2.1,hx.2.2.trans hfit.2.2.2⟩

theorem polarRoundedMap_injective {k a b : ℝ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (c : Plane) (hfit : FitsPolar c a b) : Injective (polarRoundedMap k c a b) := by
  intro x y he
  apply roundedMap_injective hk.ne' ha.ne' hb.ne' c
  exact areaPolar_injOn (openBox_subset_polar hfit (roundedMap_mem_openBox ha hb k c x))
    (openBox_subset_polar hfit (roundedMap_mem_openBox ha hb k c y)) he

theorem polarRoundedMap_smooth {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (hfit : FitsPolar c a b) : ContDiff ℝ ∞ (polarRoundedMap k c a b) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (areaPolar_smoothAt (openBox_subset_polar hfit (roundedMap_mem_openBox ha hb k c x)).1).comp x
    (roundedMap_smooth k c a b).contDiffAt

theorem polarRoundedMap_det {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (hfit : FitsPolar c a b) (x : Plane) :
    (fderiv ℝ (polarRoundedMap k c a b) x).det = (fderiv ℝ (roundedMap k c a b) x).det := by
  have hp := (openBox_subset_polar hfit (roundedMap_mem_openBox ha hb k c x)).1
  change (fderiv ℝ (areaPolar ∘ roundedMap k c a b) x).det = _
  rw [fderiv_comp x ((areaPolar_smoothAt hp).differentiableAt (by simp))
    ((roundedMap_smooth k c a b).differentiable (by simp) _),
    ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
  change (fderiv ℝ areaPolar (roundedMap k c a b x)).det * _ = _
  rw [areaPolar_det hp,one_mul]

theorem polarRoundedMap_det_pos {k a b : ℝ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (c : Plane) (hfit : FitsPolar c a b) (x : Plane) :
    0 < (fderiv ℝ (polarRoundedMap k c a b) x).det := by
  rw [polarRoundedMap_det ha hb k c hfit]
  exact roundedMap_det_pos hk ha hb c x

theorem polarRoundedMap_capacity {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (hfit : FitsPolar c a b) (x : Plane) :
    Real.pi * radiusSq (polarRoundedMap k c a b x) = (roundedMap k c a b x).1 :=
  areaPolar_capacity (openBox_subset_polar hfit (roundedMap_mem_openBox ha hb k c x)).1.le

theorem polarRoundedDisk_volume {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (hfit : FitsPolar c a b) :
    (volume (polarRoundedDisk k c a b)).toReal = a*b*squeezedArea k := by
  change (volume ((areaPolar ∘ roundedMap k c a b) '' closedRoundDisk 1)).toReal = _
  rw [image_comp]
  change (volume (areaPolar '' roundedBox k c a b)).toReal = _
  rw [areaPolar_image_volume (roundedBox_compact k c a b).measurableSet (by
    rintro z ⟨x,_,rfl⟩
    exact openBox_subset_polar hfit (roundedMap_mem_openBox ha hb k c x))]
  exact roundedBox_volume ha.le hb.le k c

theorem polarRoundedDisk_nested {k a b a' b' : ℝ} {c c' : Plane}
    (ha' : 0 < a') (hb' : 0 < b') (hfit' : FitsPolar c' a' b')
    (hnest : roundedBox k c a b ⊆ interior (roundedBox k c' a' b')) :
    polarRoundedDisk k c a b ⊆ interior (polarRoundedDisk k c' a' b') := by
  change (areaPolar ∘ roundedMap k c a b) '' closedRoundDisk 1 ⊆
    interior ((areaPolar ∘ roundedMap k c' a' b') '' closedRoundDisk 1)
  rw [image_comp,image_comp]
  apply (image_mono hnest).trans
  apply image_interior_subset_of_det_ne_zero
  · intro x hx
    obtain ⟨z,_,rfl⟩ := interior_subset hx
    exact areaPolar_smoothAt (openBox_subset_polar hfit' (roundedMap_mem_openBox ha' hb' k c' z)).1
  · intro x hx
    obtain ⟨z,_,rfl⟩ := interior_subset hx
    rw [areaPolar_det (openBox_subset_polar hfit' (roundedMap_mem_openBox ha' hb' k c' z)).1]
    norm_num

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem polarRoundedFamily_smoothOn {A : Set P} (_hA : IsOpen A)
    (C : P → Plane) (hC : ContDiff ℝ ∞ C) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (hfit : ∀ y ∈ A, FitsPolar (C y) a b) :
    ContDiffOn ℝ ∞ (fun p : P × Plane => polarRoundedMap k (C p.1) a b p.2) (A ×ˢ univ) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hg : ContDiff ℝ ∞ (fun p : P × Plane => roundedMap k (C p.1) a b p.2) :=
    (hC.comp contDiff_fst).add
      ((diagonalScale a b).contDiff.comp ((squareSqueeze_smooth k).comp contDiff_snd))
  exact (areaPolar_smoothAt
    (openBox_subset_polar (hfit p.1 hp.1) (roundedMap_mem_openBox ha hb k (C p.1) p.2)).1).comp p hg.contDiffAt



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CompactEmbeddingIsotopy
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem complex_plane_image_closedBall {R : ℝ} (hR : 0 ≤ R) :
    Complex.equivRealProdCLM '' Metric.closedBall (0:ℂ) R = closedRoundDisk R := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.re^2+z.im^2 ≤ R^2
    have hn : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have he := Complex.sq_norm z
    rw [Complex.normSq_apply] at he
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hn 2]
  · intro hx
    change x.1^2+x.2^2 ≤ R^2 at hx
    refine ⟨(⟨x.1,x.2⟩ : ℂ),?_,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right,← sq_le_sq₀ (norm_nonneg _) hR]
    have he := Complex.sq_norm (⟨x.1,x.2⟩ : ℂ)
    rw [Complex.normSq_apply] at he
    nlinarith

theorem complex_plane_image_ball {R : ℝ} (hR : 0 ≤ R) :
    Complex.equivRealProdCLM '' Metric.ball (0:ℂ) R = roundDisk R := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.re^2+z.im^2 < R^2
    have hn : ‖z‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have he := Complex.sq_norm z
    rw [Complex.normSq_apply] at he
    nlinarith [(sq_lt_sq₀ (norm_nonneg _) hR).mpr hn]
  · intro hx
    change x.1^2+x.2^2 < R^2 at hx
    refine ⟨(⟨x.1,x.2⟩ : ℂ),?_,rfl⟩
    rw [Metric.mem_ball,dist_zero_right,← sq_lt_sq₀ (norm_nonneg _) hR]
    have he := Complex.sq_norm (⟨x.1,x.2⟩ : ℂ)
    rw [Complex.normSq_apply] at he
    nlinarith

theorem complex_plane_volume_image (S : Set ℂ) :
    volume (Complex.equivRealProdCLM '' S) = volume S := by
  have hh := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
    (Complex.measurableEquivRealProd '' S)
  rw [preimage_image_eq S Complex.measurableEquivRealProd.injective] at hh
  exact hh.symm

end

theorem diagonalScale_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Injective (diagonalScale a b) := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (mul_left_cancel₀ ha h1) (mul_left_cancel₀ hb h2)

theorem diagonalScale_inv_image_closedRoundDisk {r : ℝ} (hr : 0 < r) :
    diagonalScale r⁻¹ r⁻¹ '' closedRoundDisk r = closedRoundDisk 1 := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.1^2+z.2^2 ≤ r^2 at hz
    change (r⁻¹*z.1)^2+(r⁻¹*z.2)^2 ≤ 1^2
    have hh := mul_le_mul_of_nonneg_left hz (sq_nonneg r⁻¹)
    have he : r⁻¹^2*r^2 = 1 := by field_simp
    nlinarith only [hh,he]
  · intro hx
    change x.1^2+x.2^2 ≤ 1^2 at hx
    refine ⟨(r*x.1,r*x.2),?_,?_⟩
    · change (r*x.1)^2+(r*x.2)^2 ≤ r^2
      nlinarith only [mul_le_mul_of_nonneg_left hx (sq_nonneg r)]
    · ext <;> simp [diagonalScale_apply,hr.ne']

theorem volume_closedRoundDisk {r : ℝ} (hr : 0 ≤ r) :
    volume (closedRoundDisk r) = ENNReal.ofReal (Real.pi*r^2) := by
  rw [←complex_plane_image_closedBall hr,complex_plane_volume_image]
  rw [InnerProductSpace.volume_closedBall_of_dim_even (k := 1) (by simp)]
  simp only [Complex.finrank_real_complex, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  rw [←ENNReal.ofReal_pow hr,←ENNReal.ofReal_mul (sq_nonneg r),mul_comm]

theorem areaRadius_pos {a : ℝ} (ha : 0 < a) : 0 < areaRadius a :=
  Real.sqrt_pos.2 (div_pos ha Real.pi_pos)

theorem areaRadius_sq {a : ℝ} (ha : 0 ≤ a) : (areaRadius a)^2 = a/Real.pi :=
  Real.sq_sqrt (div_nonneg ha Real.pi_pos.le)

theorem areaRadius_strictMono : StrictMonoOn areaRadius (Ici 0) := by
  intro a ha b _ hab
  exact Real.sqrt_lt_sqrt (div_nonneg ha Real.pi_pos.le) ((div_lt_div_iff_of_pos_right Real.pi_pos).2 hab)

theorem mem_roundDisk_areaRadius {a : ℝ} (ha : 0 ≤ a) (x : Plane) :
    x ∈ roundDisk (areaRadius a) ↔ radialArea x < a := by
  change radiusSq x < (areaRadius a)^2 ↔ Real.pi * radiusSq x < a
  rw [areaRadius_sq ha,lt_div_iff₀ Real.pi_pos,mul_comm]

theorem volume_closedRoundDisk_areaRadius {a : ℝ} (ha : 0 ≤ a) :
    volume (closedRoundDisk (areaRadius a)) = ENNReal.ofReal a := by
  rw [volume_closedRoundDisk (show 0 ≤ areaRadius a from Real.sqrt_nonneg _),areaRadius_sq ha]
  congr 1
  exact mul_div_cancel₀ _ Real.pi_ne_zero

theorem normalizedPolarMap_injective {k a b r : ℝ} (hk : 0 < k) (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (c : Plane) (hfit : FitsPolar c a b) :
    Injective (normalizedPolarMap k c a b r) :=
  (polarRoundedMap_injective hk ha hb c hfit).comp
    (diagonalScale_injective (inv_ne_zero hr.ne') (inv_ne_zero hr.ne'))

theorem normalizedPolarMap_det_pos {k a b r : ℝ} (hk : 0 < k) (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (c : Plane) (hfit : FitsPolar c a b) (x : Plane) :
    0 < (fderiv ℝ (normalizedPolarMap k c a b r) x).det := by
  rw [normalizedPolarMap,fderiv_comp x
    ((polarRoundedMap_smooth ha hb k c hfit).differentiable (by simp) _)
    ((diagonalScale r⁻¹ r⁻¹).differentiable _), (diagonalScale r⁻¹ r⁻¹).fderiv,
    ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
  change 0 < (fderiv ℝ (polarRoundedMap k c a b) _).det * (diagonalScale r⁻¹ r⁻¹).det
  rw [diagonalScale_det]
  exact mul_pos (polarRoundedMap_det_pos hk ha hb c hfit _) (mul_pos (inv_pos.mpr hr) (inv_pos.mpr hr))

theorem normalizedPolarMap_image {r : ℝ} (hr : 0 < r) (k : ℝ) (c : Plane) (a b : ℝ) :
    normalizedPolarMap k c a b r '' closedRoundDisk r = polarRoundedDisk k c a b := by
  rw [normalizedPolarMap,image_comp,diagonalScale_inv_image_closedRoundDisk hr]
  rfl

theorem polarRoundedDisk_volume_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (hfit : FitsPolar c a b) :
    volume (polarRoundedDisk k c a b) = ENNReal.ofReal (a*b*squeezedArea k) := by
  have hfin : volume (polarRoundedDisk k c a b) ≠ ⊤ :=
    ((closedRoundDisk_isCompact 1).image (polarRoundedMap_smooth ha hb k c hfit).continuous).measure_ne_top
  exact (ENNReal.toReal_eq_toReal_iff' hfin ENNReal.ofReal_ne_top).mp (by
    rw [polarRoundedDisk_volume ha hb k c hfit,ENNReal.toReal_ofReal
      (mul_nonneg (mul_nonneg ha.le hb.le) (squeezedArea_nonneg k))])

theorem roundedBox_nested_of_margins {k q a b a' b' : ℝ} {c c' : Plane}
    (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (hsquare : Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k)
    (hleft : c'.1-q*a' ≤ c.1-a) (hright : c.1+a ≤ c'.1+q*a')
    (hbottom : c'.2-q*b' ≤ c.2-b) (htop : c.2+b ≤ c'.2+q*b') :
    roundedBox k c a b ⊆ interior (roundedBox k c' a' b') := by
  apply Subset.trans _ (openBox_subset_interior_roundedBox ha' hb' hsquare c')
  rintro _ ⟨x,_,rfl⟩
  have hx := roundedMap_mem_openBox ha hb k c x
  exact ⟨⟨hleft.trans_lt hx.1.1,hx.1.2.trans_le hright⟩,
    ⟨hbottom.trans_lt hx.2.1,hx.2.2.trans_le htop⟩⟩

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem normalizedPolarFamily_smoothOn {A : Set P} (hA : IsOpen A)
    (C : P → Plane) (hC : ContDiff ℝ ∞ C) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k r : ℝ) (hfit : ∀ y ∈ A, FitsPolar (C y) a b) :
    ContDiffOn ℝ ∞ (fun p : P × Plane => normalizedPolarMap k (C p.1) a b r p.2) (A ×ˢ univ) :=
  (polarRoundedFamily_smoothOn hA C hC ha hb k hfit).comp
    (contDiff_fst.prodMk ((diagonalScale r⁻¹ r⁻¹).contDiff.comp contDiff_snd)).contDiffOn
    (by intro p hp; exact ⟨hp.1,mem_univ _⟩)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_NormalizedRoundedBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory

@[fun_prop] theorem normalizedRoundedMap_smooth (k : ℝ) (c : Plane) (a b r : ℝ) :
    ContDiff ℝ ∞ (normalizedRoundedMap k c a b r) :=
  (roundedMap_smooth k c a b).comp (diagonalScale r⁻¹ r⁻¹).contDiff


end

open scoped ContDiff Topology NNReal
open Set Function MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_ParametricNestedDisks
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
open Metric

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_plane_disk_germs {m : ℕ} {Y A : Set P}
    (hY : IsCompact Y) (hcY : Convex ℝ Y) (hA : IsOpen A) (hYA : Y ⊆ A)
    (y₀ : P) (hy₀ : y₀ ∈ Y) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i)
    (hrmono : StrictMono r) (f : Fin m → P × Plane → Plane)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (A ×ˢ univ))
    (hi : ∀ i y, y ∈ A → Injective (fun x => f i (y,x)))
    (hd : ∀ i y, y ∈ A → ∀ x, 0 < (fderiv ℝ (fun x => f i (y,x)) x).det)
    (hnest : ∀ ⦃i j⦄, i < j → ∀ y ∈ Y,
      (fun x => f i (y,x)) '' closedRoundDisk (r i) ⊆
        interior ((fun x => f j (y,x)) '' closedRoundDisk (r j)))
    (R : ℝ) (hR : 0 < R) (hrR : ∀ i, r i < R)
    (hfit : ∀ i y, y ∈ Y →
      (fun x => f i (y,x)) '' closedRoundDisk (r i) ⊆ roundDisk R)
    (harea : ∀ i y, y ∈ Y → volume ((fun x => f i (y,x)) '' closedRoundDisk (r i)) =
      volume (closedRoundDisk (r i))) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (r i) =
        (fun x => f i (y,x)) '' closedRoundDisk (r i) := by
  let e := Complex.equivRealProdCLM
  let g (i : Fin m) (p : P × ℂ) := e.symm (f i (p.1,e p.2))
  have hs (i : Fin m) : ContDiffOn ℝ ∞ (g i) (A ×ˢ univ) :=
    e.symm.contDiff.comp_contDiffOn ((hf i).comp
      (contDiff_fst.prodMk (e.contDiff.comp contDiff_snd)).contDiffOn (by
        intro p hp; exact ⟨hp.1,mem_univ _⟩))
  have hder (i : Fin m) (y : P) (hy : y ∈ A) (x : ℂ) :
      (fderiv ℝ (fun x => g i (y,x)) x).det =
        (fderiv ℝ (fun x => f i (y,x)) (e x)).det := by
    change (fderiv ℝ (fun x => e.symm (f i (y,e x))) x).det = _
    apply det_fderiv_conjugate e (f := fun x => f i (y,x)) (x := x)
    have hh : ContDiffAt ℝ ∞ (f i) (y,e x) :=
      (hf i).contDiffAt ((hA.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)
    exact (hh.comp _ (contDiff_const.prodMk contDiff_id).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have himage (i : Fin m) (y : P) :
      e '' ((fun x => g i (y,x)) '' Metric.closedBall 0 (r i)) =
        (fun x => f i (y,x)) '' closedRoundDisk (r i) := by
    rw [←complex_plane_image_closedBall (hr i).le]
    simp only [image_image,g,e.apply_symm_apply]
    rfl
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_disk_germs_bp240 hY hcY hA hYA y₀ hy₀ r hr hrmono g hs
    (fun i y hy => e.symm.injective.comp ((hi i y hy).comp e.injective))
    (fun i y hy x => isInvertible_of_det_ne_zero (by rw [hder i y hy x]; exact (hd i y hy _).ne'))
    (fun i y hy => by rw [hder i y hy 0]; exact hd i y hy _)
    (by
      intro i j hij y hy x hx
      have hh := hnest hij y hy
      rw [←himage i y,←himage j y] at hh
      have he : interior (e '' ((fun x => g j (y,x)) '' Metric.closedBall 0 (r j))) =
          e '' interior ((fun x => g j (y,x)) '' Metric.closedBall 0 (r j)) :=
        (e.toHomeomorph.image_interior _).symm
      rw [he] at hh
      have hh' := hh (mem_image_of_mem e hx)
      exact e.injective.mem_set_image.mp hh') R hR hrR
    (by
      intro i y hy x hx
      have hh := hfit i y hy
      rw [←himage i y,←complex_plane_image_ball hR.le] at hh
      exact e.injective.mem_set_image.mp (hh (mem_image_of_mem e hx)))
    (by
      intro i y hy
      rw [←complex_plane_volume_image, himage i y,harea i y hy,
        ←complex_plane_image_closedBall (hr i).le,complex_plane_volume_image])
  refine ⟨Ψ,?_⟩
  intro i y hy
  exact (hΨ i y hy).trans (himage i y)

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_CartesianMomentSlices
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory
open Comparison
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_rounded_intervals_bp240_oai {m : ℕ} {Y : Set P}
    (hY : IsCompact Y) (hcY : Convex ℝ Y) (y₀ : P) (hy₀ : y₀ ∈ Y)
    (h L w : Fin m → ℝ) (hh : ∀ i, 0 < h i) (hh1 : ∀ i, h i < 1)
    (hhmono : StrictMono h) (hw : ∀ i, 0 < w i) (hw1 : ∀ i, w i < 1)
    (hwmono : StrictMono w) (hL : ∀ i, L i*w i = h i)
    (c : P → Fin m → ℝ) (hc : ContDiff ℝ ∞ c)
    (V : P → Fin m → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i})
    (hVconv : ∀ y ∈ Y, ∀ i, Convex ℝ (V y i))
    (hVsub : ∀ y i, V y i ⊆ Ioo 0 1)
    (hplace : ∀ y ∈ Y, (∀ i, c y i ∈ V y i ∧ c y i+L i ∈ V y i) ∧
      StrictNestedStarts L (c y)) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1),
      ∀ i y, y ∈ Y → ∀ x ∈ closedRoundDisk (areaRadius (h i)),
        radialArea (Ψ.isotopy.map y 1 x) ∈ V y i := by
  have hLpos (i : Fin m) : 0 < L i := (mul_pos_iff_of_pos_right (hw i)).mp (hL i ▸ hh i)
  obtain ⟨q,k,hq,hq1,hk,hsquare,harea,hmargin⟩ :=
    exists_exact_area_rounded_margins hY c hc.continuous L w hwmono V hV hplace
  let s : ℝ := 4/squeezedArea k
  have hs : 0 < s := div_pos (by norm_num) harea
  let C (i : Fin m) (y : P) : Plane := (c y i+L i/2,1/2)
  let a (i : Fin m) := s*L i/2
  let b (i : Fin m) := w i/2
  have ha (i : Fin m) : 0 < a i := div_pos (mul_pos hs (hLpos i)) (by norm_num)
  have hb (i : Fin m) : 0 < b i := div_pos (hw i) (by norm_num)
  have hC (i : Fin m) : ContDiff ℝ ∞ (C i) :=
    ((contDiff_apply ℝ ℝ i).comp hc |>.add contDiff_const).prodMk contDiff_const
  let A : Set P := {y | RoundedMargins (fun y i => c y i+L i/2) L w V q s y}
  have hA : IsOpen A := (roundedMargins_open (fun y i => c y i+L i/2)
    (by apply continuous_pi; intro i; exact ((continuous_apply i).comp hc.continuous).add continuous_const)
    L w V hV).preimage
      (show Continuous (fun y : P => ((q,s),y)) from continuous_const.prodMk continuous_id)
  have hYA : Y ⊆ A := hmargin
  have hfit (i : Fin m) (y : P) (hy : y ∈ A) : FitsPolar (C i y) (a i) (b i) := by
    have hlo := (hVsub y i (hy.2.1 i).1).1
    have hhi := (hVsub y i (hy.2.1 i).2).2
    change 0 < c y i+L i/2-s*L i/2 ∧ c y i+L i/2+s*L i/2 < 1 ∧
      0 < 1/2-w i/2 ∧ 1/2+w i/2 < 1
    exact ⟨hlo,hhi,by linarith [hw1 i],by linarith [hw1 i]⟩
  let r i := areaRadius (h i)
  have hr i : 0 < r i := areaRadius_pos (hh i)
  have hrmono : StrictMono r := fun i j hij =>
    areaRadius_strictMono (hh i).le (hh j).le (hhmono hij)
  let f (i : Fin m) (p : P × Plane) := normalizedPolarMap k (C i p.1) (a i) (b i) (r i) p.2
  have hf (i : Fin m) : ContDiffOn ℝ ∞ (f i) (A ×ˢ univ) :=
    normalizedPolarFamily_smoothOn hA (C i) (hC i) (ha i) (hb i) k (r i) (hfit i)
  have hi (i : Fin m) (y : P) (hy : y ∈ A) : Injective (fun x => f i (y,x)) :=
    normalizedPolarMap_injective hk (ha i) (hb i) (hr i) (C i y) (hfit i y hy)
  have hd (i : Fin m) (y : P) (hy : y ∈ A) (x : Plane) :
      0 < (fderiv ℝ (fun x => f i (y,x)) x).det :=
    normalizedPolarMap_det_pos hk (ha i) (hb i) (hr i) (C i y) (hfit i y hy) x
  have himage (i : Fin m) (y : P) :
      (fun x => f i (y,x)) '' closedRoundDisk (r i) = polarRoundedDisk k (C i y) (a i) (b i) :=
    normalizedPolarMap_image (hr i) k (C i y) (a i) (b i)
  have hnest ⦃i j : Fin m⦄ (hij : i < j) (y : P) (hy : y ∈ Y) :
      (fun x => f i (y,x)) '' closedRoundDisk (r i) ⊆
        interior ((fun x => f j (y,x)) '' closedRoundDisk (r j)) := by
    rw [himage,himage]
    apply polarRoundedDisk_nested (ha j) (hb j) (hfit j y (hYA hy))
    apply roundedBox_nested_of_margins (ha i) (hb i) (ha j) (hb j) hsquare
    all_goals
      have hn := (hmargin y hy).2.2 hij
      dsimp only [C,a,b] at *
      nlinarith only [hn.1,hn.2.1,hn.2.2]
  have hrR (i : Fin m) : r i < areaRadius 1 :=
    areaRadius_strictMono (hh i).le (by norm_num) (hh1 i)
  have htarget (i : Fin m) (y : P) (hy : y ∈ Y) :
      (fun x => f i (y,x)) '' closedRoundDisk (r i) ⊆ roundDisk (areaRadius 1) := by
    intro z hz
    rw [himage] at hz
    obtain ⟨x,_,rfl⟩ := hz
    rw [mem_roundDisk_areaRadius (by norm_num)]
    change Real.pi * radiusSq _ < 1
    rw [polarRoundedMap_capacity (ha i) (hb i) k (C i y) (hfit i y (hYA hy))]
    exact (roundedMap_mem_openBox (ha i) (hb i) k (C i y) x).1.2.trans (hfit i y (hYA hy)).2.1
  have hva (i : Fin m) (y : P) (hy : y ∈ Y) :
      volume ((fun x => f i (y,x)) '' closedRoundDisk (r i)) = volume (closedRoundDisk (r i)) := by
    rw [himage,volume_closedRoundDisk_areaRadius (hh i).le]
    rw [polarRoundedDisk_volume_eq (ha i) (hb i) k (C i y) (hfit i y (hYA hy))]
    congr 1
    dsimp only [a,b,s]
    rw [←hL i]
    field_simp [harea.ne']
    ring
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_plane_disk_germs hY hcY hA hYA y₀ hy₀ r hr hrmono f hf hi hd hnest
    (areaRadius 1) (areaRadius_pos (by norm_num)) hrR htarget hva
  refine ⟨Ψ,?_⟩
  intro i y hy x hx
  have hm : Ψ.isotopy.map y 1 x ∈ (fun z => f i (y,z)) '' closedRoundDisk (r i) := by
    rw [←hΨ i y hy]
    exact mem_image_of_mem _ hx
  rw [himage] at hm
  obtain ⟨z,_,he⟩ := hm
  rw [←he]
  change Real.pi * radiusSq _ ∈ _
  rw [polarRoundedMap_capacity (ha i) (hb i) k (C i y) (hfit i y (hYA hy))]
  exact (hVconv y hy i).ordConnected.out ((hmargin y hy).2.1 i).1
    ((hmargin y hy).2.1 i).2 ⟨(roundedMap_mem_openBox (ha i) (hb i) k (C i y) z).1.1.le,
      (roundedMap_mem_openBox (ha i) (hb i) k (C i y) z).1.2.le⟩

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_rounded_intervals_bp240_oai := @OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_rounded_intervals_bp240_oai
