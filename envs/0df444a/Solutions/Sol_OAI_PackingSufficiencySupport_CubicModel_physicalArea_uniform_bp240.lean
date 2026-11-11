-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.CubicModel.physicalArea_uniform_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:39.829201+00:00
-- url     : https://prove2.me/submissions/2a32e1e3-d3fc-43ec-bf09-833c2035021d

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_radialForm_positive_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_tendsto_radial_cubic_cutoff_mass_bp240

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

theorem affineFSPrimitive_smooth (a : ℝ) :
    ContDiff ℝ ∞ (affineFSPrimitive a : PlanePhase ι → _) := by
  have hc : ContDiff ℝ ∞ (fun z : PlanePhase ι => a/(2*(1+phaseSq z))) :=
    contDiff_const.div (contDiff_const.mul (contDiff_const.add phaseSq_smooth))
      (fun z => mul_ne_zero (by norm_num) (fs_den_pos z).ne')
  exact hc.smul (phaseArea (ι := ι)).contDiff

end

end PackingSufficiencySupport.Hamiltonian

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
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vector_chartOneForm (α : E → E →L[ℝ] ℝ) (c y : E) :
    chartOneForm α c y=α y := by
  simp only [chartOneForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,ContinuousLinearMap.comp_id,id_eq]

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
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricAnnulusDomain
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
open DiagonalQuadrics DiagonalQuadrics.Explicit

 theorem projection_contDiff : ContDiff ℂ ∞ projection := by
  exact (((contDiff_apply ℂ ℂ 0).comp contDiff_snd).sub contDiff_fst).prodMk
    (((contDiff_apply ℂ ℂ 1).comp contDiff_snd).sub contDiff_fst)

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_CubicFubiniStudy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
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

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

theorem shrinkingCutoff_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ContDiff ℝ ∞ (shrinkingCutoff g n) := hg.comp (contDiff_const.mul contDiff_id)

theorem shrinkingCutoff_compact {g : ℝ → ℝ} (hg : HasCompactSupport g) (n : ℕ) :
    HasCompactSupport (shrinkingCutoff g n) := by
  have hh := hg.comp_homeomorph (Homeomorph.smulOfNeZero (α := ℝ) ((n:ℝ)+1) (by positivity))
  change HasCompactSupport (fun t : ℝ => g (((n:ℝ)+1)*t))
  simpa only [Function.comp_def,Homeomorph.smulOfNeZero_apply,smul_eq_mul] using hh

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

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

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
-- module Solutions.OAIQ240_BP.BallPacking_Projective_CubicEndCoordinates
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 theorem endRegularRegion_open : IsOpen endRegularRegion := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  have hroot (j : Fin 2) : ContinuousAt
      (fun t => infinityRoot (parameters 0) zeroEnd t j+1) s :=
    ((contDiffAt_pi.mp (infinityRoot_contDiffAt _ zeroEnd hs.1) j).add
      contDiffAt_const).continuousAt
  have he : ∀ᶠ t in 𝓝 s, ∀ j : Fin 2,
      infinityRoot (parameters 0) zeroEnd t j+1≠0 := by
    apply Filter.eventually_all.mpr
    intro j
    exact (hroot j).eventually_ne (hs.2 j)
  filter_upwards [(infinityRegion_open _).mem_nhds hs.1,he] with t ht ht'
  exact ⟨ht,ht'⟩

 theorem zero_mem_endRegularRegion : (0:ℂ)∈endRegularRegion := by
  refine ⟨zero_mem_infinityRegion _,?_⟩
  intro j
  simp [infinityRoot,zeroEnd,endSign]

end PackingSufficiencySupport.CubicModel

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

theorem polynomial_contDiff (k : ι → ℕ × ℕ) :
    ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => polynomial k q.1 q.2) := by
  apply ContDiff.sum
  intro i _
  dsimp [monomial]
  fun_prop

theorem centered_contDiff (k : ι → ℕ × ℕ) :
    ContDiff ℝ ∞ (fun q : ((ι → ℝ) × Plane) × Plane => centered k q.1.1 q.1.2 q.2) := by
  apply ContDiff.prodMk <;> apply ContDiff.sum <;> intro i _ <;> dsimp [monomial] <;> fun_prop

theorem centered_eq (k : ι → ℕ × ℕ) (a : ι → ℝ) (p r : Plane) :
    centered k a p r=numerator k a r-polynomial k a r • p := by
  apply Prod.ext
  · change (∑ i, (((k i).1:ℝ)-p.1)*a i*monomial (k i) r)=
      (∑ i, ((k i).1:ℝ)*a i*monomial (k i) r)-(∑ i,a i*monomial (k i) r)*p.1
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · change (∑ i, (((k i).2:ℝ)-p.2)*a i*monomial (k i) r)=
      (∑ i, ((k i).2:ℝ)*a i*monomial (k i) r)-(∑ i,a i*monomial (k i) r)*p.2
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem centered_moment {k : ι → ℕ × ℕ} {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) : centered k a (moment k a r) r=0 := by
  rw [centered_eq,moment,smul_smul,mul_inv_cancel₀ hP,one_smul,sub_self]

theorem monomial_hasFDerivAt (k : ℕ × ℕ) (r : Plane) :
    HasFDerivAt (monomial k) (monomialDerivative k r) r := by
  have h := (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x:=r)).pow k.1).mul
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x:=r)).pow k.2)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro v
  simp [monomialDerivative]
  ring

theorem centered_hasFDerivAt (k : ι → ℕ × ℕ) (a : ι → ℝ) (p r : Plane) :
    HasFDerivAt (centered k a p) (centeredDerivative k a p r) r := by
  convert! (HasFDerivAt.sum (u := Finset.univ) (fun i _ => (monomial_hasFDerivAt (k i) r).const_mul
    ((((k i).1:ℝ)-p.1)*a i))).prodMk
    (HasFDerivAt.sum (u := Finset.univ) (fun i _ => (monomial_hasFDerivAt (k i) r).const_mul
    ((((k i).2:ℝ)-p.2)*a i))) using 1
  all_goals try with_reducible_and_instances rfl
  ext v <;> simp [centered]

theorem zero_power_derivative (n : ℕ) :
    (n:ℝ)*(0:ℝ)^(n-1)=if n=1 then 1 else 0 := by
  rcases n with _|n
  · simp
  · rcases n with _|n
    · simp
    · simp

theorem monomial_axis (k : ℕ × ℕ) (t : ℝ) :
    monomial k (0,t)=if k.1=0 then t^k.2 else 0 := by
  by_cases h : k.1=0
  · simp [monomial,h]
  · simp [monomial,h,zero_pow h]

theorem monomialDerivative_axis (k : ℕ × ℕ) (t : ℝ) (v : Plane) :
    monomialDerivative k (0,t) v=
      (if k.1=1 then t^k.2 else 0)*v.1+
      (if k.1=0 then (k.2:ℝ)*t^(k.2-1) else 0)*v.2 := by
  simp only [monomialDerivative,add_apply,
    smul_apply,
    smul_eq_mul,zero_power_derivative]
  by_cases h0 : k.1=0
  · simp [h0]
  · by_cases h1 : k.1=1
    · simp [h1]
    · simp [h0,h1,zero_pow h0]

theorem centered_axis_snd (k : ι → ℕ × ℕ) (a : ι → ℝ) (p : Plane) (t : ℝ) :
    (centered k a p (0,t)).2=∑ i,(((k i).2:ℝ)-p.2)*faceMass (k i) (a i) t := by
  apply Finset.sum_congr rfl
  intro i _
  rw [monomial_axis]
  by_cases h : (k i).1=0 <;> simp [faceMass,h,mul_assoc]

theorem centeredDerivative_axis_fst (k : ι → ℕ × ℕ) (a : ι → ℝ) (p t : ℝ) (v : Plane) :
    (centeredDerivative k a (0,p) (0,t) v).1=transverse k a t*v.1 := by
  simp only [centeredDerivative,ContinuousLinearMap.prod_apply,
    sum_apply,smul_apply,smul_eq_mul,
    monomialDerivative_axis,sub_zero,transverse,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h0 : (k i).1=0
  · simp [h0]
  · by_cases h1 : (k i).1=1
    · simp [h1,mul_assoc]
    · simp [h0,h1]

theorem centeredDerivative_axis_snd (k : ι → ℕ × ℕ) (a : ι → ℝ) (p t u : ℝ) :
    (centeredDerivative k a (0,p) (0,t) (0,u)).2=active k a p t*u := by
  simp only [centeredDerivative,ContinuousLinearMap.prod_apply,
    sum_apply,smul_apply,smul_eq_mul,
    monomialDerivative_axis,mul_zero,zero_add,active,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (k i).1=0 <;> simp [h,mul_assoc]

theorem transverse_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (he : ∃ i,k i=(1,0)) {t : ℝ} (ht : 0≤t) : 0<transverse k a t := by
  classical
  apply Finset.sum_pos'
  · intro i _
    split_ifs
    · exact mul_nonneg (ha i).le (pow_nonneg ht _)
    · rfl
  · obtain ⟨i,hi⟩ := he
    exact ⟨i,Finset.mem_univ i,by simpa [hi] using ha i⟩

theorem nat_mul_power (n : ℕ) (t : ℝ) :
    (n:ℝ)*t^(n-1)*t=(n:ℝ)*t^n := by
  rcases n with _|n
  · simp
  · simp only [Nat.succ_sub_one,pow_succ]
    ring

theorem active_variance (k : ι → ℕ × ℕ) (a : ι → ℝ) (p t : ℝ)
    (hz : (centered k a (0,p) (0,t)).2=0) :
    active k a p t*t=∑ i,(((k i).2:ℝ)-p)^2*faceMass (k i) (a i) t := by
  rw [centered_axis_snd] at hz
  have he : active k a p t*t =
      (∑ i,(((k i).2:ℝ)-p)^2*faceMass (k i) (a i) t)+
        p*(∑ i,(((k i).2:ℝ)-p)*faceMass (k i) (a i) t) := by
    rw [active,Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (k i).1=0
    · simp only [ite_eq_left h,faceMass]
      calc
        (((k i).2:ℝ)-p)*a i*((k i).2:ℝ)*t^((k i).2-1)*t =
            ((((k i).2:ℝ)-p)*a i)*(((k i).2:ℝ)*t^((k i).2-1)*t) := by ring
        _ = _ := by rw [nat_mul_power]; ring
    · simp [h,faceMass]
  simpa only [hz,mul_zero,add_zero] using he

theorem active_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (hzero : ∃ i,k i=(0,0)) (he : ∃ i,k i=(0,1)) {p t : ℝ} (ht : 0<t)
    (hz : (centered k a (0,p) (0,t)).2=0) : 0<active k a p t := by
  have hV : 0<∑ i,(((k i).2:ℝ)-p)^2*faceMass (k i) (a i) t := by
    classical
    apply Finset.sum_pos'
    · intro i _
      apply mul_nonneg (sq_nonneg _)
      unfold faceMass
      split_ifs
      · exact mul_nonneg (ha i).le (pow_nonneg ht.le _)
      · rfl
    · by_cases hp : p=0
      · obtain ⟨i,hi⟩ := he
        exact ⟨i,Finset.mem_univ i,by simpa [faceMass,hi,hp] using mul_pos (ha i) ht⟩
      · obtain ⟨i,hi⟩ := hzero
        refine ⟨i,Finset.mem_univ i,?_⟩
        simpa [faceMass,hi] using mul_pos (sq_pos_of_ne_zero hp) (ha i)
  rw [← active_variance k a p t hz] at hV
  exact (mul_pos_iff_of_pos_right ht).mp hV

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

theorem slopeNumerator_contDiff (k : ι → ℕ × ℕ) :
    ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => slopeNumerator k q.1 q.2) := by
  apply ContDiff.prodMk <;> apply ContDiff.sum <;> intro i _ <;> fun_prop

theorem slope_contDiffAt {k : ι → ℕ × ℕ} {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => slope k q.1 q.2) (a,r) :=
  ((polynomial_contDiff k).contDiffAt.inv hP).smul (slopeNumerator_contDiff k).contDiffAt

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

theorem moment_eq_of_centered {k : ι → ℕ × ℕ} {a : ι → ℝ} {p r : Plane}
    (hP : polynomial k a r≠0) (hz : centered k a p r=0) : moment k a r=p := by
  rw [centered_eq,sub_eq_zero] at hz
  rw [moment,hz,smul_smul,inv_mul_cancel₀ hP,one_smul]

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

theorem active_origin_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (he : ∃ i,k i=(0,1)) : 0<active k a 0 0 := by
  classical
  have heq : active k a 0 0=∑ i,if (k i).1=0 ∧ (k i).2=1 then a i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (k i).1=0
    · simp only [ite_eq_left h,sub_zero]
      have hmul : ((k i).2:ℝ)*a i*((k i).2:ℝ)*(0:ℝ)^((k i).2-1)=
          ((k i).2:ℝ)*a i*(((k i).2:ℝ)*(0:ℝ)^((k i).2-1)) := by ring
      rw [hmul,zero_power_derivative]
      by_cases h1 : (k i).2=1 <;> simp [h,h1]
    · simp [h]
  rw [heq]
  apply Finset.sum_pos'
  · intro i _
    split_ifs
    · exact (ha i).le
    · rfl
  · obtain ⟨i,hi⟩ := he
    exact ⟨i,Finset.mem_univ i,by simpa [hi] using ha i⟩

theorem centeredDerivative_axis_isInvertible {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    (centeredDerivative k a (moment k a (0,t)) (0,t)).IsInvertible := by
  let p := (moment k a (0,t)).2
  have hm : moment k a (0,t)=(0,p) := Prod.ext (moment_axis_fst k a t) rfl
  rw [hm]
  have hz : (centered k a (0,p) (0,t)).2=0 := by
    have h := centered_moment (polynomial_pos (r := (0,t)) ha hzero ⟨le_rfl,ht⟩).ne'
    rw [hm] at h
    exact congrArg Prod.snd h
  have hA : 0<transverse k a t := transverse_pos ha he0 ht
  have hB : 0<active k a p t := by
    rcases eq_or_lt_of_le ht with ht0|htp
    · have hp : p=0 := by simp [p,← ht0,moment_origin]
      rw [← ht0,hp]
      exact active_origin_pos ha he1
    · exact active_pos ha hzero he1 htp hz
  have hker : ∀ v,centeredDerivative k a (0,p) (0,t) v=0 → v=0 := by
    intro v hv
    have h0 := congrArg Prod.fst hv
    rw [centeredDerivative_axis_fst] at h0
    change transverse k a t*v.1=0 at h0
    have hv0 : v.1=0 := (mul_eq_zero.mp h0).resolve_left hA.ne'
    have heq : v=(0,v.2) := Prod.ext hv0 rfl
    have h1 := congrArg Prod.snd hv
    rw [heq,centeredDerivative_axis_snd] at h1
    change active k a p t*v.2=0 at h1
    exact Prod.ext hv0 ((mul_eq_zero.mp h1).resolve_left hB.ne')
  have hi : Injective (centeredDerivative k a (0,p) (0,t)) := by
    intro v u h
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub,h,sub_self]
  let L := ContinuousLinearEquiv.ofBijective (centeredDerivative k a (0,p) (0,t))
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi))
  exact ⟨L,rfl⟩

theorem exists_smooth_axis_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a (0,t))=(0,t) ∧
      ContDiffAt ℝ ∞ f (a,moment k a (0,t)) ∧
      ∀ᶠ q in 𝓝 (a,moment k a (0,t)),centered k q.1 q.2 (f q)=0 := by
  let q := (a,moment k a (0,t))
  let r : Plane := (0,t)
  let F : ((ι → ℝ) × Plane) × Plane → Plane := fun s => centered k s.1.1 s.1.2 s.2
  have hF : ContDiff ℝ ∞ F := centered_contDiff k
  have hpartial : (fderiv ℝ F (q,r)).comp (ContinuousLinearMap.inr ℝ ((ι → ℝ) × Plane) Plane)=
      centeredDerivative k a (moment k a (0,t)) r := by
    have hc := ((hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (q,r)).hasFDerivAt.comp r
      ((hasFDerivAt_const q r).prodMk (hasFDerivAt_id r)))
    exact hc.unique (centered_hasFDerivAt k a (moment k a (0,t)) r)
  have hinv : (fderiv ℝ F (q,r) ∘L ContinuousLinearMap.inr ℝ ((ι → ℝ) × Plane) Plane).IsInvertible := by
    rw [hpartial]
    exact centeredDerivative_axis_isInvertible ha hzero he0 he1 ht
  have hz : F (q,r)=0 := centered_moment (polynomial_pos (r := (0,t)) ha hzero ⟨le_rfl,ht⟩).ne'
  refine ⟨hF.contDiffAt.implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv,?_,
    hF.contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv,?_⟩
  · exact hF.contDiffAt.implicitFunction_apply_self (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv
  · simpa only [hz] using hF.contDiffAt.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv

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

theorem centered_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (p r : Plane) :
    centered (fun i => (k i).swap) a p.swap r.swap=(centered k a p r).swap := by
  apply Prod.ext <;> apply Finset.sum_congr rfl <;> intro i _
  all_goals simp only [monomial,Prod.fst_swap,Prod.snd_swap]; ring

theorem exists_smooth_other_axis_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a (t,0))=(t,0) ∧
      ContDiffAt ℝ ∞ f (a,moment k a (t,0)) ∧
      ∀ᶠ q in 𝓝 (a,moment k a (t,0)),centered k q.1 q.2 (f q)=0 := by
  have hzero' : ∃ i,(k i).swap=(0,0) := by
    obtain ⟨i,hi⟩ := hzero
    exact ⟨i,by simp [hi]⟩
  have he0' : ∃ i,(k i).swap=(1,0) := by
    obtain ⟨i,hi⟩ := he1
    exact ⟨i,by simp [hi]⟩
  have he1' : ∃ i,(k i).swap=(0,1) := by
    obtain ⟨i,hi⟩ := he0
    exact ⟨i,by simp [hi]⟩
  obtain ⟨f,hf,hfs,hfe⟩ := exists_smooth_axis_radial_solution ha hzero' he0' he1' ht
  have hm : moment (fun i => (k i).swap) a (0,t)=(moment k a (t,0)).swap :=
    moment_swap k a (t,0)
  rw [hm] at hf hfs hfe
  let F : (ι → ℝ) × Plane → Plane := fun q => (f (q.1,q.2.swap)).swap
  have hswap : ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,q.2.swap)) := by
    change ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,(q.2.2,q.2.1)))
    fun_prop
  refine ⟨F,?_,?_,?_⟩
  · dsimp [F]
    rw [hf]
    rfl
  · have hc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => f (q.1,q.2.swap))
        (a,moment k a (t,0)) := hfs.comp (a,moment k a (t,0)) hswap.contDiffAt
    exact hc.snd.prodMk hc.fst
  · have htend : Tendsto (fun q : (ι → ℝ) × Plane => (q.1,q.2.swap))
        (𝓝 (a,moment k a (t,0))) (𝓝 (a,(moment k a (t,0)).swap)) :=
      hswap.continuous.continuousAt
    have he := htend.eventually hfe
    filter_upwards [he] with q hq
    have h := congrArg Prod.swap hq
    have hr : centered k q.1 q.2 (F q)=
        (centered (fun i => (k i).swap) q.1 q.2.swap (f (q.1,q.2.swap))).swap := by
      have hh := centered_swap k q.1 q.2 (F q)
      simp only [F,Prod.swap_swap] at hh
      exact (congrArg Prod.swap hh).symm
    rw [hr,h]
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




theorem exists_smooth_boundary_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=r ∧ ContDiffAt ℝ ∞ f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),centered k q.1 q.2 (f q)=0 := by
  rcases r with ⟨s,t⟩
  rcases hb with hs|ht
  · change s=0 at hs
    subst s
    exact exists_smooth_axis_radial_solution ha hzero he0 he1 hr.2
  · change t=0 at ht
    subst t
    exact exists_smooth_other_axis_radial_solution ha hzero he0 he1 hr.1

theorem exists_smooth_boundary_moment_inverse {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=r ∧ ContDiffAt ℝ ∞ f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),
        moment k q.1 (f q)=q.2 ∧
        (0≤(f q).1 ↔ 0≤q.2.1) ∧ (0≤(f q).2 ↔ 0≤q.2.2) ∧
        (0<(f q).1 ↔ 0<q.2.1) ∧ (0<(f q).2 ↔ 0<q.2.2) := by
  obtain ⟨f,hf,hfs,hfe⟩ := exists_smooth_boundary_radial_solution ha hzero he0 he1 hr hb
  let q0 := (a,moment k a r)
  have hc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,f q)) q0 :=
    contDiffAt_fst.prodMk hfs
  have hP := polynomial_pos ha hzero hr
  have hPc : ContinuousAt (fun q : (ι → ℝ) × Plane => polynomial k q.1 (f q)) q0 :=
    (polynomial_contDiff k).continuous.continuousAt.comp hc.continuousAt
  have hPe : ∀ᶠ q in 𝓝 q0,0<polynomial k q.1 (f q) := by
    apply hPc.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hP)
  have hsc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => slope k q.1 (f q)) q0 := by
    have hs := slope_contDiffAt hP.ne'
    have hh : (a,r)=(q0.1,f q0) := by simp [q0,hf]
    rw [hh] at hs
    exact hs.comp q0 hc
  have hs := slope_pos ha hzero he0 he1 hr
  have hse0 : ∀ᶠ q in 𝓝 q0,0<(slope k q.1 (f q)).1 := by
    apply hsc.continuousAt.fst.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hs.1)
  have hse1 : ∀ᶠ q in 𝓝 q0,0<(slope k q.1 (f q)).2 := by
    apply hsc.continuousAt.snd.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hs.2)
  refine ⟨f,hf,hfs,?_⟩
  filter_upwards [hfe,hPe,hse0,hse1] with q hq hPq hs0 hs1
  have hm := moment_eq_of_centered hPq.ne' hq
  refine ⟨hm,?_,?_,?_,?_⟩
  all_goals
    have he := moment_eq_radius_slope k q.1 (f q)
    rw [hm] at he
  · rw [show q.2.1=(f q).1*(slope k q.1 (f q)).1 from congrArg Prod.fst he]
    exact (mul_nonneg_iff_of_pos_right hs0).symm
  · rw [show q.2.2=(f q).2*(slope k q.1 (f q)).2 from congrArg Prod.snd he]
    exact (mul_nonneg_iff_of_pos_right hs1).symm
  · rw [show q.2.1=(f q).1*(slope k q.1 (f q)).1 from congrArg Prod.fst he]
    exact (mul_pos_iff_of_pos_right hs0).symm
  · rw [show q.2.2=(f q).2*(slope k q.1 (f q)).2 from congrArg Prod.snd he]
    exact (mul_pos_iff_of_pos_right hs1).symm




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

theorem boundary_inverse_smooth_extension {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=nonnegativeInverse k a (moment k a r) ∧
      ContDiffAt ℝ ∞ f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),
        (∀ i,0<q.1 i) → 0≤q.2.1 → 0≤q.2.2 → nonnegativeInverse k q.1 q.2=f q := by
  obtain ⟨f,hf,hfs,hfe⟩ := exists_smooth_boundary_moment_inverse ha h0 he0 he1 hr hb
  refine ⟨f,hf.trans (nonnegativeInverse_of_moment ha h0 he0 he1 hr).symm,hfs,?_⟩
  filter_upwards [hfe] with q hq hqa hq0 hq1
  exact nonnegativeInverse_eq_of_moment hqa h0 he0 he1
    ⟨hq.2.1.mpr hq0,hq.2.2.1.mpr hq1⟩ hq.1

theorem boundary_inverse_coeff_contDiffAt {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ContDiffAt ℝ ∞ (fun b : ι → ℝ => nonnegativeInverse k b (moment k a r)) a := by
  obtain ⟨f,hf,hfs,hfe⟩ := boundary_inverse_smooth_extension ha h0 he0 he1 hr hb
  have hmap : ContDiff ℝ ∞ (fun b : ι → ℝ => (b,moment k a r)) := by fun_prop
  have hfc : ContDiffAt ℝ ∞ (fun b : ι → ℝ => f (b,moment k a r)) a :=
    hfs.comp a hmap.contDiffAt
  apply hfc.congr_of_eventuallyEq
  have hmapt : Tendsto (fun b : ι → ℝ => (b,moment k a r)) (𝓝 a) (𝓝 (a,moment k a r)) :=
    hmap.continuous.continuousAt
  have hape : ∀ᶠ b in 𝓝 a,∀ i,0<b i := positiveCoefficients_isOpen.mem_nhds ha
  filter_upwards [hmapt.eventually hfe,hape] with b hb hba
  have hsm := slope_pos ha h0 he0 he1 hr
  have hmr : 0≤(moment k a r).1 ∧ 0≤(moment k a r).2 := by
    rw [moment_eq_radius_slope]
    exact ⟨mul_nonneg hr.1 hsm.1.le,mul_nonneg hr.2 hsm.2.le⟩
  exact hb hba hmr.1 hmr.2


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

theorem trapezoid_inverse_spec {A B : ℕ} (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) : moment latticeIndex a (nonnegativeInverse latticeIndex a p)=p :=
  nonnegativeInverse_spec (trapezoid_radial_surjective hAB ha hp)


end

section

open scoped BigOperators Topology ContDiff
open Set Filter Function
variable {ι : Type*} [Fintype ι]

theorem planeVector_contDiff : ContDiff ℝ ∞ (fun r : Plane => planeVector r.1 r.2) := by
  apply (contDiff_piLp 2).mpr
  intro j
  fin_cases j
  · exact contDiff_fst
  · exact contDiff_snd

theorem expRadius_contDiff : ContDiff ℝ ∞ expRadius := by
  apply ContDiff.prodMk <;> apply ContDiff.exp <;> fun_prop

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

theorem nonnegativeInverse_interior_contDiffAt [Nonempty ι] {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : Surrounds (weight k) (planeVector p.1 p.2)) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => nonnegativeInverse k q.1 q.2) (a,p) := by
  have hmap : ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,planeVector q.2.1 q.2.2)) :=
    contDiff_fst.prodMk (planeVector_contDiff.comp contDiff_snd)
  have hs := expRadius_contDiff.contDiffAt.comp (a,p)
    ((inverse_contDiffAt ha hp).comp (a,p) hmap.contDiffAt)
  apply hs.congr_of_eventuallyEq
  have hae : ∀ᶠ q : (ι → ℝ) × Plane in 𝓝 (a,p),∀ i,0<q.1 i :=
    (positiveCoefficients_isOpen.preimage continuous_fst).mem_nhds ha
  have hpe : ∀ᶠ q : (ι → ℝ) × Plane in 𝓝 (a,p),Surrounds (weight k) (planeVector q.2.1 q.2.2) :=
    ((surrounds_isOpen (weight k)).preimage (planeVector_contDiff.continuous.comp continuous_snd)).mem_nhds hp
  filter_upwards [hae,hpe] with q hqa hqp
  exact nonnegativeInverse_exp hqa h0 he0 he1 hqp


end


open scoped BigOperators Topology ContDiff
open Set Filter Function

theorem trapezoid_inverse_coeff_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ContDiffAt ℝ ∞ (fun b : TrapezoidWeight A B → ℝ => nonnegativeInverse latticeIndex b p) a := by
  by_cases hb : p.1=0 ∨ p.2=0
  · let r := nonnegativeInverse (latticeIndex (A:=A) (B:=B)) a p
    have hr := nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a p
    have he : moment latticeIndex a r=p := trapezoid_inverse_spec hAB ha hp
    have hz := moment_zero_coordinates ha (lattice_zero A B) (lattice_unit_fst hA hAB)
      (lattice_unit_snd hA hAB) hr
    have hbr : r.1=0 ∨ r.2=0 := by
      rw [he] at hz
      exact hb.elim (fun h => Or.inl (hz.1.mp h)) (fun h => Or.inr (hz.2.mp h))
    have hs := boundary_inverse_coeff_contDiffAt ha (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) hr hbr
    rwa [he] at hs
  · have hp0 : 0<p.1 := lt_of_le_of_ne hp.1 (Ne.symm (fun h => hb (Or.inl h)))
    have hp1 : 0<p.2 := lt_of_le_of_ne hp.2.2.1 (Ne.symm (fun h => hb (Or.inr h)))
    have hs : ContDiffAt ℝ ∞
        (fun q : (TrapezoidWeight A B → ℝ) × Plane => nonnegativeInverse latticeIndex q.1 q.2) (a,p) :=
      nonnegativeInverse_interior_contDiffAt ha (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
      (trapezoidWeight_surrounds hAB ⟨hp0,hp.2.1,hp1,hp.2.2.2⟩)
    have hmap : ContDiffAt ℝ ∞ (fun b : TrapezoidWeight A B → ℝ => (b,p)) a :=
      contDiffAt_id.prodMk contDiffAt_const
    have hc := hs.comp a hmap
    exact hc



end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_AnalyticBoundary
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

theorem centered_contDiff_analytic (k : ι → ℕ × ℕ) :
    ContDiff ℝ ω (fun q : ((ι → ℝ) × Plane) × Plane => centered k q.1.1 q.1.2 q.2) := by
  apply ContDiff.prodMk <;> apply ContDiff.sum <;> intro i _ <;> dsimp [monomial] <;> fun_prop

theorem exists_analytic_axis_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a (0,t))=(0,t) ∧
      ContDiffAt ℝ ω f (a,moment k a (0,t)) ∧
      ∀ᶠ q in 𝓝 (a,moment k a (0,t)),centered k q.1 q.2 (f q)=0 := by
  let q := (a,moment k a (0,t))
  let r : Plane := (0,t)
  let F : ((ι → ℝ) × Plane) × Plane → Plane := fun s => centered k s.1.1 s.1.2 s.2
  have hF : ContDiff ℝ ω F := centered_contDiff_analytic k
  have hpartial : (fderiv ℝ F (q,r)).comp (ContinuousLinearMap.inr ℝ ((ι → ℝ) × Plane) Plane)=
      centeredDerivative k a (moment k a (0,t)) r := by
    have hc := ((hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (q,r)).hasFDerivAt.comp r
      ((hasFDerivAt_const q r).prodMk (hasFDerivAt_id r)))
    exact hc.unique (centered_hasFDerivAt k a (moment k a (0,t)) r)
  have hinv : (fderiv ℝ F (q,r) ∘L ContinuousLinearMap.inr ℝ ((ι → ℝ) × Plane) Plane).IsInvertible := by
    rw [hpartial]
    exact centeredDerivative_axis_isInvertible ha hzero he0 he1 ht
  have hz : F (q,r)=0 := centered_moment (polynomial_pos (r := (0,t)) ha hzero ⟨le_rfl,ht⟩).ne'
  refine ⟨hF.contDiffAt.implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv,?_,
    hF.contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv,?_⟩
  · exact hF.contDiffAt.implicitFunction_apply_self (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv
  · simpa only [hz] using hF.contDiffAt.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv

theorem exists_analytic_other_axis_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a (t,0))=(t,0) ∧
      ContDiffAt ℝ ω f (a,moment k a (t,0)) ∧
      ∀ᶠ q in 𝓝 (a,moment k a (t,0)),centered k q.1 q.2 (f q)=0 := by
  have hzero' : ∃ i,(k i).swap=(0,0) := by
    obtain ⟨i,hi⟩ := hzero
    exact ⟨i,by simp [hi]⟩
  have he0' : ∃ i,(k i).swap=(1,0) := by
    obtain ⟨i,hi⟩ := he1
    exact ⟨i,by simp [hi]⟩
  have he1' : ∃ i,(k i).swap=(0,1) := by
    obtain ⟨i,hi⟩ := he0
    exact ⟨i,by simp [hi]⟩
  obtain ⟨f,hf,hfs,hfe⟩ := exists_analytic_axis_radial_solution ha hzero' he0' he1' ht
  have hm : moment (fun i => (k i).swap) a (0,t)=(moment k a (t,0)).swap :=
    moment_swap k a (t,0)
  rw [hm] at hf hfs hfe
  let F : (ι → ℝ) × Plane → Plane := fun q => (f (q.1,q.2.swap)).swap
  have hswap : ContDiff ℝ ω (fun q : (ι → ℝ) × Plane => (q.1,q.2.swap)) := by
    change ContDiff ℝ ω (fun q : (ι → ℝ) × Plane => (q.1,(q.2.2,q.2.1)))
    fun_prop
  refine ⟨F,?_,?_,?_⟩
  · dsimp [F]
    rw [hf]
    rfl
  · have hc : ContDiffAt ℝ ω (fun q : (ι → ℝ) × Plane => f (q.1,q.2.swap))
        (a,moment k a (t,0)) := hfs.comp (a,moment k a (t,0)) hswap.contDiffAt
    exact hc.snd.prodMk hc.fst
  · have htend : Tendsto (fun q : (ι → ℝ) × Plane => (q.1,q.2.swap))
        (𝓝 (a,moment k a (t,0))) (𝓝 (a,(moment k a (t,0)).swap)) :=
      hswap.continuous.continuousAt
    have he := htend.eventually hfe
    filter_upwards [he] with q hq
    have h := congrArg Prod.swap hq
    have hr : centered k q.1 q.2 (F q)=
        (centered (fun i => (k i).swap) q.1 q.2.swap (f (q.1,q.2.swap))).swap := by
      have hh := centered_swap k q.1 q.2 (F q)
      simp only [F,Prod.swap_swap] at hh
      exact (congrArg Prod.swap hh).symm
    rw [hr,h]
    rfl

theorem exists_analytic_boundary_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=r ∧ ContDiffAt ℝ ω f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),centered k q.1 q.2 (f q)=0 := by
  rcases r with ⟨s,t⟩
  rcases hb with hs|ht
  · change s=0 at hs
    subst s
    exact exists_analytic_axis_radial_solution ha hzero he0 he1 hr.2
  · change t=0 at ht
    subst t
    exact exists_analytic_other_axis_radial_solution ha hzero he0 he1 hr.1

theorem exists_analytic_boundary_moment_inverse {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=r ∧ ContDiffAt ℝ ω f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),
        moment k q.1 (f q)=q.2 ∧
        (0≤(f q).1 ↔ 0≤q.2.1) ∧ (0≤(f q).2 ↔ 0≤q.2.2) ∧
        (0<(f q).1 ↔ 0<q.2.1) ∧ (0<(f q).2 ↔ 0<q.2.2) := by
  obtain ⟨f,hf,hfs,hfe⟩ := exists_analytic_boundary_radial_solution ha hzero he0 he1 hr hb
  let q0 := (a,moment k a r)
  have hc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,f q)) q0 :=
    contDiffAt_fst.prodMk (hfs.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hP := polynomial_pos ha hzero hr
  have hPc : ContinuousAt (fun q : (ι → ℝ) × Plane => polynomial k q.1 (f q)) q0 :=
    (polynomial_contDiff k).continuous.continuousAt.comp hc.continuousAt
  have hPe : ∀ᶠ q in 𝓝 q0,0<polynomial k q.1 (f q) := by
    apply hPc.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hP)
  have hsc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => slope k q.1 (f q)) q0 := by
    have hs := slope_contDiffAt hP.ne'
    have hh : (a,r)=(q0.1,f q0) := by simp [q0,hf]
    rw [hh] at hs
    exact hs.comp q0 hc
  have hs := slope_pos ha hzero he0 he1 hr
  have hse0 : ∀ᶠ q in 𝓝 q0,0<(slope k q.1 (f q)).1 := by
    apply hsc.continuousAt.fst.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hs.1)
  have hse1 : ∀ᶠ q in 𝓝 q0,0<(slope k q.1 (f q)).2 := by
    apply hsc.continuousAt.snd.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hs.2)
  refine ⟨f,hf,hfs,?_⟩
  filter_upwards [hfe,hPe,hse0,hse1] with q hq hPq hs0 hs1
  have hm := moment_eq_of_centered hPq.ne' hq
  refine ⟨hm,?_,?_,?_,?_⟩
  all_goals
    have he := moment_eq_radius_slope k q.1 (f q)
    rw [hm] at he
  · rw [show q.2.1=(f q).1*(slope k q.1 (f q)).1 from congrArg Prod.fst he]
    exact (mul_nonneg_iff_of_pos_right hs0).symm
  · rw [show q.2.2=(f q).2*(slope k q.1 (f q)).2 from congrArg Prod.snd he]
    exact (mul_nonneg_iff_of_pos_right hs1).symm
  · rw [show q.2.1=(f q).1*(slope k q.1 (f q)).1 from congrArg Prod.fst he]
    exact (mul_pos_iff_of_pos_right hs0).symm
  · rw [show q.2.2=(f q).2*(slope k q.1 (f q)).2 from congrArg Prod.snd he]
    exact (mul_pos_iff_of_pos_right hs1).symm

theorem trapezoid_inverse_open_representative {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ∃ U : Set ((TrapezoidWeight A B → ℝ) × Plane), ∃ f : ((TrapezoidWeight A B → ℝ) × Plane) → Plane,
      IsOpen U ∧ (a,p)∈U ∧ ContDiffOn ℝ ∞ f U ∧
      ∀ q∈U,(∀ i,0<q.1 i) → q.2∈lowerTrapezoid A B →
        f q=nonnegativeInverse latticeIndex q.1 q.2 := by
  by_cases hb : p.1=0 ∨ p.2=0
  · let r := nonnegativeInverse (latticeIndex (A:=A) (B:=B)) a p
    have hr := nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a p
    have he : moment latticeIndex a r=p := trapezoid_inverse_spec hAB ha hp
    have hz := moment_zero_coordinates ha (lattice_zero A B) (lattice_unit_fst hA hAB)
      (lattice_unit_snd hA hAB) hr
    have hbr : r.1=0 ∨ r.2=0 := by
      rw [he] at hz
      exact hb.elim (fun h => Or.inl (hz.1.mp h)) (fun h => Or.inr (hz.2.mp h))
    obtain ⟨f,hf,hfs,hfe⟩ := exists_analytic_boundary_moment_inverse ha (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) hr hbr
    rw [he] at hf hfs hfe
    obtain ⟨V,hV,hfV⟩ := hfs.contDiffOn (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (fun _ => rfl)
    obtain ⟨U,hUV,hU,hpU⟩ := mem_nhds_iff.mp (inter_mem hV hfe)
    refine ⟨U,f,hU,hpU,hfV.mono (fun q hq => (hUV hq).1),?_⟩
    intro q hq hqa hqp
    have hqf := (hUV hq).2
    exact (nonnegativeInverse_eq_of_moment hqa (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
      ⟨hqf.2.1.mpr hqp.1,hqf.2.2.1.mpr hqp.2.2.1⟩ hqf.1).symm
  · let U : Set ((TrapezoidWeight A B → ℝ) × Plane) :=
      {q | (∀ i,0<q.1 i) ∧ 0<q.2.1 ∧ q.2.1<A ∧ 0<q.2.2 ∧ q.2.1+q.2.2<B}
    have hU : IsOpen U := (positiveCoefficients_isOpen.preimage continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd.fst).inter
        ((isOpen_lt continuous_snd.fst continuous_const).inter
          ((isOpen_lt continuous_const continuous_snd.snd).inter
            (isOpen_lt (continuous_snd.fst.add continuous_snd.snd) continuous_const))))
    have hp0 : 0<p.1 := lt_of_le_of_ne hp.1 (Ne.symm (fun h => hb (Or.inl h)))
    have hp1 : 0<p.2 := lt_of_le_of_ne hp.2.2.1 (Ne.symm (fun h => hb (Or.inr h)))
    refine ⟨U,fun q => nonnegativeInverse latticeIndex q.1 q.2,hU,⟨ha,hp0,hp.2.1,hp1,hp.2.2.2⟩,?_,?_⟩
    · intro q hq
      exact (nonnegativeInverse_interior_contDiffAt hq.1 (lattice_zero A B)
        (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
        (trapezoidWeight_surrounds hAB hq.2)).contDiffWithinAt
    · intros
      rfl

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι : Type*} [Fintype ι]

theorem probability_contDiffAt (k : ι → ℕ × ℕ) {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) (i : ι) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => probability k q.1 q.2 i) (a,r) := by
  apply ContDiffAt.div _ (polynomial_contDiff k).contDiffAt hP
  dsimp [monomial]
  fun_prop

end

theorem trapezoid_selected_coeff_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) (i : TrapezoidWeight A B) :
    ContDiffAt ℝ ∞ (fun b : TrapezoidWeight A B → ℝ => selected latticeIndex b p i) a := by
  have hi := trapezoid_inverse_coeff_contDiffAt hA hAB ha hp
  have hs := probability_contDiffAt latticeIndex
    (polynomial_pos ha (lattice_zero A B) (nonnegativeInverse_nonneg latticeIndex a p)).ne' i
  have hmap := contDiffAt_id.prodMk hi
  have hc := hs.comp a hmap
  exact hc

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_local_smooth_extension {K S : Set E} (hK : IsCompact K) (g : E → F)
    (hlocal : ∀ x∈K, ∃ U : Set E, ∃ f : E → F,
      IsOpen U ∧ x∈U ∧ ContDiffOn ℝ ∞ f U ∧ ∀ y∈U,y∈S → f y=g y) :
    ∃ f : E → F, ContDiff ℝ ∞ f ∧ ∀ᶠ y in 𝓝ˢ K,y∈S → f y=g y := by
  classical
  choose U f hU hmem hf he using (fun x : K => hlocal x.val x.property)
  have hKU : K⊆⋃ x : K,U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hmem ⟨x,hx⟩⟩
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK (isOpen_iUnion hU) hKU
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,E) hL.isClosed U hU hLU
  refine ⟨fun y => ∑ᶠ i,ρ i y • f i y,
    (hρ.contMDiff_finsum_smul hU (fun i => (hf i).contMDiffOn)).contDiff,?_⟩
  filter_upwards [isOpen_interior.mem_nhdsSet.mpr hKL] with y hy hyS
  have ht : (fun i : K => ρ i y • f i y)=(fun i : K => ρ i y • g y) := by
    funext i
    by_cases hi : ρ i y=0
    · simp [hi]
    · rw [he i y (hρ i (subset_closure hi)) hyS]
  rw [ht,← finsum_smul,ρ.sum_eq_one (interior_subset hy),one_smul]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

theorem trapezoid_selected_open_representative {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ∃ U : Set ((TrapezoidWeight A B → ℝ) × Plane),
      ∃ f : ((TrapezoidWeight A B → ℝ) × Plane) → (TrapezoidWeight A B → ℝ),
      IsOpen U ∧ (a,p)∈U ∧ ContDiffOn ℝ ∞ f U ∧
      ∀ q∈U,(∀ i,0<q.1 i) → q.2∈lowerTrapezoid A B →
        f q=selected latticeIndex q.1 q.2 := by
  obtain ⟨U,f,hU,hqU,hf,he⟩ := trapezoid_inverse_open_representative hA hAB ha hp
  have hs : ContDiffAt ℝ ∞ (fun q => (q.1,f q)) (a,p) :=
    contDiffAt_fst.prodMk ((hf (a,p) hqU).contDiffAt (hU.mem_nhds hqU))
  have hP : 0<polynomial latticeIndex a (f (a,p)) := by
    rw [he (a,p) hqU ha hp]
    exact polynomial_pos ha (lattice_zero A B) (nonnegativeInverse_nonneg _ _ _)
  have hPe : ∀ᶠ q in 𝓝 (a,p),0<polynomial latticeIndex q.1 (f q) :=
    ((polynomial_contDiff latticeIndex).continuous.continuousAt.comp hs.continuousAt).eventually
      (eventually_gt_nhds hP)
  obtain ⟨V,hVU,hV,hqV⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hqU) hPe)
  refine ⟨V,fun q => probability latticeIndex q.1 (f q),hV,hqV,?_,?_⟩
  · rw [contDiffOn_pi]
    intro i q hq
    exact ((probability_contDiffAt latticeIndex ((hVU hq).2.ne') i).comp_contDiffWithinAt q
      (contDiffWithinAt_fst.prodMk ((hf q (hVU hq).1).mono (fun z hz => (hVU hz).1))))
  · intro q hq hqa hqp
    dsimp only
    rw [he q (hVU hq).1 hqa hqp]
    rfl

theorem trapezoid_selected_compact_extension {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {K : Set ((TrapezoidWeight A B → ℝ) × Plane)} (hK : IsCompact K)
    (hKS : ∀ q∈K,(∀ i,0<q.1 i) ∧ q.2∈lowerTrapezoid A B) :
    ∃ f : ((TrapezoidWeight A B → ℝ) × Plane) → (TrapezoidWeight A B → ℝ),
      ContDiff ℝ ∞ f ∧ ∃ U : Set ((TrapezoidWeight A B → ℝ) × Plane),
        IsOpen U ∧ K⊆U ∧ ∀ q∈U,(∀ i,0<q.1 i) → q.2∈lowerTrapezoid A B →
          f q=selected latticeIndex q.1 q.2 := by
  obtain ⟨f,hf,he⟩ := Hamiltonian.compact_local_smooth_extension
    (S := {q | (∀ i,0<q.1 i) ∧ q.2∈lowerTrapezoid A B}) hK
    (fun q => selected latticeIndex q.1 q.2) (by
      intro q hq
      obtain ⟨U,f,hU,hqU,hf,he⟩ := trapezoid_selected_open_representative hA hAB (hKS q hq).1 (hKS q hq).2
      exact ⟨U,f,hU,hqU,hf,fun y hy hys => he y hy hys.1 hys.2⟩)
  obtain ⟨U,hU,hKU,hUS⟩ := mem_nhdsSet_iff_exists.mp he
  exact ⟨f,hf,U,hU,hKU,fun q hq hqa hqp => hUS hq ⟨hqa,hqp⟩⟩

end PackingSufficiencySupport.FiniteMoment.Radial
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
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
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

 theorem compactSurfaceFormIntegral_congr {D : Set M} (hD : IsCompact D)
    {Ω Λ : ManifoldTwoForm Plane M} (h : EqOn Ω Λ D) :
    compactSurfaceFormIntegral hD Ω=compactSurfaceFormIntegral hD Λ := by
  unfold compactSurfaceFormIntegral
  rw [restrictedPartitionFormMass_eq_indicator _ _ hD.isClosed.measurableSet,
    restrictedPartitionFormMass_eq_indicator _ _ hD.isClosed.measurableSet]
  congr 1
  exact Set.indicator_congr h

end
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
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem familySpatialExterior_smoothAt {Γ : P × E → E →L[ℝ] ℝ}
    {p : P × E} (hΓ : ContDiffAt ℝ ∞ Γ p) : ContDiffAt ℝ ∞ (familySpatialExterior Γ) p := by
  have hd : ContDiffAt ℝ ∞ (fun q => (fderiv ℝ Γ q).comp (ContinuousLinearMap.inr ℝ P E)) p :=
    (hΓ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiffAt_const
  have hflip : ContDiff ℝ ∞ (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ)
  exact hd.sub (hflip.contDiffAt.comp p hd)

 theorem familySpatialExterior_eq_slice {Γ : P × E → E →L[ℝ] ℝ}
    {p : P × E} (hΓ : DifferentiableAt ℝ Γ p) :
    familySpatialExterior Γ p=euclideanExteriorOneForm (fun x => Γ (p.1,x)) p.2 := by
  have hi : HasFDerivAt (fun y : E => (p.1,y))
      ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hh : HasFDerivAt Γ (fderiv ℝ Γ p) (p.1,p.2) := hΓ.hasFDerivAt
  have hs := (hh.comp p.2 hi).fderiv
  change fderiv ℝ (fun y => Γ (p.1,y)) p.2 = _ at hs
  unfold familySpatialExterior euclideanExteriorOneForm
  rw [hs]
  rfl

 theorem manifoldExteriorOneForm_family_smooth {Γ : P → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) : SmoothTwoFormFamily (fun p => manifoldExteriorOneForm (Γ p)) := by
  intro c p hp
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hp
  apply ((familySpatialExterior_smoothAt ((hΓ c).contDiffAt hn)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with q hq
  rw [manifoldExteriorOneForm_chart (fun b y hy => (hΓ.spatial_smooth q.1 b hy).contDiffWithinAt) hq.2]
  exact (familySpatialExterior_eq_slice (((hΓ c).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).symm

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_skew (α : ManifoldOneForm E M) (x : M) (v w : E) :
    manifoldExteriorOneForm α x v w = -manifoldExteriorOneForm α x w v := by
  change fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x v) (chartDifferential x x w) -
    fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x w) (chartDifferential x x v) = -_
  change _ = -(fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x w) (chartDifferential x x v) -
    fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x v) (chartDifferential x x w))
  ring

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

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicCoefficientDifferential
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι]

theorem radialProbability_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) (i : TrapezoidWeight A B) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (fun x => radialProbability Radial.latticeIndex D m p x i) := by
  have ha : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,TrapezoidWeight A B → ℝ) ∞
      (fun x : BaseCurve => fun j => coefficientNorm (D j) (m j) x) :=
    contMDiff_pi_space.mpr (fun j => coefficientNorm_smooth _ _)
  intro x
  have hs := Radial.trapezoid_selected_coeff_contDiffAt hA hAB
    (fun j => coefficientNorm_pos (D j) (m j) x) hp i
  have hc := hs.contMDiffAt.comp x ha.contMDiffAt
  exact hc

theorem radialPrimitive_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) (c : ℝ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) :
    SmoothOneFormFamily (fun _ : ℝ => radialPrimitive Radial.latticeIndex D m c p) := by
  have hs := SmoothOneFormFamily.sum Finset.univ (fun i _ =>
    (weightedFSPrimitive_smooth (D i) (m i) c).spatial_smul (radialProbability_smooth hA hAB D m hp i))
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext t x
  simp only [radialPrimitive,Finset.sum_apply]

theorem radialForm_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) (c : ℝ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) : SmoothTwoForm (radialForm Radial.latticeIndex D m c p) :=
  (manifoldExteriorOneForm_family_smooth (radialPrimitive_smooth hA hAB D m c hp)).eval 0

theorem radialForm_skew (k : ι → ℕ × ℕ) (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane)
    (x : BaseCurve) (v u : RealModel) : radialForm k D m c p x v u= -radialForm k D m c p x u v :=
  manifoldExteriorOneForm_skew _ _ _ _

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialFamilyExtension
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

 theorem exists_radialPrimitive_smooth_extension {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) (c : ℝ)
    {P : Set Radial.Plane} (hP : IsCompact P) (hPS : P⊆Radial.lowerTrapezoid A B)
    {C : Set BaseCurve} (hC : IsCompact C) :
    ∃ Γ : Radial.Plane → ManifoldOneForm RealModel BaseCurve,
      SmoothOneFormFamily Γ ∧ ∀ᶠ q in 𝓝ˢ (P ×ˢ C),q.1∈Radial.lowerTrapezoid A B →
        Γ q.1 q.2=radialPrimitive Radial.latticeIndex D m c q.1 q.2 := by
  let a : BaseCurve → TrapezoidWeight A B → ℝ := fun x i => coefficientNorm (D i) (m i) x
  have ha : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,TrapezoidWeight A B → ℝ) ∞ a :=
    contMDiff_pi_space.mpr (fun i => coefficientNorm_smooth _ _)
  let F : Radial.Plane × BaseCurve → (TrapezoidWeight A B → ℝ) × Radial.Plane :=
    fun q => (a q.2,q.1)
  have hF : Continuous F := (ha.continuous.comp continuous_snd).prodMk continuous_fst
  obtain ⟨g,hg,U,hU,hKU,he⟩ := Radial.trapezoid_selected_compact_extension hA hAB
    ((hP.prod hC).image hF) (by
      rintro q ⟨z,hz,rfl⟩
      exact ⟨fun i => coefficientNorm_pos _ _ _,hPS hz.1⟩)
  let Γ : Radial.Plane → ManifoldOneForm RealModel BaseCurve :=
    fun p x => ∑ i,g (a x,p) i • weightedFSPrimitive (D i) (m i) c x
  have hterm (i : TrapezoidWeight A B) : SmoothOneFormFamily
      (fun p : Radial.Plane => fun x => g (a x,p) i • weightedFSPrimitive (D i) (m i) c x) := by
    intro b q hq
    have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,RealModel)) (n := ∞) b).contMDiffAt
      ((isOpen_extChartAt_target b).mem_nhds hq.2)
    have hac : ContDiffAt ℝ ∞ (fun z : Radial.Plane × RealModel =>
        a ((extChartAt 𝓘(ℝ,RealModel) b).symm z.2)) q :=
      (ha.contMDiffAt.comp q.2 hi).contDiffAt.comp q contDiffAt_snd
    have hgc := ((contDiff_apply ℝ ℝ i).comp hg).contDiffAt.comp q
      (hac.prodMk contDiffAt_fst)
    have hw : SmoothOneFormFamily (fun _ : Radial.Plane => weightedFSPrimitive (D i) (m i) c) :=
      (weightedFSPrimitive_smooth (D i) (m i) c).comp (contDiff_const (c := (0:ℝ)))
    have hwc := (hw b).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target b)).mem_nhds hq)
    simpa only [chartOneForm_spatial_smul,Function.comp_apply,Pi.smul_def'] using (hgc.smul hwc).contDiffWithinAt
  refine ⟨Γ,?_,?_⟩
  · convert SmoothOneFormFamily.sum Finset.univ (fun i _ => hterm i) using 1
    all_goals try with_reducible_and_instances rfl
    funext p x
    simp only [Γ,Finset.sum_apply]
  · have hPU : P ×ˢ C⊆F ⁻¹' U := fun q hq => hKU (mem_image_of_mem F hq)
    filter_upwards [(hU.preimage hF).mem_nhdsSet.mpr hPU] with q hq hqp
    have hge := he (F q) hq (fun i => coefficientNorm_pos _ _ _) hqp
    change (∑ i,g (F q) i • weightedFSPrimitive (D i) (m i) c q.2)=_
    rw [hge]
    rfl

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold MeasureTheory
section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {I : Type*} [Fintype I] {K : Set M}

omit [Fintype I] in
theorem partitionChartDensity_family_continuous (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω) (i : I) :
    ∃ L : Set Plane,IsCompact L ∧
      Continuous (fun q : P × Plane => partitionChartDensity B ρ (Ω q.1) i q.2) ∧
      ∀ p y,y∉L → partitionChartDensity B ρ (Ω p) i y=0 := by
  let C := tsupport (ρ i)
  have hC : IsCompact C := (B i).isCompact_compactCarrier.of_isClosed_subset
    (isClosed_tsupport _) ((hρ i).trans (B i).carrier_subset_compactCarrier)
  have hCc : C⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source := fun _ hx => (hρ i hx).1
  have hs : SmoothTwoFormFamily (fun p : P => fun x => ρ i x • Ω p x) :=
    hΩ.spatial_smul (ρ i).contMDiff
  have hz : ∀ p x,x∉C→ρ i x • Ω p x=0 := by
    intro _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (0 : ℝ) * _ = 0
    exact zero_mul _
  refine ⟨(extChartAt 𝓘(ℝ,Plane) (B i).center) '' C,
    hC.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) (B i).center).mono hCc),?_,?_⟩
  · have hfull := extendedChartCoefficient_smooth (Ω := fun p : P => fun x => ρ i x • Ω p x)
      (c := (B i).center) (hs (B i).center) hC hCc hz
    exact hfull.continuous
  · intro p y hy
    exact extendedChartCoefficient_zero hz p hy

theorem restrictedPartitionFormMass_family_continuous (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) (C : Set M)
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω) :
    Continuous (fun p => restrictedPartitionFormMass B ρ C (Ω p)) := by
  apply continuous_finsetSum
  intro i _
  obtain ⟨L,hL,hf,hz⟩ := partitionChartDensity_family_continuous B ρ hρ hΩ i
  apply continuousOn_univ.mp
  exact continuousOn_integral_of_compact_support hL hf.continuousOn (fun p y _ hy => hz p y hy)

theorem compactSurfaceFormIntegral_family_continuous [T2Space M] [SigmaCompactSpace M]
    {C : Set M} (hC : IsCompact C) {Ω : P → ManifoldTwoForm Plane M}
    (hΩ : SmoothTwoFormFamily Ω) :
    Continuous (fun p => compactSurfaceFormIntegral hC (Ω p)) :=
  restrictedPartitionFormMass_family_continuous _ _ (compactSurfacePartition_subordinate hC) C hΩ

end

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

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

 attribute [local instance] OAI.PackingSufficiencySupport.CubicModel.radialFamilySigmaCompact
theorem radial_compact_area_continuousOn {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) (c : ℝ)
    {P : Set Radial.Plane} (hP : IsCompact P) (hPS : P⊆Radial.lowerTrapezoid A B)
    {C : Set BaseCurve} (hC : IsCompact C) :
    ContinuousOn (fun p => compactSurfaceFormIntegral hC
      (radialForm Radial.latticeIndex D m c p)) P := by
  obtain ⟨Γ,hΓ,he⟩ := exists_radialPrimitive_smooth_extension hA hAB D m c hP hPS hC
  have hd p (hp : p∈P) x (hx : x∈C) :
      manifoldExteriorOneForm (Γ p) x=radialForm Radial.latticeIndex D m c p x := by
    apply manifoldExteriorOneForm_congr_germ
    have hn := mem_nhdsSet_iff_forall.mp he (p,x) ⟨hp,hx⟩
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hn] with y hy
    exact hy (hPS hp)
  have heq : EqOn (fun p => compactSurfaceFormIntegral hC (manifoldExteriorOneForm (Γ p)))
      (fun p => compactSurfaceFormIntegral hC (radialForm Radial.latticeIndex D m c p)) P :=
    fun p hp => compactSurfaceFormIntegral_congr hC (fun x hx => hd p hp x hx)
  exact (compactSurfaceFormIntegral_family_continuous hC
    (manifoldExteriorOneForm_family_smooth hΓ)).continuousOn.congr heq.symm

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold

 theorem totalWeight_le {A B : ℕ} (k : TrapezoidWeight A B) : totalWeight k≤B := k.property.2

 theorem cubicMarked_lt_degree {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    (k : TrapezoidWeight A B) : cubicMarkedOrder S k < cubicDegree D k := by
  have hk := totalWeight_le k
  dsimp [cubicMarkedOrder,cubicDegree]
  omega

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricEndResidueMass
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

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricSmoothExhaustion
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact
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

end

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CubicAreaExhaustion
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian
open scoped BigOperators
open FiniteMoment
section

 theorem exists_small_cubic_end_cutoff : ∃ (g : ℝ → ℝ) (r R : ℝ),0 < r ∧ 0<R ∧ R<1 ∧
    ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ t,g t∈Icc (0:ℝ) 1) ∧
    (∀ t∈Ioo (-r) r,g t=1) ∧ tsupport g⊆Iic R ∧
    {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion := by
  obtain ⟨d,hd,hdb⟩ := Metric.mem_nhds_iff.mp
    (endRegularRegion_open.mem_nhds zero_mem_endRegularRegion)
  let e := min d 1
  have he : 0<e := lt_min hd (by norm_num)
  have hed : e≤d := min_le_left _ _
  have he1 : e≤1 := min_le_right _ _
  let R := (e/2)^2
  have hR : 0<R := sq_pos_of_pos (by linarith)
  have hR1 : R<1 := by dsimp [R] <;> nlinarith
  have hreg : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion := by
    intro s hs
    apply hdb
    rw [Metric.mem_ball,dist_zero_right]
    have hn : ‖s‖≤e/2 := (sq_le_sq₀ (norm_nonneg s) (by linarith : 0≤e/2)).mp (by
      simpa only [Complex.normSq_eq_norm_sq,R,mem_ofPred_eq] using hs)
    linarith
  obtain ⟨g,hg,hgc,hgs,hg1,hgb⟩ := exists_smooth_cutoff
    (isCompact_Icc : IsCompact (Icc (-R/2) (R/2))) isOpen_Ioo
    (show Icc (-R/2) (R/2)⊆Ioo (-R) R by intro t ht; constructor <;> linarith [ht.1,ht.2])
  refine ⟨g,R/2,R,by linarith,hR,hR1,hg,hgc,hgb,?_,?_,hreg⟩
  · intro t ht
    have heq : g=ᶠ[𝓝 t] fun _ => 1 := hg1.filter_mono
      (nhds_le_nhdsSet (show t∈Icc (-R/2) (R/2) by constructor <;> linarith [ht.1,ht.2]))
    exact heq.eq_of_nhds
  · exact fun t ht => (hgs ht).2.le

end

 attribute [local instance] OAI.PackingSufficiencySupport.CubicModel.radialCubicCompactAreaSigmaCompact
theorem radial_cubic_compact_area_le {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) {c : ℝ} (hc : 0 < c)
    {K : Set BaseCurve} (hK : IsCompact K) :
    compactSurfaceFormIntegral hK
      (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)≤
      c*(3*((D:ℝ)-3*(p.1+p.2))-2*markedHeight S (planeVector p.1 p.2))*Real.pi := by
  obtain ⟨g,r,R,hr,hR,hR1,hg,hgc,hgb,h1,h0,hreg⟩ := exists_small_cubic_end_cutoff
  apply ge_of_tendsto (tendsto_radial_cubic_cutoff_mass_bp240 hA hS0 hAB hSB hB hS hp hg hgc hr hR hR1 hreg h1 h0 c)
  filter_upwards [curveEndCutoff_eventually_one_on_compact (parameters 0) hR.le h0 hK] with n hn
  exact compactIntegral_le_surfaceCutoffMass (positivePlaneTransitions (parameters 0)) hK
    (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)
    (curveEndCutoff_smooth (parameters 0) (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n))
    (fun x => (curveEndCutoff_range (parameters 0) (fun t => hgb _) x).1) hn
    (radialForm_smooth hA hAB _ _ c hp) (radialForm_skew _ _ _ c p)
    (fun b y hy => (radialForm_positive_bp240 hA hAB (cubicMarked_lt_degree hB hS) hc hp b hy).le)

 theorem tendsto_radial_cubic_exhaustion_area {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ℓ => compactSurfaceFormIntegral
      (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ))
      (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)) atTop
      (𝓝 (c*(3*((D:ℝ)-3*(p.1+p.2))-2*markedHeight S (planeVector p.1 p.2))*Real.pi)) := by
  obtain ⟨g,r,R,hr,hR,hR1,hg,hgc,hgb,h1,h0,hreg⟩ := exists_small_cubic_end_cutoff
  have ht := tendsto_radial_cubic_cutoff_mass_bp240 hA hS0 hAB hSB hB hS hp hg hgc hr hR hR1 hreg h1 h0 c
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨n,hn⟩ := ((tendsto_order.mp ht).1 b hb).exists
    filter_upwards [compact_eventually_subset_projectionDomain (parameters 0)
      (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)] with ℓ hℓ
    apply hn.trans_le
    exact surfaceCutoffMass_le_compactIntegral (positivePlaneTransitions (parameters 0))
      (projectionDomain_compact (parameters 0) _) (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n) hℓ
      (curveEndCutoff_smooth (parameters 0) (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n))
      (fun x => (curveEndCutoff_range (parameters 0) (fun t => hgb _) x).2)
      (radialForm_smooth hA hAB _ _ c hp) (radialForm_skew _ _ _ c p)
      (fun b y hy => (radialForm_positive_bp240 hA hAB (cubicMarked_lt_degree hB hS) hc hp b hy).le)
  · intro b hb
    exact Eventually.of_forall (fun ℓ => (radial_cubic_compact_area_le hA hS0 hAB hSB hB hS hp hc
      (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ))).trans_lt hb)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

theorem compactSurfaceFormIntegral_mono {C D : Set M} (hC : IsCompact C)
    (hD : IsCompact D) (hCD : C⊆D) (hor : PositivePlaneTransitions M)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0 ≤ chartTwoForm Ω c y (1,0) (0,1)) :
    compactSurfaceFormIntegral hC Ω ≤ compactSurfaceFormIntegral hD Ω := by
  let B := fun b : compactSurfaceBoxes hD => b.1
  let ρ := compactSurfacePartition hD
  have hρ := compactSurfacePartition_subordinate hD
  rw [compactSurfaceFormIntegral_eq_setIntegral hC hor hCD B ρ hρ hΩ ha hp,
    compactSurfaceFormIntegral_eq_setIntegral hD hor Subset.rfl B ρ hρ hΩ ha hp]
  apply setIntegral_mono_set
  · exact (smooth_integrable_partitionAreaMeasure B ρ hρ hΩ hp
      (contMDiff_const (c := (1:ℝ)))).integrableOn
  · exact Filter.Eventually.of_forall (fun _ => zero_le_one)
  · exact Filter.Eventually.of_forall (fun x hx => hCD hx)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

 attribute [local instance] OAI.PackingSufficiencySupport.CubicModel.radialCubicUniformAreaSigmaCompact
theorem tendstoUniformlyOn_radial_cubic_area {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {P : Set Radial.Plane} (hP : IsCompact P) (hPS : P⊆Radial.lowerTrapezoid A B)
    {c : ℝ} (hc : 0 < c) :
    TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral
      (projectionDomain_compact (parameters 0) (exhaustionRadius (parameters 0) ℓ))
      (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p))
      (fun p => c*(3*((D:ℝ)-3*(p.1+p.2))-2*markedHeight S (planeVector p.1 p.2))*Real.pi)
      atTop P := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto hP
  · intro ℓ
    exact radial_compact_area_continuousOn hA hAB _ _ c hP hPS
      (projectionDomain_compact (parameters 0) _)
  · intro p hp i j hij
    apply compactSurfaceFormIntegral_mono _ _ ?_ (positivePlaneTransitions (parameters 0))
      (radialForm_smooth hA hAB _ _ c (hPS hp)) (radialForm_skew _ _ _ c p)
      (fun b y hy => (radialForm_positive_bp240 hA hAB (cubicMarked_lt_degree hB hS) hc (hPS hp) b hy).le)
    intro x hx
    change ‖x.val.1‖≤exhaustionRadius (parameters 0) j
    have hh : exhaustionRadius (parameters 0) i≤exhaustionRadius (parameters 0) j := by
      dsimp only [exhaustionRadius]
      gcongr
    exact hx.trans hh
  · have hct : Continuous (fun p : Radial.Plane =>
        c*(3*((D:ℝ)-3*(p.1+p.2))-2*markedHeight S (planeVector p.1 p.2))*Real.pi) := by
      simp only [markedHeight,planeVector,Matrix.cons_val_zero,Matrix.cons_val_one]
      fun_prop
    exact hct.continuousOn
  · exact fun p hp => tendsto_radial_cubic_exhaustion_area hA hS0 hAB hSB hB hS (hPS hp) hc

end PackingSufficiencySupport.CubicModel

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
-- module Solutions.OAIQ240_BP.BallPacking_Models_RationalSlack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

theorem physicalParameter_smooth (L : ℝ) : ContDiff ℝ ∞ (physicalParameter L) := by
  unfold physicalParameter
  fun_prop

 attribute [local instance] OAI.PackingSufficiencySupport.CubicModel.instSigmaCompactSpaceElemAffineHAddNatOfNatBaseCurve
theorem physicalArea_uniform_bp240_oai {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {P : Set (Moments 2)} (hP : IsCompact P) (L : ℝ)
    (hPS : MapsTo (physicalParameter L) P (Radial.lowerTrapezoid A B))
    {c : ℝ} (hc : 0 < c) :
    TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (cubicExhaustion_compact ℓ)
      (manifoldExteriorOneForm (physicalPrimitive (A := A) (B := B) D S c L p)))
      (physicalArea D S c L) atTop P := by
  have hlim := (tendstoUniformlyOn_radial_cubic_area hA hS0 hAB hSB hB hS
    (hP.image (physicalParameter_smooth L).continuous) (image_subset_iff.mpr hPS) hc).comp
    (physicalParameter L)
  have hh := hlim.mono (show P⊆physicalParameter L ⁻¹' (physicalParameter L '' P) from
    fun p hp => mem_image_of_mem _ hp)
  unfold physicalArea
  simpa only [Function.comp_def,physicalPrimitive,physicalParameter,sub_add_eq_sub_sub,
    markedHeight,planeVector,Matrix.cons_val_zero,Matrix.cons_val_one,radialForm] using! hh

end PackingSufficiencySupport.CubicModel

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.CubicModel.physicalArea_uniform_bp240_oai := @OAI.PackingSufficiencySupport.CubicModel.physicalArea_uniform_bp240_oai
