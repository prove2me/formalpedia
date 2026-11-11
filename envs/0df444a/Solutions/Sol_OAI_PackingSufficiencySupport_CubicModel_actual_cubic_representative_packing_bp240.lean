-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.CubicModel.actual_cubic_representative_packing_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:26.539563+00:00
-- url     : https://prove2.me/submissions/781b1786-2711-4c28-80a1-87677adf2ca6

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_physicalArea_uniform_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_radialForm_positive_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_exists_actual_compact_normalized_dual_fixed_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_MomentPolytope_Annular_exhausted_surface_packing_bp240

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
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_add _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm_add _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_inside _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_outside _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_vertical _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
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

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem chartTwoForm_skew {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) (c : M) (y u v : Plane) :
    chartTwoForm Ω c y u v = -chartTwoForm Ω c y v u := by
  exact hΩ _ _ _


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
section

variable {m : ℕ}

theorem projectionDomain_closed (a : Fin m → ℂ) (R : ℝ) :
    IsClosed (projectionDomain a R) :=
  isClosed_le ((continuous_fst.comp continuous_subtype_val).norm) continuous_const

theorem projectionDomain_nested (a : Fin m → ℂ) {R S : ℝ} (hRS : R<S) :
    projectionDomain a R⊆interior (projectionDomain a S) := by
  have ho : IsOpen {x : locus a | ‖x.val.1‖<S} :=
    isOpen_lt ((continuous_fst.comp continuous_subtype_val).norm) continuous_const
  have hs : {x : locus a | ‖x.val.1‖<S}⊆projectionDomain a S := fun x (hx : ‖x.val.1‖<S) => hx.le
  intro x hx
  exact interior_maximal hs ho (lt_of_le_of_lt hx hRS)

theorem projectionDomain_cover (a : Fin m → ℂ) (R : ℝ) :
    (⋃ ℓ : ℕ,projectionDomain a (R+ℓ))=univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨ℓ,hℓ⟩ := exists_nat_gt (‖x.val.1‖-R)
  exact mem_iUnion.mpr ⟨ℓ,by change ‖x.val.1‖≤R+ℓ; linarith⟩

end

variable {m : ℕ} {a : Fin m → ℂ}

private theorem square_not_locally_constant (z c : ℂ) :
    ¬ ∀ᶠ w in 𝓝 z,w^2=c := by
  intro h
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => w^2) univ := fun w _ => analyticAt_id.pow 2
  have he : (fun w : ℂ => w^2)=(fun _ : ℂ => c) :=
    hf.eq_of_eventuallyEq analyticOnNhd_const h
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  norm_num at h0 h1
  exact zero_ne_one (h0.trans h1.symm)

namespace NormalChart
variable (e : NormalChart a) (x : locus a)

theorem projectionChart_nonconstant {z : ℂ} (hz : z∈(e.sliceChart x).target) :
    ¬ ∀ᶠ w in 𝓝 z,(e.inclusionChart x w).1=(e.inclusionChart x z).1 := by
  intro h
  have hc : ∀ᶠ w in 𝓝 z,curveCoordinate e.coordinate (e.inclusionChart x w)=w := by
    filter_upwards [(e.sliceChart x).open_target.mem_nhds hz] with w hw
    exact e.inclusionChart_coordinate x hw
  cases he : e.coordinate with
  | none =>
    have hh : ∀ᶠ w in 𝓝 z,w^2=((e.inclusionChart x z).1)^2 := by
      filter_upwards [h,hc] with w hw hc
      rw [he] at hc
      change (e.inclusionChart x w).1=w at hc
      rw [← hc,hw]
    exact square_not_locally_constant z _ hh
  | some j =>
    have hh : ∀ᶠ w in 𝓝 z,w^2=((e.inclusionChart x z).1)^2-a j := by
      filter_upwards [h,hc] with w hw hc
      rw [he] at hc
      change (e.inclusionChart x w).2 j=w at hc
      rw [← hc]
      have hmem := mem_locus.mp ((e.sliceChart x).symm w).property j
      change (e.inclusionChart x w).2 j ^ 2=(e.inclusionChart x w).1^2-a j at hmem
      rw [hmem,hw]
    exact square_not_locally_constant z _ hh

theorem projectionChart_open_at {z : ℂ} (hz : z∈(e.sliceChart x).target) :
    𝓝 ((e.inclusionChart x z).1) ≤ map (fun w => (e.inclusionChart x w).1) (𝓝 z) := by
  have hd := ((e.inclusionChart_smooth x).fst.differentiableOn (by simp)).analyticOnNhd
    (e.sliceChart x).open_target
  exact (hd z hz).eventually_constant_or_nhds_le_map_nhds.resolve_left
    (e.projectionChart_nonconstant x hz)
end NormalChart

variable [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem curveProjection_open : IsOpenMap (curveProjection a) := by
  rw [isOpenMap_iff_nhds_le]
  intro x
  let e := (normalChartAt a x).sliceChart x
  have hx : x∈e.source := mem_normalChartAt a x
  have h := (normalChartAt a x).projectionChart_open_at x (e.map_source hx)
  change 𝓝 (curveProjection a (e.symm (e x))) ≤ map (curveProjection a ∘ e.symm) (𝓝 (e x)) at h
  rw [e.left_inv hx,← map_map,e.symm_map_nhds_eq hx] at h
  exact h

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
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldMapDifferential
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_inside _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_outside _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_vertical _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
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

theorem vector_chartTwoForm (Ω : E → E →L[ℝ] E →L[ℝ] ℝ) (c y : E) :
    chartTwoForm Ω c y=Ω y := by
  ext v w
  simp only [chartTwoForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,id_eq,
    ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.id_apply]

theorem vector_oneForm_smooth {α : E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α) :
    SmoothOneFormFamily (fun _ : ℝ => α) := by
  intro c
  simpa only [vector_chartOneForm,Function.comp_def] using
    (hα.comp contDiff_snd).contDiffOn

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
  [MeasurableSpace M] [BorelSpace M]

theorem chartInverseExtension_measurable (c : M) : Measurable (chartInverseExtension c) := by
  classical
  exact (continuousOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) c).measurable_piecewise
    continuousOn_const (isOpen_extChartAt_target c).measurableSet

omit [MeasurableSpace M] [BorelSpace M] in
theorem chartInverseExtension_eq {c : M} {y : Plane}
    (hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target) :
    chartInverseExtension c y=(extChartAt 𝓘(ℝ,Plane) c).symm y := ite_eq_left hy

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [MeasurableSpace M] [BorelSpace M]

variable {I : Type*} [Fintype I] {K : Set M}

variable [IsManifold 𝓘(ℝ,Plane) ∞ M]

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
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]

 variable [MeasurableSpace M] [BorelSpace M]

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
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open Hamiltonian

variable {m : ℕ} {a : Fin m → ℂ} [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem exists_projection_chart (x : locus a) (hx : ∀ j,x.val.2 j≠0) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) (locus a) RealModel ∞,
      x∈e.source ∧ ∀ y,e y=Complex.equivRealProdCLM y.val.1 := by
  obtain ⟨e,he,_hreg,heq,_hf,hg⟩ := exists_normal_straightening a none hx
  let E : NormalChart a := ⟨none,e,heq,hg⟩
  refine ⟨E.realSliceDiffeomorph x,?_,fun y => rfl⟩
  change x∈(E.realSliceChart x).source
  rw [E.realSliceChart_source]
  exact he

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport
open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem diskBoundaryMap_smooth (R : ℝ) (p : DiskPlane) : ContDiff ℝ ∞ (diskBoundaryMap R p) :=
  ((contDiff_const.mul contDiff_snd).sub (contDiff_const.mul contDiff_fst)).prodMk
    (contDiff_const.sub ((contDiff_fst.pow 2).add (contDiff_snd.pow 2)))

theorem diskBoundaryMap_hasFDerivAt (R : ℝ) (p q : DiskPlane) :
    HasFDerivAt (diskBoundaryMap R p) (diskBoundaryDerivative p q) q := by
  have h1 := ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).const_mul p.1).sub ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).const_mul p.2)
  have h2 := (((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).pow 2).add ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).pow 2)).const_sub (R^2)
  apply (h1.prodMk h2).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext <;> simp [diskBoundaryDerivative]
  ring

theorem diskBoundaryDerivative_bijective {p q : DiskPlane} (h : p.1*q.1+p.2*q.2≠0) :
    Bijective (diskBoundaryDerivative p q) := by
  have h' : q.1*p.1+q.2*p.2≠0 := by simpa only [mul_comm] using h
  constructor
  · intro v w he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    change p.1*v.2-p.2*v.1=p.1*w.2-p.2*w.1 at he1
    change (-2*q.1)*v.1+(-2*q.2)*v.2=(-2*q.1)*w.1+(-2*q.2)*w.2 at he2
    apply Prod.ext
    · apply (mul_left_inj' h).mp
      linear_combination -q.2*he1-p.1/2*he2
    · apply (mul_left_inj' h).mp
      linear_combination q.1*he1-p.2/2*he2
  · intro y
    refine ⟨((-2*q.2*y.1-p.1*y.2)/(2*(p.1*q.1+p.2*q.2)),
      (2*q.1*y.1-p.2*y.2)/(2*(p.1*q.1+p.2*q.2))),?_⟩
    apply Prod.ext
    · change p.1*((2*q.1*y.1-p.2*y.2)/(2*(p.1*q.1+p.2*q.2)))-
        p.2*((-2*q.2*y.1-p.1*y.2)/(2*(p.1*q.1+p.2*q.2)))=y.1
      field_simp [h,h']
      ring
    · change (-2*q.1)*((-2*q.2*y.1-p.1*y.2)/(2*(p.1*q.1+p.2*q.2)))+
        (-2*q.2)*((2*q.1*y.1-p.2*y.2)/(2*(p.1*q.1+p.2*q.2)))=y.2
      field_simp [h,h']
      ring

theorem exists_diskBoundaryDiffeomorph (R : ℝ) {p : DiskPlane}
    (hp : 0<p.1^2+p.2^2) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ,DiskPlane) 𝓘(ℝ,DiskPlane) DiskPlane DiskPlane ∞,
      p∈e.source ∧ (e : DiskPlane→DiskPlane)=diskBoundaryMap R p := by
  have h0 : p.1*p.1+p.2*p.2≠0 := by nlinarith
  let D := diskBoundaryDerivative p p
  let L := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr (diskBoundaryDerivative_bijective h0).1)
    (LinearMap.range_eq_top.mpr (diskBoundaryDerivative_bijective h0).2)
  have hd : HasFDerivAt (diskBoundaryMap R p) (L : DiskPlane→L[ℝ]DiskPlane) p :=
    diskBoundaryMap_hasFDerivAt R p p
  let e0 := (diskBoundaryMap_smooth R p).contDiffAt.toOpenPartialHomeomorph
    (diskBoundaryMap R p) hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let U : Set DiskPlane := {q | p.1*q.1+p.2*q.2≠0}
  have hU : IsOpen U := isOpen_ne_fun (by fun_prop) continuous_const
  let e := e0.restrOpen U hU
  have he : (e : DiskPlane→DiskPlane)=diskBoundaryMap R p := rfl
  have hi : ContDiffOn ℝ ∞ e.symm e.target := by
    intro y hy
    have hq : p.1*(e.symm y).1+p.2*(e.symm y).2≠0 := (e.map_target hy).2
    let B := diskBoundaryDerivative p (e.symm y)
    let K := ContinuousLinearEquiv.ofBijective B
      (LinearMap.ker_eq_bot.mpr (diskBoundaryDerivative_bijective hq).1)
      (LinearMap.range_eq_top.mpr (diskBoundaryDerivative_bijective hq).2)
    exact (e.contDiffAt_symm (𝕜 := ℝ) (f₀' := K) hy
      (diskBoundaryMap_hasFDerivAt R p (e.symm y))
      (diskBoundaryMap_smooth R p).contDiffAt).contDiffWithinAt
  let E : PartialDiffeomorph 𝓘(ℝ,DiskPlane) 𝓘(ℝ,DiskPlane) DiskPlane DiskPlane ∞ := {
    __ := e
    contMDiffOn_toFun := (diskBoundaryMap_smooth R p).contMDiff.contMDiffOn
    contMDiffOn_invFun := hi.contMDiffOn }
  exact ⟨E,
    ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),h0⟩,he⟩

end PackingSufficiencySupport

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricSmoothExhaustion
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
section
variable {m : ℕ} {a : Fin m → ℂ} [Fact (Injective a)] [Fact (∀ j,a j≠0)]

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem projectionDomain_frontier_norm {R : ℝ} {x : locus a}
    (hx : x∈frontier (projectionDomain a R)) : ‖x.val.1‖=R := by
  have hle : ‖x.val.1‖≤R := (projectionDomain_closed a R).frontier_subset hx
  apply le_antisymm hle
  by_contra! hlt
  apply hx.2
  have ho : IsOpen {y : locus a | ‖y.val.1‖<R} :=
    isOpen_lt ((continuous_fst.comp continuous_subtype_val).norm) continuous_const
  exact interior_maximal (fun {y : locus a} (hy : ‖y.val.1‖<R) => hy.le) ho hlt

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem projectionDomain_frontier_regular {R : ℝ} (hR : ∀ j,‖a j‖<R^2)
    {x : locus a} (hx : x∈frontier (projectionDomain a R)) : ∀ j,x.val.2 j≠0 := by
  intro j hj
  have he := mem_locus.mp x.property j
  rw [hj,zero_pow (by decide)] at he
  have ht : x.val.1^2=a j := sub_eq_zero.mp he.symm
  have hn := congrArg norm ht
  rw [norm_pow,projectionDomain_frontier_norm hx] at hn
  exact (ne_of_lt (hR j)) hn.symm

theorem projectionDomain_smoothBoundary {R : ℝ} (hRp : 0<R) (hR : ∀ j,‖a j‖<R^2) :
    Hamiltonian.HasSmoothSurfaceBoundary (projectionDomain a R) := by
  intro x hx
  obtain ⟨e,he,heq⟩ := exists_projection_chart x (projectionDomain_frontier_regular hR hx)
  have h0 : 0<(e x).1^2+(e x).2^2 := by
    rw [heq x]
    change 0<x.val.1.re^2+x.val.1.im^2
    have hh := projectionDomain_frontier_norm hx
    have hs : x.val.1.re^2+x.val.1.im^2=R^2 := by
      rw [← Complex.sq_norm_sub_sq_im]
      rw [hh]
      ring
    rw [hs]
    exact sq_pos_of_pos hRp
  obtain ⟨f,hf,hfq⟩ := exists_diskBoundaryDiffeomorph R h0
  refine ⟨e.trans f,⟨he,hf⟩,?_⟩
  intro y _hy
  change ‖y.val.1‖≤R ↔ 0≤(f (e y)).2
  rw [hfq,heq y]
  change ‖y.val.1‖≤R ↔ 0≤R^2-(y.val.1.re^2+y.val.1.im^2)
  have hsq : y.val.1.re^2+y.val.1.im^2=‖y.val.1‖^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    ring
  rw [hsq,sub_nonneg]
  exact sq_le_sq₀ (norm_nonneg _) hRp.le |>.symm

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem exhaustionRadius_pos (a : Fin m → ℂ) (ℓ : ℕ) : 0<exhaustionRadius a ℓ := by
  unfold exhaustionRadius
  positivity

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem exhaustionRadius_branch (a : Fin m → ℂ) (ℓ : ℕ) (j : Fin m) :
    ‖a j‖<(exhaustionRadius a ℓ)^2 := by
  have hs : ‖a j‖≤∑ k,‖a k‖ := Finset.single_le_sum (fun k _ => norm_nonneg (a k)) (Finset.mem_univ j)
  have he : 2+‖a j‖≤exhaustionRadius a ℓ := by
    unfold exhaustionRadius
    linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  nlinarith [sq_nonneg (exhaustionRadius a ℓ-1),norm_nonneg (a j)]

end

variable {m : ℕ} {a : Fin m → ℂ}

theorem signFlip_continuous (j : Fin m) : Continuous (signFlip (a := a) j) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk (continuous_fst.comp continuous_subtype_val)
  apply continuous_pi
  intro i
  by_cases hi : i=j
  · simp only [ite_eq_left hi]
    fun_prop
  · simp only [ite_eq_right hi]
    fun_prop

theorem signFlip_fixed_branch (j : Fin m) (b : ℂ) (hb : b^2=a j)
    {x : locus a} (hx : x.val.1=b) : signFlip j x=x := by
  have hj := mem_locus.mp x.property j
  rw [hx,hb,sub_self] at hj
  have hz : x.val.2 j=0 := sq_eq_zero_iff.mp hj
  apply Subtype.ext
  refine Prod.ext rfl ?_
  funext i
  by_cases hi : i=j
  · subst i
    simp [signFlip,hz]
  · simp [signFlip,hi]

theorem fiberMix_insert (x y : locus a) (hxy : x.val.1=y.val.1)
    (F : Finset (Fin m)) (j : Fin m) (hj : j∉F) :
    fiberMix x y hxy (insert j F)=fiberMix x y hxy F ∨
    fiberMix x y hxy (insert j F)=signFlip j (fiberMix x y hxy F) := by
  have hs : y.val.2 j^2=x.val.2 j^2 := by
    rw [mem_locus.mp y.property j,mem_locus.mp x.property j,hxy]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with he | he
  · left
    apply Subtype.ext
    refine Prod.ext rfl ?_
    funext i
    by_cases hi : i=j
    · subst i; simp [fiberMix,hj,he]
    · simp [fiberMix,hi]
  · right
    apply Subtype.ext
    refine Prod.ext rfl ?_
    funext i
    by_cases hi : i=j
    · subst i; simp [fiberMix,signFlip,hj,he]
    · simp [fiberMix,signFlip,hi]

theorem signStable_contains_fiber {S : Set (locus a)}
    (hS : ∀ j,MapsTo (signFlip j) S S) {x y : locus a}
    (hx : x∈S) (hxy : x.val.1=y.val.1) : y∈S := by
  have h : ∀ F : Finset (Fin m),fiberMix x y hxy F∈S := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa using hx
    | @insert j F hj ih =>
      rcases fiberMix_insert x y hxy F j hj with he | he
      · rwa [he]
      · rw [he]; exact hS j ih
  simpa using h Finset.univ

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport
open scoped Topology
open Set Function

theorem component_image_eq_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace X] [PreconnectedSpace Y]
    (f : X→Y) (hf : IsProperMap f) (ho : IsOpenMap f) (x : X) :
    f '' connectedComponent x=univ := by
  apply IsClopen.eq_univ
  · exact ⟨hf.isClosedMap _ isClosed_connectedComponent,ho _ isOpen_connectedComponent⟩
  · exact ⟨f x,⟨x,mem_connectedComponent,rfl⟩⟩

theorem component_preserved_of_fixed_fiber {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [LocallyConnectedSpace X] [PreconnectedSpace Y]
    (f : X→Y) (hf : IsProperMap f) (ho : IsOpenMap f)
    (τ : X→X) (hτ : Continuous τ) (b : Y) (hfix : ∀ p,f p=b→τ p=p) (x : X) :
    MapsTo τ (connectedComponent x) (connectedComponent x) := by
  have hb : b∈f '' connectedComponent x := by rw [component_image_eq_univ f hf ho x]; trivial
  obtain ⟨p,hp,hpb⟩ := hb
  have hc : connectedComponent p=connectedComponent x := (connectedComponent_eq hp).symm
  have hi := hτ.image_connectedComponent_subset p
  rw [hfix p hpb,hc] at hi
  exact fun y hy => hi ⟨y,hy,rfl⟩

end PackingSufficiencySupport

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter MeasureTheory
open Hamiltonian
section

variable {m : ℕ} {a : Fin m → ℂ}

theorem curveProjection_surjective (a : Fin m → ℂ) : Surjective (curveProjection a) := by
  intro t
  refine ⟨⟨(t,fun j => Complex.sqrt (t^2-a j)),?_⟩,rfl⟩
  exact mem_locus.mpr (fun j => sqrt_sq_complex _)

theorem signFlipOver_continuous (V : Set ℂ) (j : Fin m) :
    Continuous (signFlipOver (a := a) V j) :=
  ((signFlip_continuous j).comp continuous_subtype_val).subtype_mk _

variable [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem projection_preimage_preconnected {V : Set ℂ} (hVo : IsOpen V)
    (hVc : IsPreconnected V) (hbranch : ∀ j,Complex.sqrt (a j)∈V) :
    IsPreconnected (curveProjection a ⁻¹' V) := by
  let : LocallyConnectedSpace (locus a) := ChartedSpace.locallyConnectedSpace ℂ (locus a)
  let : LocallyConnectedSpace (curveProjection a ⁻¹' V) :=
    (hVo.preimage (curveProjection_continuous a)).locallyConnectedSpace
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hVc
  rw [isPreconnected_iff_preconnectedSpace]
  apply preconnectedSpace_iff_connectedComponent.mpr
  intro x
  apply eq_univ_of_forall
  intro y
  let f := V.restrictPreimage (curveProjection a)
  have hf : IsProperMap f := (curveProjection_proper a).restrictPreimage V
  have ho : IsOpenMap f := curveProjection_open.restrictPreimage V
  have hflip : ∀ j,MapsTo (signFlipOver V j) (connectedComponent x) (connectedComponent x) := by
    intro j
    apply PackingSufficiencySupport.component_preserved_of_fixed_fiber f hf ho
      (signFlipOver V j) (signFlipOver_continuous V j) ⟨Complex.sqrt (a j),hbranch j⟩ _ x
    intro p hp
    apply Subtype.ext
    exact signFlip_fixed_branch j _ (sqrt_sq_complex _) (congrArg Subtype.val hp)
  have him : f y∈f '' connectedComponent x := by
    rw [PackingSufficiencySupport.component_image_eq_univ f hf ho x]
    trivial
  obtain ⟨z,hz,hzy⟩ := him
  let S : Set (locus a) := Subtype.val '' connectedComponent x
  have hS : ∀ j,MapsTo (signFlip j) S S := by
    rintro j p ⟨q,hq,rfl⟩
    exact ⟨signFlipOver V j q,hflip j hq,rfl⟩
  have hy : y.val∈S := signStable_contains_fiber hS ⟨z,hz,rfl⟩ (congrArg Subtype.val hzy)
  obtain ⟨q,hq,hqy⟩ := hy
  exact (Subtype.ext hqy) ▸ hq

theorem projection_preimage_connected {V : Set ℂ} (hVo : IsOpen V)
    (hVc : IsConnected V) (hbranch : ∀ j,Complex.sqrt (a j)∈V) :
    IsConnected (curveProjection a ⁻¹' V) := by
  refine ⟨?_,projection_preimage_preconnected hVo hVc.isPreconnected hbranch⟩
  obtain ⟨t,ht⟩ := hVc.nonempty
  obtain ⟨x,rfl⟩ := curveProjection_surjective a t
  exact ⟨x,ht⟩

theorem projectionDomain_interior {R : ℝ} (hR : 0<R) :
    interior (projectionDomain a R)=curveProjection a ⁻¹' Metric.ball 0 R := by
  have he : projectionDomain a R=curveProjection a ⁻¹' Metric.closedBall 0 R := by
    ext x
    simp only [projectionDomain,mem_ofPred_eq,mem_preimage,Metric.mem_closedBall,
      dist_zero_right,curveProjection]
  rw [he,← curveProjection_open.preimage_interior_eq_interior_preimage
    (curveProjection_continuous a),interior_closedBall _ hR.ne']

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
 theorem sqrt_mem_disk {R : ℝ} (hR : 0<R) {z : ℂ} (hz : ‖z‖<R^2) :
    Complex.sqrt z∈Metric.ball 0 R := by
  rw [Metric.mem_ball,dist_zero_right]
  have he := congrArg norm (sqrt_sq_complex z)
  rw [norm_pow] at he
  exact (sq_lt_sq₀ (norm_nonneg _) hR.le).mp (by rwa [he])

theorem projectionDomain_interior_connected {R : ℝ} (hR : 0<R)
    (hbranch : ∀ j,‖a j‖<R^2) : IsConnected (interior (projectionDomain a R)) := by
  rw [projectionDomain_interior hR]
  exact projection_preimage_connected Metric.isOpen_ball ⟨Metric.nonempty_ball.mpr hR,(convex_ball (0 : ℂ) R).isPreconnected⟩
    (fun j => sqrt_mem_disk hR (hbranch j))

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
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_BaseHorizontalForms
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_manifold _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_manifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory
open scoped ContDiff Manifold Topology

theorem circleBand_compact {a b : ℝ} :
    IsCompact (circleTurn '' Icc a b) := isCompact_Icc.image circleTurn_smooth.continuous

theorem intervalClock_monotone {a b : ℝ} (hab : a < b) : Monotone (intervalClock a b) := by
  intro x y hxy
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_nonneg.mpr hab.le))

theorem intervalClock_deriv_nonneg {a b : ℝ} (hab : a < b) (s : ℝ) :
    0 ≤ deriv (intervalClock a b) s := (intervalClock_monotone hab).deriv_nonneg

theorem intervalClock_zero {a b s : ℝ} (hab : a < b) (hs : s ≤ a) : intervalClock a b s=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sub_nonneg.mpr hab.le))

theorem intervalClock_one {a b s : ℝ} (hab : a < b) (hs : b ≤ s) : intervalClock a b s=1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).2 (by linarith))

theorem intervalClock_deriv_smooth (a b : ℝ) : ContDiff ℝ ∞ (deriv (intervalClock a b)) :=
  (contDiff_infty_iff_deriv.mp (intervalClock_smooth a b)).2

theorem intervalClock_deriv_zero_left {a b s : ℝ} (hab : a<b) (hs : s<a) :
    deriv (intervalClock a b) s=0 := by
  have he : intervalClock a b =ᶠ[𝓝 s] fun _ => (0:ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds hs] with t ht
    exact intervalClock_zero hab ht.le
  rw [he.deriv_eq,deriv_const]

theorem intervalClock_deriv_zero_right {a b s : ℝ} (hab : a<b) (hs : b < s) :
    deriv (intervalClock a b) s=0 := by
  have he : intervalClock a b =ᶠ[𝓝 s] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact intervalClock_one hab ht.le
  rw [he.deriv_eq,deriv_const]

theorem circleClockDensity_support {b : ℝ} (hb : 0<b) :
    support (circleClockDensity b) ⊆ circleTurn '' Icc (-b) b := by
  intro z hz
  refine ⟨shortCircleArgument z,?_,circleTurn_shortCircleArgument z⟩
  have hab : -b<b := by linarith
  constructor
  · by_contra hn
    exact hz (intervalClock_deriv_zero_left hab (lt_of_not_ge hn))
  · by_contra hn
    exact hz (intervalClock_deriv_zero_right hab (lt_of_not_ge hn))

theorem circleClockDensity_smooth {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ (circleClockDensity b) := by
  intro z
  by_cases hz : z∈circleTurn '' Icc (-b) b
  · obtain ⟨s,hs,rfl⟩ := hz
    have hin : s∈Ioo (-(1/2):ℝ) (1/2) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
    exact (intervalClock_deriv_smooth (-b) b).contMDiff.contMDiffAt.comp _
      (shortCircleArgument_smooth_at (circleTurn_short_slit hin))
  · apply (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [circleBand_compact.isClosed.isOpen_compl.mem_nhds hz] with w hw
    by_contra hs
    exact hw (circleClockDensity_support hb hs)

theorem circleClockDensity_nonneg {b : ℝ} (hb : 0<b) (z : Circle) :
    0 ≤ circleClockDensity b z :=
  intervalClock_deriv_nonneg (by linarith) _

theorem circleClockDensity_turn {b s : ℝ} (hs : s∈Ioo (-(1/2):ℝ) (1/2)) :
    circleClockDensity b (circleTurn s)=deriv (intervalClock (-b) b) s := by
  unfold circleClockDensity
  rw [shortCircleArgument_turn hs]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_CircleHandleBump
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





theorem circleTurn_eq_iff (s t : ℝ) :
    circleTurn s=circleTurn t ↔ ∃ m : ℤ, s=t+m := by
  rw [circleTurn,circleTurn,Circle.exp_eq_exp]
  constructor
  · rintro ⟨m,hm⟩
    refine ⟨m,?_⟩
    apply mul_left_cancel₀ (show 2*Real.pi≠0 by positivity)
    calc
      2*Real.pi*s=2*Real.pi*t+(m:ℝ)*(2*Real.pi) := hm
      _ = 2*Real.pi*(t+(m:ℝ)) := by ring
  · rintro ⟨m,rfl⟩
    exact ⟨m,by ring⟩


end

open scoped ContDiff Topology
open Set Function MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_CylinderAnnularNormalization
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply
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

theorem circleTurn_period_one : Periodic circleTurn 1 := by
  intro t
  exact (circleTurn_eq_iff (t+1) t).2 ⟨1,by simp⟩


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem shortCircleArgument_bounds (z : Circle) :
    -(1/2:ℝ) < shortCircleArgument z ∧ shortCircleArgument z≤1/2 := by
  have hp : 0<2*Real.pi := by positivity
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [Complex.neg_pi_lt_arg (z : ℂ)]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [Complex.arg_le_pi (z : ℂ)]

theorem positiveCircleCoordinate_target : positiveCircleCoordinate.target=({1}ᶜ : Set Circle) := by
  ext z
  constructor
  · rintro ⟨s,hs,rfl⟩ hz
    have he : circleTurn s=circleTurn 0 := by simpa only [mem_singleton_iff,circleTurn,mul_zero,Circle.exp_zero] using hz
    obtain ⟨m,hm⟩ := (circleTurn_eq_iff s 0).mp he
    have hlo : (0:ℤ) < m := by exact_mod_cast (show (0:ℝ) < m by linarith [hs.1])
    have hhi : m < (1:ℤ) := by exact_mod_cast (show (m:ℝ)<1 by linarith [hs.2])
    omega
  · intro hz
    have hb := shortCircleArgument_bounds z
    have hne : shortCircleArgument z≠0 := by
      intro he
      apply hz
      have hc := circleTurn_shortCircleArgument z
      rw [he] at hc
      simpa only [mem_singleton_iff,circleTurn,mul_zero,Circle.exp_zero] using hc.symm
    by_cases hpos : 0 < shortCircleArgument z
    · exact ⟨shortCircleArgument z,⟨hpos,by linarith [hb.2]⟩,circleTurn_shortCircleArgument z⟩
    · refine ⟨shortCircleArgument z+1,⟨by linarith [hb.1],by
          have hn : shortCircleArgument z<0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
          linarith⟩,?_⟩
      rw [circleTurn_period_one,circleTurn_shortCircleArgument]


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

theorem positiveCircleClock_smooth {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ (positiveCircleClock b) :=
  (circleClockDensity_smooth hb hsmall).comp (contMDiff_id.div contMDiff_const)

theorem positiveCircleClock_nonneg {b : ℝ} (hb : 0<b) (z : Circle) :
    0≤positiveCircleClock b z := circleClockDensity_nonneg hb _

theorem positiveCircleClock_turn {b s : ℝ} (hs : s∈Ioo (0:ℝ) 1) :
    positiveCircleClock b (circleTurn s)=deriv (intervalClock (-b) b) (s-1/2) := by
  unfold positiveCircleClock
  rw [←circleTurn_sub,circleClockDensity_turn (show s-1/2∈Ioo (-(1/2):ℝ) (1/2) by
    constructor <;> linarith [hs.1,hs.2])]

theorem positiveCircleClock_tsupport {b : ℝ} (hb : 0<b) :
    tsupport (positiveCircleClock b)⊆circleTurn '' Icc (1/2-b) (1/2+b) := by
  apply closure_minimal _ (isCompact_Icc.image circleTurn_smooth.continuous).isClosed
  intro z hz
  obtain ⟨s,hs,he⟩ := circleClockDensity_support hb hz
  refine ⟨s+1/2,⟨by linarith [hs.1],by linarith [hs.2]⟩,?_⟩
  rw [circleTurn_add,he,div_mul_cancel]

theorem positiveCircleClock_cut {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    tsupport (positiveCircleClock b)⊆({1}ᶜ : Set Circle) := by
  intro z hz
  rw [←positiveCircleCoordinate_target]
  obtain ⟨s,hs,rfl⟩ := positiveCircleClock_tsupport hb hz
  exact ⟨s,⟨by linarith [hs.1],by linarith [hs.2]⟩,rfl⟩

theorem positiveCircleClock_integral {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    (∫ s in (0:ℝ)..1,positiveCircleClock b (circleTurn s))=1 := by
  let T : ℝ → ℝ := fun s => intervalClock (-b) b (s-1/2)
  have hd (s : ℝ) : HasDerivAt T (deriv (intervalClock (-b) b) (s-1/2)) s := by
    have hh := (((intervalClock_smooth (-b) b).differentiable (by simp) (s-1/2)).hasDerivAt.comp s
      ((hasDerivAt_id s).sub_const (1/2)))
    convert hh using 1 <;> first | rfl | ring
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ)≤1)
    (fun s hs => positiveCircleClock_turn hs)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (((intervalClock_deriv_smooth (-b) b).continuous.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _)]
  dsimp [T]
  rw [intervalClock_one (by linarith : -b<b) (by linarith),
    intervalClock_zero (by linarith : -b<b) (by linarith)]
  norm_num


end


open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularChartNormalization
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

theorem exists_fixed_annularHandleData (m : ℕ) :
    ∃ H : AnnularHandleData RealModel (Surface m),
      H.width=transverseCylinderWidth m/2 ∧
      H.chart=restrictedTransverseCylinder m (transverseCylinderWidth m/2) ∧
      H.clock=positiveCircleClock (1/4) := by
  let f := positiveCircleClock (1/4)
  have hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f := positiveCircleClock_smooth (by norm_num) (by norm_num)
  have hfi : (∫ t in (0:ℝ)..1,f (circleTurn t))=1 := positiveCircleClock_integral (by norm_num) (by norm_num)
  obtain ⟨a,e,β,hae,hee,ha,he,hec,hβ,hcp,hcl,hpb⟩ :=
    exists_actual_compact_normalized_dual_fixed_bp240 m hf hfi
  exact ⟨⟨a,ha,e,he,hec,f,hf,positiveCircleClock_nonneg (by norm_num),
    positiveCircleClock_cut (by norm_num) (by norm_num),hfi,β,hβ,hcp,hcl,hpb⟩,hae,hee,rfl⟩

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_EqualNormalModelConvergence
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian

variable (m : ℕ)

theorem transverse_transition_differentiable (c : Surface m) {z : ℂ}
    (hz : z∈transverseAnnulusDomain m) :
    DifferentiableAt ℂ (((normalChartAt (parameters m) c).sliceChart c) ∘
      (transverseAnnulusChart m).symm) z := by
  let n := normalChartAt (parameters m) c
  have hs := (curveCoordinate n.coordinate).contDiff.contDiffAt.comp z
    (transverseAnnulusPoint_contDiffAt m hz)
  apply (hs.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).congr_of_eventuallyEq
  filter_upwards [(transverseAnnulusDomain_isOpen m).mem_nhds hz] with t ht
  change curveCoordinate n.coordinate ((transverseAnnulusInverse m t).val)=_
  rw [transverseAnnulusInverse_val m ht.1]
  rfl

theorem transverse_transition_inverse_differentiable (c : Surface m) {z : ℂ}
    (hz : z∈((normalChartAt (parameters m) c).sliceChart c).target) :
    DifferentiableAt ℂ ((transverseAnnulusChart m) ∘
      ((normalChartAt (parameters m) c).sliceChart c).symm) z := by
  have hs := ((normalChartAt (parameters m) c).sliceChart_inverse_smooth c).contDiffAt
    (((normalChartAt (parameters m) c).sliceChart c).open_target.mem_nhds hz)
  exact ((transverseCoordinate m).contDiff.contDiffAt.comp z hs).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

theorem transverseDiffeomorph_positive : PositivePartialChart (transverseDiffeomorph m) := by
  intro c y hy hc
  let n := normalChartAt (parameters m) c
  let e := (transverseAnnulusChart m).symm.trans (n.sliceChart c)
  have hchart : chartAt Plane c=realChart (parameters m) c := rfl
  have hc' : transverseDiffeomorph m y∈(n.sliceChart c).source := by
    simpa only [mfld_simps,hchart,realChart_source] using hc
  have hy' : Complex.equivRealProdCLM.symm y∈transverseAnnulusDomain m := by
    simpa only [transverseDiffeomorph_source,mem_preimage] using hy
  have hye : Complex.equivRealProdCLM.symm y∈e.source := ⟨hy',hc'⟩
  have h := holomorphic_partialHomeomorph_orientation e hye
    (transverse_transition_differentiable m c hy')
    (transverse_transition_inverse_differentiable m c (n.sliceChart c |>.map_source hc'))
  simpa only [e,mfld_simps,hchart,realChart,realTransverseChart,
    transverseDiffeomorph,Function.comp_def,OpenPartialHomeomorph.trans_apply,
    ContinuousLinearEquiv.coe_toHomeomorph] using h

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem rectanglePolar_smooth : ContDiff ℝ ∞ rectanglePolar := by
  apply contMDiff_iff_contDiff.mp
  exact Complex.equivRealProdCLM.contDiff.contMDiff.comp
    (cylinderComplexMap_smooth.comp cylinderCover_smooth)

theorem rectanglePolar_det (y : Plane) :
    (fderiv ℝ rectanglePolar y).det=2*Real.pi*(Real.exp y.1)^2 := by
  let u : ℂ := circleTurn y.2
  have h1 := (Complex.ofRealCLM.hasFDerivAt.comp y.1 (Real.hasDerivAt_exp y.1).hasFDerivAt).comp y
    (hasFDerivAt_fst : HasFDerivAt (@Prod.fst ℝ ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) y)
  have h2 := (circleTurn_deriv y.2).hasFDerivAt.comp y
    (hasFDerivAt_snd : HasFDerivAt (@Prod.snd ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) y)
  have hh := Complex.equivRealProdCLM.hasFDerivAt.comp y (h1.mul h2)
  change HasFDerivAt rectanglePolar _ y at hh
  rw [hh.fderiv,planar_det,planarArea_apply]
  have hu : u.re^2+u.im^2=1 := by
    have h := Complex.sq_norm (u)
    rw [show ‖u‖=1 from Circle.norm_coe _,one_pow] at h
    simpa only [Complex.normSq_apply,pow_two] using h.symm
  simp [Function.comp_def,Complex.mul_re,Complex.mul_im,Complex.exp_ofReal_re]
  calc
    _=2*Real.pi*(Real.exp y.1)^2*(u.re^2+u.im^2) := by ring
    _=_ := by rw [hu,mul_one]

theorem rectanglePolar_det_pos (y : Plane) : 0<(fderiv ℝ rectanglePolar y).det := by
  rw [rectanglePolar_det]
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (sq_pos_of_pos (Real.exp_pos _))

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable (m : ℕ)

theorem fixed_handle_densityChart_positive (H : AnnularHandleData Plane (Surface m))
    (hH : H.chart=restrictedTransverseCylinder m (transverseCylinderWidth m/2)) :
    PositivePartialChart H.densityChart := by
  have heq : (H.densityChart : Plane → Surface m)=transverseDiffeomorph m ∘ rectanglePolar := by
    funext y
    rw [AnnularHandleData.densityChart_apply,hH]
    rfl
  intro c y hy hc
  have hys : cylinderCover y∈H.chart.source := hy.2
  rw [hH] at hys
  have hyc : cylinderCover y∈(transverseCylinder m).source := hys.1
  rw [transverseCylinder_source] at hyc
  have hyd : rectanglePolar y∈(transverseDiffeomorph m).source := by
    rw [transverseDiffeomorph_source]
    change Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM
      (cylinderComplexMap (cylinderCover y)))∈transverseAnnulusDomain m
    simpa only [ContinuousLinearEquiv.symm_apply_apply,mem_preimage] using hyc
  have hc' : transverseDiffeomorph m (rectanglePolar y)∈(extChartAt 𝓘(ℝ,Plane) c).source := by
    simpa only [heq,Function.comp_apply] using hc
  have hpos := transverseDiffeomorph_positive m c (rectanglePolar y) hyd hc'
  have hf : DifferentiableAt ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ transverseDiffeomorph m) (rectanglePolar y) := by
    have hi := (transverseDiffeomorph m).contMDiffOn.contMDiffAt
      ((transverseDiffeomorph m).open_source.mem_nhds hyd)
    have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,Plane)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hc')
    exact (ho.comp _ hi).contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [heq,← Function.comp_assoc,fderiv_comp y hf (rectanglePolar_smooth.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) y)]
  change 0<LinearMap.det ((fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ transverseDiffeomorph m)
    (rectanglePolar y)).toLinearMap.comp (fderiv ℝ rectanglePolar y).toLinearMap)
  rw [LinearMap.det_comp]
  exact mul_pos hpos (rectanglePolar_det_pos y)

theorem exists_positive_fixed_annularHandleData :
    ∃ H : AnnularHandleData Plane (Surface m),
      H.width=transverseCylinderWidth m/2 ∧
      H.clock=positiveCircleClock (1/4) ∧ PositivePartialChart H.densityChart := by
  obtain ⟨H,hw,hH,hf⟩ := exists_fixed_annularHandleData m
  exact ⟨H,hw,hf,fixed_handle_densityChart_positive m H hH⟩

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_SurfaceComparison
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

 theorem surface_form_scalar_in_chart {Λ Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v,Ω x u v= -Ω x v u) (hΛ : ∀ x u v,Λ x u v= -Λ x v u)
    {c x : M} (hx : x∈(extChartAt 𝓘(ℝ,Plane) c).source)
    (hpos : chartTwoForm Λ c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1)≠0) :
    Ω x=(chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1) /
      chartTwoForm Λ c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1)) • Λ x := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change Ω x u v=_*Λ x u v
  rw [← chartTwoForm_apply_chart hx u v (Ω := Ω),← chartTwoForm_apply_chart hx u v (Ω := Λ)]
  change chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c x) (chartDifferential c x u) (chartDifferential c x v) =
    (chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1) /
      chartTwoForm Λ c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1)) *
        chartTwoForm Λ c (extChartAt 𝓘(ℝ,Plane) c x) (chartDifferential c x u) (chartDifferential c x v)
  rw [planar_skew_coefficient _ (chartTwoForm_skew hΩ _ _) (chartDifferential c x u) (chartDifferential c x v),
    planar_skew_coefficient _ (chartTwoForm_skew hΛ _ _) (chartDifferential c x u) (chartDifferential c x v)]
  field_simp [hpos]

 theorem surface_form_scalar {Λ Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v,Ω x u v= -Ω x v u) (hΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target →
      0 < chartTwoForm Λ c y (1,0) (0,1)) (x : M) :
    Ω x=surfaceFormRatio Λ Ω x • Λ x :=
  surface_form_scalar_in_chart hΩ hΛ (mem_extChartAt_source x)
    (ne_of_gt (hpos x _ (mem_extChartAt_target x)))

 theorem surfaceFormRatio_eq_chart {Λ Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v,Ω x u v= -Ω x v u) (hΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target →
      0 < chartTwoForm Λ c y (1,0) (0,1)) {c x : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Plane) c).source) :
    surfaceFormRatio Λ Ω x=chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1) /
      chartTwoForm Λ c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1) := by
  have he : Ω=fun z => surfaceFormRatio Λ Ω z • Λ z :=
    funext (surface_form_scalar hΩ hΛ hpos)
  conv_rhs => rw [he,chartTwoForm_spatial_smul]
  simp only [smul_apply,smul_eq_mul,(extChartAt 𝓘(ℝ,Plane) c).left_inv hx]
  exact (mul_div_cancel_right₀ _ (ne_of_gt (hpos c _ ((extChartAt 𝓘(ℝ,Plane) c).map_source hx)))).symm

 variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
 theorem surfaceFormRatio_smooth {Λ : ManifoldTwoForm Plane M}
    (hΛ : SmoothTwoForm Λ) (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0 < chartTwoForm Λ c y (1,0) (0,1))
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hsΩ : ∀ p x u v,Ω p x u v= -Ω p x v u) :
    ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞
      (fun q : P × M => surfaceFormRatio Λ (Ω q.1) q.2) := by
  intro q
  let c := q.2
  let y := extChartAt 𝓘(ℝ,Plane) c c
  have hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target := mem_extChartAt_target c
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) c)).mem_nhds
    (show (q.1,y)∈univ ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target from ⟨mem_univ _,hy⟩)
  have hnum : ContDiffAt ℝ ∞ (fun z : P × Plane => chartTwoForm (Ω z.1) c z.2 (1,0) (0,1)) (q.1,y) :=
    (((hΩ c).contDiffAt hn).clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hden : ContDiffAt ℝ ∞ (fun z : P × Plane => chartTwoForm Λ c z.2 (1,0) (0,1)) (q.1,y) :=
    ((((SmoothTwoFormFamily.const (P := P) hΛ) c).contDiffAt hn).clm_apply
      contDiffAt_const).clm_apply contDiffAt_const
  have hrat : ContDiffAt ℝ ∞ (fun z : P × Plane =>
      chartTwoForm (Ω z.1) c z.2 (1,0) (0,1)/chartTwoForm Λ c z.2 (1,0) (0,1)) (q.1,y) :=
    hnum.div hden (ne_of_gt (hpΛ c y hy))
  have hc : ContMDiffAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (extChartAt 𝓘(ℝ,Plane) c) c :=
    contMDiffAt_extChartAt
  have hin : ContMDiffAt (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,P × Plane) ∞
      (fun z : P × M => (z.1,extChartAt 𝓘(ℝ,Plane) c z.2)) q :=
    contMDiffAt_fst.prodMk_space (hc.comp q contMDiffAt_snd)
  have hlocal := hrat.contMDiffAt.comp q hin
  apply hlocal.congr_of_eventuallyEq
  have hnsource : ∀ᶠ z : P × M in 𝓝 q,z.2∈(extChartAt 𝓘(ℝ,Plane) c).source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds c)
  filter_upwards [hnsource] with z hz
  exact surfaceFormRatio_eq_chart (hsΩ z.1) hsΛ hpΛ hz

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.MomentPolytope.Annular
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Manifold MeasureTheory
open Hamiltonian

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]

 theorem exhausted_curvature_surface_packing {m q N : ℕ} [Nonempty (Fin N)]
    (bF : Fin q → Moments m) (cF : Fin q → ℝ)
    (hbF : ∀ ν j,0≤bF ν j) (hcF : ∀ ν,0 < cF ν) (hcomp : IsCompact (region bF cF))
    (A : Moments m → ℝ) (hA : ContinuousOn A (region bF cF))
    (hAp : ∀ p∈region bF cF,0<A p) (r r' : Fin N → ℝ)
    (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
    (hsimplex : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j) ≤ r i → p∈region bF cF)
    (hface : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j) ≤ r i →
      ∀ ν,(∑ j,bF ν j*p j)≠cF ν)
    (hconc : ConcaveOn ℝ (region bF cF) (fun p => A p-∑ i,max (r i-∑ j,p j) 0))
    (hmean : 0<∫ p in region bF cF,A p-∑ i,max (r i-∑ j,p j) 0)
    {τ d₀ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (hd₀ : 0<d₀)
    (houter : ∀ p∈region bF cF,p∉τ • region bF cF → d₀≤A p-∑ i,max (r i-∑ j,p j) 0)
    (D : ℕ → Set M) (hD : ∀ ℓ,IsCompact (D ℓ))
    (hmono : ∀ ℓ,D ℓ⊆interior (D (ℓ+1))) (hcover : (⋃ ℓ,D ℓ)=univ)
    (hcD : ∀ ℓ,IsPreconnected (interior (D ℓ))) (hne : ∀ ℓ,(interior (D ℓ)).Nonempty)
    (hb : ∀ ℓ,HasSmoothSurfaceBoundary (D ℓ)) (hor : PositivePlaneTransitions M)
    (H : AnnularHandleData Plane M)
    {b δ : ℝ} (hbp : 0<b) (hbw : b<H.width) (hδ : 0<δ) (hsmall : δ<1/2)
    (heor : PositivePartialChart H.densityChart)
    (hclock : H.clock=positiveCircleClock δ)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0 < chartTwoForm Λ c y (1,0) (0,1))
    (Γ : ℕ → Moments m → ManifoldOneForm Plane M) (hΓ : ∀ ℓ,SmoothOneFormFamily (Γ ℓ))
    (hpos : ∀ ℓ,∀ p∈region bF cF,∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target →
      (extChartAt 𝓘(ℝ,Plane) c).symm y∈D ℓ →
      0 < chartTwoForm (manifoldExteriorOneForm (Γ ℓ p)) c y (1,0) (0,1))
    (hlim : TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (hD ℓ)
      (manifoldExteriorOneForm (Γ ℓ p))) A Filter.atTop (region bF cF)) :
    ∃ ℓ,∃ φ : Fin N → Ambient (m+1) → M × PlanePhase (Fin m),
      (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
        (globalHorizontalCoupling phaseArea (Γ ℓ ∘ planeMoments)) (φ i)) ∧
      (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (D ℓ ×ˢ planeRegion bF cF))) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  let κ : ℕ → Moments m → ManifoldTwoForm Plane M := fun ℓ p => manifoldExteriorOneForm (Γ ℓ p)
  have hκ ℓ : SmoothTwoFormFamily (κ ℓ) := manifoldExteriorOneForm_family_smooth (hΓ ℓ)
  have hsκ ℓ p x u v : κ ℓ p x u v= -κ ℓ p x v u := manifoldExteriorOneForm_skew _ _ _ _
  let d : ℕ → Moments m × M → ℝ := fun ℓ q => surfaceFormRatio Λ (κ ℓ q.1) q.2
  have hd ℓ : ContMDiff (𝓘(ℝ,Moments m).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ (d ℓ) :=
    surfaceFormRatio_smooth hΛ hsΛ hpΛ (hκ ℓ) (hsκ ℓ)
  have heq ℓ p x : κ ℓ p x=d ℓ (p,x) • Λ x := surface_form_scalar (hsκ ℓ p) hsΛ hpΛ x
  have hdp ℓ p (hp : p∈region bF cF) x (hx : x∈D ℓ) : 0<d ℓ (p,x) :=
    div_pos (hpos ℓ p hp x _ (mem_extChartAt_target x) (by simpa using hx))
      (hpΛ x _ (mem_extChartAt_target x))
  have hlim' : TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (hD ℓ)
      (fun x => d ℓ (p,x) • Λ x)) A Filter.atTop (region bF cF) := by
    convert hlim using 1
    all_goals try with_reducible_and_instances rfl
    exact funext (fun ℓ => funext (fun p => congrArg (compactSurfaceFormIntegral (hD ℓ))
      (funext (fun x => (heq ℓ p x).symm))))
  exact exhausted_surface_packing_bp240 bF cF hbF hcF hcomp A hA hAp r r' hr' hrr hsimplex hface
    hconc hmean hτ hτ1 hd₀ houter D hD hmono hcover hcD hne hb hor H hbp hbw hδ hsmall
    heor hclock hΛ hsΛ hpΛ d hd hdp Γ hΓ heq hlim'

end PackingSufficiencySupport.MomentPolytope.Annular
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_RationalSlack
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
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

 theorem physicalArea_continuous (D S : ℕ) (c L : ℝ) : Continuous (physicalArea D S c L) := by
  unfold physicalArea
  fun_prop

 attribute [local instance] OAI.PackingSufficiencySupport.CubicModel.instSigmaCompactSpaceElemAffineHAddNatOfNatBaseCurve
theorem exists_physicalPrimitive_extension {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (c L : ℝ) {P : Set (Moments 2)} (hP : IsCompact P)
    (hPS : MapsTo (physicalParameter L) P (Radial.lowerTrapezoid A B)) (ℓ : ℕ) :
    ∃ Γ : Moments 2 → ManifoldOneForm RealModel BaseCurve,
      SmoothOneFormFamily Γ ∧ ∀ᶠ q in 𝓝ˢ (P ×ˢ cubicExhaustion ℓ),
        physicalParameter L q.1∈Radial.lowerTrapezoid A B →
        Γ q.1 q.2=physicalPrimitive (A := A) (B := B) D S c L q.1 q.2 := by
  obtain ⟨Γ,hΓ,he⟩ := exists_radialPrimitive_smooth_extension hA hAB
    (cubicDegree D) (cubicMarkedOrder S) c (hP.image (physicalParameter_smooth L).continuous)
    (image_subset_iff.mpr hPS) (cubicExhaustion_compact ℓ)
  refine ⟨Γ ∘ physicalParameter L,hΓ.comp (physicalParameter_smooth L),?_⟩
  apply mem_nhdsSet_iff_forall.mpr
  intro q hq
  have hn := mem_nhdsSet_iff_forall.mp he (physicalParameter L q.1,q.2)
    ⟨mem_image_of_mem _ hq.1,hq.2⟩
  have hc : Continuous (fun q : Moments 2 × BaseCurve => (physicalParameter L q.1,q.2)) :=
    ((physicalParameter_smooth L).continuous.comp continuous_fst).prodMk continuous_snd
  exact hc.continuousAt.eventually hn

 theorem physicalPrimitive_extension_curvature {A B : ℕ} {D S : ℕ} {c L : ℝ}
    {P : Set (Moments 2)} {ℓ : ℕ} {Γ : Moments 2 → ManifoldOneForm RealModel BaseCurve}
    (he : ∀ᶠ q in 𝓝ˢ (P ×ˢ cubicExhaustion ℓ),
      physicalParameter L q.1∈Radial.lowerTrapezoid A B →
      Γ q.1 q.2=physicalPrimitive (A := A) (B := B) D S c L q.1 q.2)
    {p : Moments 2} (hp : p∈P) (hs : physicalParameter L p∈Radial.lowerTrapezoid A B)
    {x : BaseCurve} (hx : x∈cubicExhaustion ℓ) :
    manifoldExteriorOneForm (Γ p) x=
      radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c
        (physicalParameter L p) x := by
  apply manifoldExteriorOneForm_congr_germ
  have hn := mem_nhdsSet_iff_forall.mp he (p,x) ⟨hp,hx⟩
  filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hn] with y hy
  exact hy hs

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

local instance instSigmaCompactSpaceElemAffineHAddNatOfNatBaseCurve_1 : SigmaCompactSpace BaseCurve := curveSigmaCompact (parameters 0)

 theorem physicalArea_pos {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    {c L : ℝ} (hc : 0 < c) {p : Moments 2}
    (hp : physicalParameter L p∈Radial.lowerTrapezoid A B) : 0<physicalArea D S c L p := by
  have hb : 3*(B:ℝ)<D := by exact_mod_cast hB
  have hs : 3*(S:ℝ)<D := by exact_mod_cast hS
  have ht : L*p 0+L*p 1<(B:ℝ) := hp.2.2.2
  unfold physicalArea
  apply mul_pos (mul_pos hc ?_) Real.pi_pos
  by_cases hh : (S:ℝ)≤L*p 0+L*p 1
  · rw [max_eq_right (sub_nonpos.mpr hh)]
    linarith
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hh))]
    linarith

 theorem actual_cubic_representative_packing_bp240_oai {A B D S N q : ℕ} [Nonempty (Fin N)]
    (hA : 0<A) (hS0 : 0<S) (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {c L : ℝ} (hc : 0 < c)
    (bF : Fin q → Moments 2) (cF : Fin q → ℝ)
    (hbF : ∀ ν j,0≤bF ν j) (hcF : ∀ ν,0 < cF ν) (hcomp : IsCompact (region bF cF))
    (hPS : MapsTo (physicalParameter L) (region bF cF) (Radial.lowerTrapezoid A B))
    (r r' : Fin N → ℝ) (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
    (hsimplex : ∀ i,∀ p : Moments 2,(∀ j,0≤p j) → (∑ j,p j) ≤ r i → p∈region bF cF)
    (hface : ∀ i,∀ p : Moments 2,(∀ j,0≤p j) → (∑ j,p j) ≤ r i →
      ∀ ν,(∑ j,bF ν j*p j)≠cF ν)
    (hconc : ConcaveOn ℝ (region bF cF) (fun p => physicalArea D S c L p-∑ i,max (r i-∑ j,p j) 0))
    (hmean : 0<∫ p in region bF cF,physicalArea D S c L p-∑ i,max (r i-∑ j,p j) 0)
    {τ d₀ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (hd₀ : 0<d₀)
    (houter : ∀ p∈region bF cF,p∉τ • region bF cF →
      d₀≤physicalArea D S c L p-∑ i,max (r i-∑ j,p j) 0) :
    ∃ ℓ,∃ Γ : Moments 2 → ManifoldOneForm RealModel BaseCurve,
      SmoothOneFormFamily Γ ∧
      (∀ᶠ q in 𝓝ˢ (region bF cF ×ˢ cubicExhaustion ℓ),
        physicalParameter L q.1∈Radial.lowerTrapezoid A B →
        Γ q.1 q.2=physicalPrimitive (A := A) (B := B) D S c L q.1 q.2) ∧
      ∃ φ : Fin N → Ambient 3 → BaseCurve × PlanePhase (Fin 2),
        (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
          (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments)) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall 3 (r' i)) (interior (cubicExhaustion ℓ ×ˢ planeRegion bF cF))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall 3 (r' i)) (φ j '' closedBall 3 (r' j))) := by
  choose Γ hΓ he using fun ℓ => exists_physicalPrimitive_extension hA hAB D S c L hcomp hPS ℓ
  have hform ℓ p (hp : p∈region bF cF) x (hx : x∈cubicExhaustion ℓ) :=
    physicalPrimitive_extension_curvature (he ℓ) hp (hPS hp) hx
  have hlim : TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (cubicExhaustion_compact ℓ)
      (manifoldExteriorOneForm (Γ ℓ p))) (physicalArea D S c L) atTop (region bF cF) := by
    apply (physicalArea_uniform_bp240 hA hS0 hAB hSB hB hS hcomp L hPS hc).congr
    filter_upwards [] with ℓ
    intro p hp
    exact (compactSurfaceFormIntegral_congr (cubicExhaustion_compact ℓ)
      (fun x hx => hform ℓ p hp x hx)).symm
  have hmono ℓ : cubicExhaustion ℓ⊆interior (cubicExhaustion (ℓ+1)) := by
    apply projectionDomain_nested
    simp only [exhaustionRadius,Nat.cast_add,Nat.cast_one]
    linarith
  have hconn ℓ : IsConnected (interior (cubicExhaustion ℓ)) :=
    projectionDomain_interior_connected (exhaustionRadius_pos (parameters 0) ℓ)
      (exhaustionRadius_branch (parameters 0) ℓ)
  have hcover : (⋃ ℓ,cubicExhaustion ℓ)=univ :=
    projectionDomain_cover (parameters 0) (2+∑ j,‖parameters 0 j‖)
  obtain ⟨H,_hw,hclock,hpos⟩ := exists_positive_fixed_annularHandleData 0
  have hcurv ℓ p (hp : p∈region bF cF) b y (hy : y∈(extChartAt 𝓘(ℝ,Plane) b).target)
      (hx : (extChartAt 𝓘(ℝ,Plane) b).symm y∈cubicExhaustion ℓ) :
      0 < chartTwoForm (manifoldExteriorOneForm (Γ ℓ p)) b y (1,0) (0,1) := by
    dsimp only [chartTwoForm]
    erw [hform ℓ p hp _ hx]
    exact radialForm_positive_bp240 hA hAB (cubicMarked_lt_degree hB hS) hc (hPS hp) b hy
  obtain ⟨ℓ,φ,hφ,hm,hd⟩ := Annular.exhausted_curvature_surface_packing bF cF hbF hcF hcomp
    (physicalArea D S c L) (physicalArea_continuous D S c L).continuousOn
    (fun p hp => physicalArea_pos hB hS hc (hPS hp)) r r' hr' hrr hsimplex hface
    hconc hmean hτ hτ1 hd₀ houter cubicExhaustion cubicExhaustion_compact hmono hcover
    (fun ℓ => (hconn ℓ).isPreconnected) (fun ℓ => (hconn ℓ).nonempty)
    (fun ℓ => projectionDomain_smoothBoundary (exhaustionRadius_pos (parameters 0) ℓ)
      (exhaustionRadius_branch (parameters 0) ℓ)) (positivePlaneTransitions (parameters 0))
    H (half_pos H.width_pos) (by linarith [H.width_pos]) (by norm_num : (0:ℝ)<1/4)
    (by norm_num : (1:ℝ)/4<1/2) hpos hclock
    (DiagonalQuadrics.curveFSForm_smooth (parameters 0) (1/Real.pi)) (DiagonalQuadrics.curveFSForm_skew (parameters 0) (1/Real.pi))
    (fun b y hy => DiagonalQuadrics.curveFSForm_positive (parameters 0) (one_div_pos.mpr Real.pi_pos) b hy)
    Γ hΓ hcurv hlim
  exact ⟨ℓ,Γ ℓ,hΓ ℓ,he ℓ,φ,hφ,hm,hd⟩

end PackingSufficiencySupport.CubicModel
end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.CubicModel.actual_cubic_representative_packing_bp240_oai := @OAI.PackingSufficiencySupport.CubicModel.actual_cubic_representative_packing_bp240_oai
