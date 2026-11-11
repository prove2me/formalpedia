-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndCutoff_partition_mass_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:50.279307+00:00
-- url     : https://prove2.me/submissions/60752d7f-59ef-4320-b86b-5981f37ae98f

import Mathlib
import Definitions.Def_OAIQ240Bp019

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

theorem euclideanExteriorOneForm_smul (a : ℝ) {α : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) :
    euclideanExteriorOneForm (a • α) x = a • euclideanExteriorOneForm α x := by
  rw [euclideanExteriorOneForm,fderiv_const_smul hα]
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,smul_apply,
    smul_eq_mul]
  ring



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ChartSupportedDensity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul
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

theorem SmoothTwoFormFamily.neg {Ω : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) : SmoothTwoFormFamily (-Ω) := by
  have he : -Ω = fun p => (-1:ℝ) • Ω p := by ext p x u v; simp
  rw [he]
  exact hΩ.smul contDiff_const

theorem SmoothTwoFormFamily.sub {Ω Λ : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) (hΛ : SmoothTwoFormFamily Λ) : SmoothTwoFormFamily (Ω-Λ) := by
  have he : Ω-Λ = Ω+(-Λ) := sub_eq_add_neg Ω Λ
  rw [he]
  exact hΩ.add hΛ.neg


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory



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

end

variable {ι : Type*} [Fintype ι]

theorem affineFSForm_eq_exterior (a : ℝ) :
    (affineFSForm a : PlanePhase ι → _) = euclideanExteriorOneForm (affineFSPrimitive a) := by
  funext z
  ext v w
  exact (affineFSPrimitive_exterior a z v w).symm

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricCurveManifold
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

variable {m : ℕ} (a : Fin m → ℂ)

theorem re_ne_zero_of_sq_re_pos {z : ℂ} (hz : 0<(z^2).re) : z.re≠0 := by
  intro h
  have hi := sq_nonneg z.im
  simp only [pow_two,Complex.mul_re,h,zero_mul] at hz
  nlinarith

theorem endSign_positive_unique {z : ℂ} {b c : Bool}
    (hb : 0<(endSign b*z).re) (hc : 0<(endSign c*z).re) : b=c := by
  cases b <;> cases c <;> simp_all [endSign]
  <;> linarith

theorem exists_positive_endSign {z : ℂ} (hz : z.re≠0) : ∃ b : Bool,0<(endSign b*z).re := by
  rcases lt_or_gt_of_ne hz with h|h
  · exact ⟨true,by simpa [endSign] using neg_pos.mpr h⟩
  · exact ⟨false,by simpa [endSign] using h⟩

theorem infinityBranch_disjoint {ε η : Fin m → Bool} (h : ε≠η) :
    Disjoint (infinityBranch a ε) (infinityBranch a η) := by
  rw [Set.disjoint_left]
  intro x hx hy
  apply h
  funext j
  exact endSign_positive_unique (hx.2.2 j) (hy.2.2 j)

theorem exists_infinityBranch {x : locus a} (hx : x.val.1≠0)
    (hr : x.val.1⁻¹∈infinityRegion a) : ∃ ε : Fin m → Bool,x∈infinityBranch a ε := by
  have h : ∀ j,∃ b : Bool,0<(endSign b*(x.val.1⁻¹*x.val.2 j)).re := by
    intro j
    apply exists_positive_endSign
    apply re_ne_zero_of_sq_re_pos
    rw [normalized_coordinate_sq a hx]
    exact hr j
  choose ε hε using h
  exact ⟨ε,hx,hr,hε⟩

end PackingSufficiencySupport.DiagonalQuadrics

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
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realInfinityChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_J_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_J_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_single_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseArea_single_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_J_J _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_J_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_J_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_fderiv _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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

noncomputable section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
namespace PackingSufficiencySupport.Hamiltonian
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem partialChartCoefficient_contDiffOn
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) :
    ContDiffOn ℝ ∞ (partialChartCoefficient e Ω) e.source := by
  intro y hy
  have hs := euclideanPullbackTwoForm_contDiffAt (E := Plane) (F := Plane) (M := M)
    (Ω := fun _ : ℝ => Ω) (g := e) (p := ((0:ℝ),y))
    (SmoothTwoFormFamily.const (P := ℝ) hΩ)
    (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hy))
  exact (((hs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).comp y
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

theorem partialChartCoefficient_change
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    {Ω : ManifoldTwoForm Plane M} (hΩ : ∀ x u v,Ω x u v= -Ω x v u)
    {c : M} {y : Plane} (hy : y∈e.source)
    (hc : e y∈(extChartAt 𝓘(ℝ,Plane) c).source) :
    partialChartCoefficient e Ω y=
      (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ e) y).det *
        chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c (e y)) (1,0) (0,1) := by
  unfold partialChartCoefficient
  rw [euclideanPullbackTwoForm_chart (e.mdifferentiableAt (by simp) hy) hc,
    ContinuousLinearMap.bilinearComp_apply,
    planar_skew_coefficient _ (chartTwoForm_skew hΩ _ _),← planar_det,mul_comm]

theorem partialChart_area_integral_change
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    {Ω : ManifoldTwoForm Plane M} (hΩ : ∀ x u v,Ω x u v= -Ω x v u)
    {c : M} {K : Set M} (hK : IsCompact K) (hKe : K⊆e.target)
    (hKc : K⊆(extChartAt 𝓘(ℝ,Plane) c).source)
    (hpos : ∀ y∈e.symm '' K,
      0<(fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ e) y).det) :
    (∫ y in e.symm '' K,partialChartCoefficient e Ω y)=
      ∫ y in extChartAt 𝓘(ℝ,Plane) c '' K,chartTwoForm Ω c y (1,0) (0,1) := by
  let g : Plane → Plane := extChartAt 𝓘(ℝ,Plane) c ∘ e
  have hys {y : Plane} (hy : y∈e.symm '' K) : y∈e.source := by
    obtain ⟨x,hx,rfl⟩ := hy
    exact e.map_target (hKe hx)
  have hyK {y : Plane} (hy : y∈e.symm '' K) : e y∈K := by
    obtain ⟨x,hx,rfl⟩ := hy
    have heq : e (e.symm x)=x := e.right_inv (hKe hx)
    rwa [heq]
  have hgs : ∀ y∈e.symm '' K,ContDiffAt ℝ ∞ g y := by
    intro y hy
    have hi := e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hys hy))
    have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,Plane)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hKc (hyK hy))
    exact (ho.comp y hi).contDiffAt
  have hgi : InjOn g (e.symm '' K) := by
    intro y hy z hz heq
    exact e.injOn (hys hy) (hys hz)
      ((extChartAt 𝓘(ℝ,Plane) c).injOn (hKc (hyK hy)) (hKc (hyK hz)) heq)
  have him : g '' (e.symm '' K)=extChartAt 𝓘(ℝ,Plane) c '' K := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨e z,hyK hz,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨e.symm x,⟨x,hx,rfl⟩,congrArg (extChartAt 𝓘(ℝ,Plane) c) (e.right_inv (hKe hx))⟩
  have hmeas : MeasurableSet (e.symm '' K) :=
    (hK.image_of_continuousOn (e.symm.contMDiffOn.continuousOn.mono hKe)).measurableSet
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume hmeas
    (f' := fderiv ℝ g)
    (fun y hy => ((hgs y hy).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
    hgi (fun y => chartTwoForm Ω c y (1,0) (0,1))
  rw [him] at hi
  rw [hi]
  apply setIntegral_congr_fun hmeas
  intro y hy
  change partialChartCoefficient e Ω y=|(fderiv ℝ g y).det| •
    chartTwoForm Ω c (g y) (1,0) (0,1)
  rw [partialChartCoefficient_change e hΩ (hys hy) (hKc (hyK hy)),
    abs_of_pos (hpos y hy)]
  rfl

theorem chartMass_eq_partialChart_integral
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    {Ω : ManifoldTwoForm Plane M} (hΩ : ∀ x u v,Ω x u v= -Ω x v u)
    {c : M} {K : Set M} (hK : IsCompact K) (hKe : K⊆e.target)
    (hKc : K⊆(extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ x,x∉K→Ω x=0)
    (hpos : ∀ y∈e.symm '' K,
      0<(fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ e) y).det) :
    chartMass c Ω=∫ y in e.symm '' K,partialChartCoefficient e Ω y := by
  rw [chartMass_eq_setIntegral hK hKc hz]
  exact (partialChart_area_integral_change e hΩ hK hKe hKc hpos).symm

end PackingSufficiencySupport.Hamiltonian


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
variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
  (ε : Fin m → Bool)

theorem infinity_transition_differentiable (c : locus a) {z : ℂ}
    (hz : z∈infinityDomain a) :
    DifferentiableAt ℂ (((normalChartAt a c).sliceChart c) ∘ (infinityChart a ε).symm) z := by
  let n := normalChartAt a c
  have hs := (curveCoordinate n.coordinate).contDiff.contDiffAt.comp z
    (infinityPoint_contDiffAt a ε hz)
  apply (hs.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).congr_of_eventuallyEq
  filter_upwards [(infinityDomain_open a).mem_nhds hz] with t ht
  change curveCoordinate n.coordinate ((infinityInverse a ε t).val)=_
  rw [infinityInverse_val a ε ht.1]
  rfl

theorem infinity_transition_inverse_differentiable (c : locus a) {z : ℂ}
    (hz : z∈((normalChartAt a c).sliceChart c).target)
    (hn : (((normalChartAt a c).sliceChart c).symm z).val.1≠0) :
    DifferentiableAt ℂ ((infinityChart a ε) ∘ ((normalChartAt a c).sliceChart c).symm) z := by
  have hs := ((normalChartAt a c).sliceChart_inverse_smooth c).contDiffAt
    (((normalChartAt a c).sliceChart c).open_target.mem_nhds hz)
  exact hs.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.fst |>.inv hn

theorem infinityDiffeomorph_positive : PositivePartialChart (infinityDiffeomorph a ε) := by
  intro c y hy hc
  let n := normalChartAt a c
  let e := (infinityChart a ε).symm.trans (n.sliceChart c)
  have hchart : chartAt Plane c=realChart a c := rfl
  have hc' : infinityDiffeomorph a ε y∈(n.sliceChart c).source := by
    simpa only [mfld_simps,hchart,realChart_source] using hc
  have hy' : Complex.equivRealProdCLM.symm y∈infinityDomain a := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hye : Complex.equivRealProdCLM.symm y∈e.source := ⟨hy',hc'⟩
  have hn : (((n.sliceChart c).symm ((n.sliceChart c) (infinityDiffeomorph a ε y))).val.1)≠0 := by
    rw [(n.sliceChart c).left_inv hc']
    exact ((infinityChart a ε).map_target hy').1
  have h := holomorphic_partialHomeomorph_orientation e hye
    (infinity_transition_differentiable a ε c hy')
    (infinity_transition_inverse_differentiable a ε c (n.sliceChart c |>.map_source hc') hn)
  simpa only [e,mfld_simps,hchart,realChart,realInfinityChart,
    infinityDiffeomorph,Function.comp_def,OpenPartialHomeomorph.trans_apply,
    ContinuousLinearEquiv.coe_toHomeomorph] using h

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

theorem curveEndCutoff_infinity (g : ℝ → ℝ) (ε : Fin m → Bool) {y : Plane}
    (hy : y∈(infinityDiffeomorph a ε).source) :
    curveEndCutoff a g (infinityDiffeomorph a ε y)=1-g (radiusSq y) := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain a := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hval : (infinityDiffeomorph a ε y).val=infinityPoint a ε (Complex.equivRealProdCLM.symm y) :=
    infinityInverse_val a ε hD.1
  unfold curveEndCutoff inverseComplementCutoff curveProjection
  rw [hval]
  simp only [infinityPoint,inv_ne_zero hD.1,↓reduceIte,inv_inv]
  congr 2
  change y.1*y.1+y.2*y.2=y.1^2+y.2^2
  ring

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

theorem curveFSPrimitive_exterior (c : ℝ) :
    manifoldExteriorOneForm (curveFSPrimitive a c)=curveFSForm a c := by
  have hα : ∀ z : PlanePhase (Option (Fin m)),ContDiffOn ℝ ∞
      (chartOneForm (affineFSPrimitive c) z) (extChartAt 𝓘(ℝ,PlanePhase (Option (Fin m))) z).target := by
    intro z
    rw [show chartOneForm (affineFSPrimitive c) z=affineFSPrimitive c from
      funext (vector_chartOneForm (affineFSPrimitive c) z)]
    exact (affineFSPrimitive_smooth c).contDiffOn
  funext x
  change manifoldExteriorOneForm (manifoldPullbackOneForm
    (fun _ => (affineFSPrimitive c : PlanePhase (Option (Fin m)) → _)) (phaseInclusion a) 0) x=_
  rw [manifold_pullback_exterior hα (phaseInclusion_smooth a) x]
  rw [vector_exteriorOneForm,← affineFSForm_eq_exterior]
  rfl

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_CubicFubiniStudy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
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

theorem infinityRegularPoint_fderiv {s : ℂ} (hs : s∈infinityRegion a) (u : ℂ) :
    fderiv ℂ (infinityRegularPoint a ε) s u=(u,fderiv ℂ (infinityRoot a ε) s u) := by
  have hr := ((infinityRoot_contDiffAt a ε hs).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have H := (hasFDerivAt_id s).prodMk hr
  change HasFDerivAt (infinityRegularPoint a ε) _ s at H
  rw [H.fderiv]
  rfl

theorem infinityPoint_fderiv {s : ℂ} (hs : s∈infinityDomain a) (u : ℂ) :
    fderiv ℂ (infinityPoint a ε) s u=
      (-u/s^2,fun j => (fderiv ℂ (infinityRoot a ε) s u j)/s-
        (infinityRoot a ε s j/s)*(u/s)) := by
  have hi := (hasDerivAt_inv hs.1).hasFDerivAt
  have hr := ((infinityRoot_contDiffAt a ε hs.2).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have H := hi.prodMk (hi.smul hr)
  change HasFDerivAt (infinityPoint a ε) _ s at H
  rw [H.fderiv]
  apply Prod.ext
  · change u * (-(s^2)⁻¹)= -u/s^2
    ring
  · funext j
    change s⁻¹ * (fderiv ℂ (infinityRoot a ε) s u j)+
      (u * (-(s^2)⁻¹))*infinityRoot a ε s j=_
    ring

theorem realPhaseDerivative_fderiv {f : ℂ → Affine m} {s : ℂ}
    (hf : DifferentiableAt ℂ f s) :
    fderiv ℝ (fun y : Plane => affinePhase m (f (Complex.equivRealProdCLM.symm y)))
      (Complex.equivRealProdCLM s)=realPhaseDerivative (fderiv ℂ f s) := by
  have hd := (affinePhase m).hasFDerivAt.comp (Complex.equivRealProdCLM s)
    ((hf.hasFDerivAt.restrictScalars ℝ).comp (Complex.equivRealProdCLM s)
      Complex.equivRealProdCLM.symm.hasFDerivAt)
  simpa only [ContinuousLinearEquiv.symm_apply_apply,Function.comp_def,realPhaseDerivative] using hd.fderiv

end

 theorem complexArea_apply (z v : ℂ) : complexArea z v=z.re*v.im-z.im*v.re := by
  simp only [complexArea,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

 theorem complexArea_sub (z v w : ℂ) : complexArea z (v-w)=complexArea z v-complexArea z w := by
  simp only [complexArea,mul_sub,Complex.sub_im]

 theorem complexArea_mul (s z v : ℂ) : complexArea (s*z) (s*v)=Complex.normSq s*complexArea z v := by
  unfold complexArea
  rw [map_mul]
  have he : conj s*conj z*(s*v)=(Complex.normSq s : ℂ)*(conj z*v) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [he]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

 theorem complexArea_self_mul (z u : ℂ) : complexArea z (z*u)=Complex.normSq z*u.im := by
  unfold complexArea
  rw [← mul_assoc,← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

 theorem complex_div_im (s u : ℂ) : (u/s).im=complexArea s u/Complex.normSq s := by
  rw [Complex.div_im,complexArea_apply]
  ring

 theorem complexArea_div_derivative (s w u v : ℂ) :
    complexArea (w/s) (v/s-(w/s)*(u/s))=
      complexArea w v/Complex.normSq s - Complex.normSq w/(Complex.normSq s)^2*complexArea s u := by
  rw [complexArea_sub,complexArea_self_mul,Complex.normSq_div,complex_div_im]
  have h : complexArea (w/s) (v/s)=complexArea w v/Complex.normSq s := by
    rw [div_eq_mul_inv,div_eq_mul_inv,mul_comm w,mul_comm v,complexArea_mul,Complex.normSq_inv]
    ring
  rw [h]
  ring

 theorem phaseSq_affinePhase {m : ℕ} (z : Affine m) :
    phaseSq (affinePhase m z)=Complex.normSq z.1+∑ j,Complex.normSq (z.2 j) := by
  simp only [phaseSq,phaseDot_apply,Fintype.sum_option,affinePhase_none,affinePhase_some]
  rfl

 theorem phaseArea_affinePhase {m : ℕ} (z v : Affine m) :
    phaseArea (affinePhase m z) (affinePhase m v)=complexArea z.1 v.1+∑ j,complexArea (z.2 j) (v.2 j) := by
  simp only [phaseArea_apply,Fintype.sum_option,affinePhase_none,affinePhase_some,complexArea_apply]

 theorem affineFSPrimitive_complex {m : ℕ} (c : ℝ) (z v : Affine m) :
    affineFSPrimitive c (affinePhase m z) (affinePhase m v)=
      c/(2*(1+Complex.normSq z.1+∑ j,Complex.normSq (z.2 j)))*
        (complexArea z.1 v.1+∑ j,complexArea (z.2 j) (v.2 j)) := by
  change c/(2*(1+phaseSq (affinePhase m z)))*phaseArea (affinePhase m z) (affinePhase m v)=_
  rw [phaseSq_affinePhase,phaseArea_affinePhase]
  rw [add_assoc]

 theorem affineFSPrimitive_projective_swap {m : ℕ} (c : ℝ) {s : ℂ} (hs : s≠0)
    (w : Fin m → ℂ) (u : ℂ) (v : Fin m → ℂ) :
    affineFSPrimitive c (affinePhase m (s⁻¹,fun j => w j/s))
      (affinePhase m (-u/s^2,fun j => v j/s-(w j/s)*(u/s)))=
    affineFSPrimitive c (affinePhase m (s,w)) (affinePhase m (u,v))-
      c/(2*Complex.normSq s)*complexArea s u := by
  have hq : Complex.normSq s≠0 := mt Complex.normSq_eq_zero.mp hs
  have hden : 0<1+Complex.normSq s+∑ j,Complex.normSq (w j) := by
    have hw : 0≤∑ j,Complex.normSq (w j) := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
    linarith [Complex.normSq_nonneg s]
  have hbase : complexArea (s⁻¹) (-u/s^2)= -(complexArea s u)/(Complex.normSq s)^2 := by
    have h := complexArea_div_derivative s 1 u 0
    have he : (0 : ℂ)/s-(1/s)*(u/s)= -u/s^2 := by ring
    rw [he] at h
    simp only [one_div,complexArea_apply,Complex.one_re,Complex.one_im,Complex.zero_re,
      Complex.zero_im,mul_zero,sub_zero,Complex.normSq_one,zero_div,zero_sub] at h ⊢
    exact h.trans (by ring)
  rw [affineFSPrimitive_complex,affineFSPrimitive_complex,hbase,Complex.normSq_inv]
  simp only [Complex.normSq_div,complexArea_div_derivative,Finset.sum_sub_distrib,
    ← Finset.sum_div,← Finset.sum_mul]
  have hd : 1+Complex.normSq s+∑ j,Complex.normSq (w j)≠0 := ne_of_gt hden
  field_simp [hq,hd]
  ring_nf
  field_simp [hd]
  ring

end PackingSufficiencySupport.DiagonalQuadrics

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

 theorem euclideanPullbackOneForm_comp {g : N → M} {f : G → N} {x : G}
    (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g (f x))
    (hf : MDifferentiableAt 𝓘(ℝ,G) 𝓘(ℝ,F) f x)
    (α : ManifoldOneForm E M) :
    euclideanPullbackOneForm (E := F) (F := G) (fun _ => manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) f (0,x)=
      euclideanPullbackOneForm (E := E) (F := G) (fun _ => α) (g ∘ f) (0,x) := by
  change (α (g (f x))).comp
    ((manifoldMapDifferential (E := E) (F := F) g (f x)).comp
      (manifoldMapDifferential (E := F) (F := G) f x))=
    (α (g (f x))).comp (manifoldMapDifferential (E := E) (F := G) (g ∘ f) x)
  rw [manifoldMapDifferential_comp hg hf]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldFormTransport
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

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

 theorem HasCompactSupport.left_slice {F : Type*} [Zero F] {f : ℝ × ℝ → F}
    (hf : HasCompactSupport f) (y : ℝ) : HasCompactSupport (fun x => f (x,y)) := by
  apply HasCompactSupport.intro (hf.image continuous_fst)
  intro x hx
  by_contra hn
  exact hx ⟨(x,y),subset_tsupport f hn,rfl⟩

 theorem HasCompactSupport.right_slice {F : Type*} [Zero F] {f : ℝ × ℝ → F}
    (hf : HasCompactSupport f) (x : ℝ) : HasCompactSupport (fun y => f (x,y)) := by
  apply HasCompactSupport.intro (hf.image continuous_snd)
  intro y hy
  by_contra hn
  exact hy ⟨(x,y),subset_tsupport f hn,rfl⟩

 theorem integral_compact_partial_fst {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ z, fderiv ℝ f z (1,0))=0 := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (1,0)) :=
    (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hdc := hc.fderiv_apply (𝕜 := ℝ) (1,0)
  rw [Measure.volume_eq_prod ℝ ℝ,integral_prod_symm _
    (hd.continuous.integrable_of_hasCompactSupport hdc)]
  have he (y : ℝ) : (∫ x, fderiv ℝ f (x,y) (1,0))=0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun x => f (x,y))
    · intro x
      exact ((hf.differentiable (by simp) (x,y)).hasFDerivAt).comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
    · exact (hd.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.left_slice hdc y)
    · exact (hf.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.left_slice hc y)
  simp_rw [he]
  exact integral_zero _ _

 theorem integral_compact_partial_snd {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ z, fderiv ℝ f z (0,1))=0 := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (0,1)) :=
    (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hdc := hc.fderiv_apply (𝕜 := ℝ) (0,1)
  rw [Measure.volume_eq_prod ℝ ℝ,integral_prod _
    (hd.continuous.integrable_of_hasCompactSupport hdc)]
  have he (x : ℝ) : (∫ y, fderiv ℝ f (x,y) (0,1))=0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun y => f (x,y))
    · intro y
      exact ((hf.differentiable (by simp) (x,y)).hasFDerivAt).comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
    · exact (hd.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.right_slice hdc x)
    · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.right_slice hc x)
  simp_rw [he]
  exact integral_zero _ _

 theorem compact_planar_stokes {α : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hc : HasCompactSupport α) :
    (∫ z, fderiv ℝ α z (1,0) (0,1) - fderiv ℝ α z (0,1) (1,0))=0 := by
  have h1 : ContDiff ℝ ∞ (fun z => α z (0,1)) := hα.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun z => α z (1,0)) := hα.clm_apply contDiff_const
  have hc1 : HasCompactSupport (fun z => α z (0,1)) := hc.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1)) rfl
  have hc2 : HasCompactSupport (fun z => α z (1,0)) := hc.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0)) rfl
  have he1 (z v : ℝ × ℝ) : fderiv ℝ (fun z => α z (0,1)) z v=fderiv ℝ α z v (0,1) := by
    rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
    simp only [add_apply,ContinuousLinearMap.comp_apply,fderiv_const_apply,
      zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
  have he2 (z v : ℝ × ℝ) : fderiv ℝ (fun z => α z (1,0)) z v=fderiv ℝ α z v (1,0) := by
    rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
    simp only [add_apply,ContinuousLinearMap.comp_apply,fderiv_const_apply,
      zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
  have hd1 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun z => α z (0,1)) z (1,0)) :=
    (h1.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hd2 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun z => α z (1,0)) z (0,1)) :=
    (h2.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  simp_rw [← he1,← he2]
  rw [integral_sub
    (hd1.continuous.integrable_of_hasCompactSupport
      (hc1.fderiv_apply (𝕜 := ℝ) (1,0)))
    (hd2.continuous.integrable_of_hasCompactSupport
      (hc2.fderiv_apply (𝕜 := ℝ) (0,1))),
    integral_compact_partial_fst h1 hc1,integral_compact_partial_snd h2 hc2,sub_self]

theorem HasCompactSupport.comp_radiusSq {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z : Plane => g (radiusSq z)) := by
  obtain ⟨B,hB,hbound⟩ := hg.isBounded.exists_pos_norm_le
  apply HasCompactSupport.intro ((isCompact_Icc : IsCompact (Icc (-(B+1)) (B+1))).prod (isCompact_Icc : IsCompact (Icc (-(B+1)) (B+1))))
  intro z hz
  by_contra hg0
  have hb := hbound (radiusSq z) (subset_tsupport g hg0)
  have hq : 0 ≤ radiusSq z := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hq] at hb
  apply hz
  dsimp only [radiusSq] at hb
  constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2]

theorem HasCompactSupport.comp_square {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun x : ℝ => g (x^2)) := by
  simpa only [radiusSq,zero_pow (by decide : (2:ℕ)≠0),add_zero] using
    HasCompactSupport.left_slice (HasCompactSupport.comp_radiusSq hg) 0

theorem integral_radial_derivative {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : (∫ z : Plane,2*deriv g (radiusSq z))= -2*Real.pi*g 0 := by
  let h : ℝ → ℝ := fun r => g (r^2)
  have hh : ContDiff ℝ ∞ h := hg.comp (contDiff_id.pow 2)
  have hhC : HasCompactSupport h := HasCompactSupport.comp_square hc
  have hd (r : ℝ) : deriv h r=2*r*deriv g (r^2) := by
    have H := (hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (r^2)).hasDerivAt.comp r ((hasDerivAt_id r).pow 2)
    change HasDerivAt h _ r at H
    rw [H.deriv]
    simp only [Nat.cast_ofNat,mul_one,id_eq]
    norm_num
    ring
  rw [← integral_comp_polarCoord_symm]
  have he : (fun p : Plane => p.1 • (2*deriv g (radiusSq (polarCoord.symm p))))=
      (fun p : Plane => deriv h p.1 * (1 : ℝ)) := by
    funext p
    rw [radiusSq_polar,hd]
    simp only [smul_eq_mul]
    ring
  rw [he,polarCoord_target,Measure.volume_eq_prod,setIntegral_prod_mul (deriv h) (fun _ : ℝ => (1 : ℝ)),
    HasCompactSupport.integral_Ioi_deriv_eq (hh.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hhC]
  simp only [h,zero_pow (by decide : (2:ℕ)≠0),integral_const,smul_eq_mul,
    Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0≤Real.pi-(-Real.pi))]
  ring

theorem radiusSq_hasFDerivAt (z : Plane) :
    HasFDerivAt radiusSq ((2:ℝ) • planarDot z) z := by
  have H := (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2).add
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2)
  change HasFDerivAt radiusSq _ z at H
  apply H.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change (2 • z.1^(2-1))*v.1+(2 • z.2^(2-1))*v.2=2*(z.1*v.1+z.2*v.2)
  norm_num
  ring

theorem angularOneForm_contDiffAt {z : Plane} (hz : radiusSq z≠0) :
    ContDiffAt ℝ ∞ angularOneForm z :=
  (radiusSq_smooth.contDiffAt.inv hz).smul planarArea.contDiff.contDiffAt

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

theorem planarCurl_spatial_smul {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {z : Plane}
    (hf : DifferentiableAt ℝ f z) (hβ : DifferentiableAt ℝ β z) :
    planarCurl (fun y => f y • β y) z=cutoffWedge f β z+f z*planarCurl β z := by
  unfold planarCurl cutoffWedge
  have H := hf.hasFDerivAt.smul hβ.hasFDerivAt
  change HasFDerivAt (fun y => f y • β y) _ z at H
  rw [H.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
  ring

theorem integral_cutoffWedge {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    (∫ z,cutoffWedge f β z)= -(∫ z,f z*planarCurl β z) := by
  have hp : ContDiff ℝ ∞ (fun z => f z • β z) := hf.smul hβ
  have hpc : HasCompactSupport (fun z => f z • β z) := hc.smul_right
  have hci : Integrable (planarCurl (fun z => f z • β z)) := (planarCurl_contDiff hp).continuous.integrable_of_hasCompactSupport (planarCurl_compact hpc)
  have hgi : Integrable (fun z => f z*planarCurl β z) := (hf.mul (planarCurl_contDiff hβ)).continuous.integrable_of_hasCompactSupport hc.mul_right
  have he : cutoffWedge f β=(fun z => planarCurl (fun y => f y • β y) z-f z*planarCurl β z) := by
    funext z
    rw [planarCurl_spatial_smul (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z) (hβ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)]
    ring
  rw [he,integral_sub hci hgi,show (∫ z,planarCurl (fun y => f y • β y) z)=0 from compact_planar_stokes hp hpc,zero_sub]

theorem cutoffWedge_integrable {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    Integrable (cutoffWedge f β) := by
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (1,0)) := (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := ((1:ℝ),(0:ℝ))))
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (0,1)) := (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := ((0:ℝ),(1:ℝ))))
  exact ((h1.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (1,0)).mul_right).sub
    ((h2.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (0,1)).mul_right)

theorem integral_planar_residue_cutoff {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (h0 : g 0=1)
    (hβ : ContDiff ℝ ∞ β) (c : ℝ) :
    (∫ z : Plane,-cutoffWedge (fun y => g (radiusSq y)) β z+c*deriv g (radiusSq z))=
      (∫ z : Plane,g (radiusSq z)*planarCurl β z)-c*Real.pi := by
  have hgs : ContDiff ℝ ∞ (fun z : Plane => g (radiusSq z)) := hg.comp radiusSq_smooth
  have hgc := HasCompactSupport.comp_radiusSq hc
  have hdi : Integrable (fun z : Plane => deriv g (radiusSq z)) := ((hg.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.comp_radiusSq hc.deriv)
  have hni : Integrable (fun z : Plane => -cutoffWedge (fun y => g (radiusSq y)) β z) :=
    (cutoffWedge_integrable hgs hgc hβ).neg
  rw [integral_add hni (hdi.const_mul c),integral_neg,
    integral_cutoffWedge hgs hgc hβ,neg_neg,integral_const_mul]
  have hi := integral_radial_derivative hg hc
  rw [integral_const_mul,h0,mul_one] at hi
  have hid : (∫ z : Plane,deriv g (radiusSq z))= -Real.pi := by linarith
  rw [hid]
  ring

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_QuadricInfinityPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
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

theorem infinityRegularPrimitive_apply (c : ℝ) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈infinityRegion a) (v : Plane) :
    infinityRegularPrimitive a ε c y v=
      affineFSPrimitive c (affinePhase m (infinityRegularPoint a ε (Complex.equivRealProdCLM.symm y)))
        (affinePhase m (Complex.equivRealProdCLM.symm v,
          fderiv ℂ (infinityRoot a ε) (Complex.equivRealProdCLM.symm y) (Complex.equivRealProdCLM.symm v))) := by
  have hf := realPhaseDerivative_fderiv
    ((infinityRegularPoint_contDiffAt a ε hy).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hf
  change affineFSPrimitive c _ (fderiv ℝ (infinityRegularPhase a ε) y v)=_
  change fderiv ℝ (infinityRegularPhase a ε) y = _ at hf
  rw [hf]
  change affineFSPrimitive c _ (affinePhase m
    (fderiv ℂ (infinityRegularPoint a ε) (Complex.equivRealProdCLM.symm y)
      (Complex.equivRealProdCLM.symm v)))=_
  rw [infinityRegularPoint_fderiv a ε hy]
  rfl

variable [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem infinityPhase_germ {y : Plane}
    (hy : y∈(infinityDiffeomorph a ε).source) :
    (phaseInclusion a ∘ infinityDiffeomorph a ε)=ᶠ[𝓝 y]
      fun z => affinePhase m (infinityPoint a ε (Complex.equivRealProdCLM.symm z)) := by
  filter_upwards [(infinityDiffeomorph a ε).open_source.mem_nhds hy] with z hz
  have hzD : Complex.equivRealProdCLM.symm z∈infinityDomain a := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hz
  change affinePhase m ((infinityInverse a ε (Complex.equivRealProdCLM.symm z)).val)=_
  rw [infinityInverse_val a ε hzD.1]

theorem curveFSPrimitive_infinity (c : ℝ) {y : Plane}
    (hy : y∈(infinityDiffeomorph a ε).source) :
    euclideanPullbackOneForm (fun _ => curveFSPrimitive a c) (infinityDiffeomorph a ε) (0,y)=
      infinityRegularPrimitive a ε c y-(c/2) • angularOneForm y := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain a := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hg := infinityPhase_germ a ε hy
  have hd := realPhaseDerivative_fderiv
    ((infinityPoint_contDiffAt a ε hD).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hd
  change euclideanPullbackOneForm (fun _ => manifoldPullbackOneForm
    (fun _ => affineFSPrimitive c) (phaseInclusion a) 0) (infinityDiffeomorph a ε) (0,y)=_
  rw [euclideanPullbackOneForm_comp ((phaseInclusion_smooth a).mdifferentiable (by simp) _)
    ((infinityDiffeomorph a ε).mdifferentiableAt (by simp) hy)]
  apply ContinuousLinearMap.ext
  intro v
  change affineFSPrimitive c ((phaseInclusion a ∘ infinityDiffeomorph a ε) y)
    (manifoldMapDifferential (E := PlanePhase (Option (Fin m))) (F := Plane)
      (phaseInclusion a ∘ infinityDiffeomorph a ε) y v)=_
  rw [manifoldMapDifferential,mfderiv_eq_fderiv,hg.eq_of_nhds,hg.fderiv_eq,hd]
  change affineFSPrimitive c (affinePhase m (infinityPoint a ε (Complex.equivRealProdCLM.symm y)))
    (affinePhase m (fderiv ℂ (infinityPoint a ε) (Complex.equivRealProdCLM.symm y)
      (Complex.equivRealProdCLM.symm v)))=_
  rw [infinityPoint_fderiv a ε hD]
  have hp : infinityPoint a ε (Complex.equivRealProdCLM.symm y)=
      ((Complex.equivRealProdCLM.symm y)⁻¹,fun j =>
        infinityRoot a ε (Complex.equivRealProdCLM.symm y) j/(Complex.equivRealProdCLM.symm y)) := by
    simp only [infinityPoint,div_eq_mul_inv,mul_comm]
  rw [hp,affineFSPrimitive_projective_swap c hD.1]
  rw [sub_apply,smul_apply,infinityRegularPrimitive_apply a ε c hD.2]
  have hns : Complex.normSq (Complex.equivRealProdCLM.symm y)=radiusSq y := by
    change y.1*y.1+y.2*y.2=y.1^2+y.2^2
    ring
  have hca : complexArea (Complex.equivRealProdCLM.symm y) (Complex.equivRealProdCLM.symm v)=planarArea y v := by
    rw [complexArea_apply]
    rfl
  simp only [hns,hca,angularOneForm,smul_apply,smul_eq_mul,infinityRegularPoint]
  ring

end PackingSufficiencySupport.DiagonalQuadrics

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

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem manifoldExteriorOneForm_congr_of_eventuallyEq {α β : ManifoldOneForm E M}
    {x : M} (he : α =ᶠ[𝓝 x] β) : manifoldExteriorOneForm α x=manifoldExteriorOneForm β x := by
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) x).source := mem_extChartAt_source x
  have hxt := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) x).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hxt)).continuousAt
  have hh : chartOneForm α x =ᶠ[𝓝 (extChartAt 𝓘(ℝ,E) x x)] chartOneForm β x := by
    have he' : α =ᶠ[𝓝 ((extChartAt 𝓘(ℝ,E) x).symm (extChartAt 𝓘(ℝ,E) x x))] β := by
      rw [(extChartAt 𝓘(ℝ,E) x).left_inv hx]
      exact he
    have hn := he'.comp_tendsto hi
    filter_upwards [hn] with y hy
    simp only [chartOneForm]
    change α ((extChartAt 𝓘(ℝ,E) x).symm y)=β ((extChartAt 𝓘(ℝ,E) x).symm y) at hy
    rw [hy]
  unfold manifoldExteriorOneForm euclideanExteriorOneForm
  rw [hh.fderiv_eq]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldExteriorAlgebra
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
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

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_smul (a : ℝ) {α : ManifoldOneForm E M}
    (hα : ∀ c,ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (x : M) : manifoldExteriorOneForm (a • α) x=a • manifoldExteriorOneForm α x := by
  have hx : extChartAt 𝓘(ℝ,E) x x∈(extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x)
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hx
  have he : chartOneForm (a • α) x=a • chartOneForm α x := funext (chartOneForm_smul a α x)
  simp only [manifoldExteriorOneForm,he,euclideanExteriorOneForm_smul a
    ((hα x).contDiffAt hn |>.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  rfl


end


open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_zero (x : M) :
    manifoldExteriorOneForm (0 : ManifoldOneForm E M) x=0 := by
  unfold manifoldExteriorOneForm
  have hz : chartOneForm (0 : ManifoldOneForm E M) x = fun _ => 0 :=
    funext fun y => chartOneForm_zero x y
  simp only [hz,euclideanExteriorOneForm,fderiv_const_apply,
    ContinuousLinearMap.flip_zero]
  ext u v
  change (0 : ℝ)-0=0
  ring



end PackingSufficiencySupport.Hamiltonian
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
-- module Solutions.OAIQ240_BP.BallPacking_Projective_AnnularChartHelpers
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
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

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
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

theorem manifoldExteriorOneForm_sum {I : Type*} (s : Finset I)
    {α : I → P → ManifoldOneForm E M} (hα : ∀ i ∈ s, SmoothOneFormFamily (α i))
    (p : P) (x : M) :
    manifoldExteriorOneForm (∑ i ∈ s,α i p) x =
      ∑ i ∈ s,manifoldExteriorOneForm (α i p) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,manifoldExteriorOneForm_zero]
  | @insert i s hi ih =>
    have hx : extChartAt 𝓘(ℝ,E) x x ∈ (extChartAt 𝓘(ℝ,E) x).target :=
      (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x)
    have hs := fun j hj => hα j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    rw [manifoldExteriorOneForm_add_at
      ((hα i (Finset.mem_insert_self i s)).spatial_smooth p x hx)
      ((SmoothOneFormFamily.sum s hs).spatial_smooth p x hx), ih hs]

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

 omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem manifoldExteriorOneForm_zero_off [IsManifold 𝓘(ℝ,E) ∞ M]
    {L : Set M} (hL : IsClosed L) {α : ManifoldOneForm E M}
    (hz : ∀ x,x∉L→α x=0) {x : M} (hx : x∉L) : manifoldExteriorOneForm α x=0 := by
  have he : α =ᶠ[𝓝 x] (0 : ManifoldOneForm E M) := by
    filter_upwards [hL.isOpen_compl.mem_nhds hx] with y hy
    exact hz y hy
  rw [manifoldExteriorOneForm_congr_of_eventuallyEq he,manifoldExteriorOneForm_zero]

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

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialFamilyExtension
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
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
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem partialChartCoefficient_exterior
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    {α : ManifoldOneForm Plane M} (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    {y : Plane} (hy : y∈e.source) :
    partialChartCoefficient e (manifoldExteriorOneForm α) y=
      planarCurl (fun z => euclideanPullbackOneForm (fun _ => α) e (0,z)) y := by
  have hs := euclidean_manifold_pullback_exterior_at
    (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hy))
    (by
      have hv := (hα (e y)).contDiffAt
        ((isOpen_univ.prod (isOpen_extChartAt_target (e y))).mem_nhds
          (show (0,extChartAt 𝓘(ℝ,Plane) (e y) (e y))∈(univ : Set ℝ)×ˢ(extChartAt 𝓘(ℝ,Plane) (e y)).target from
            ⟨mem_univ _,mem_extChartAt_target (e y)⟩))
      exact hv.comp _ (contDiffAt_const.prodMk contDiffAt_id))
  change ((manifoldExteriorOneForm α (e y)).bilinearComp
    (manifoldMapDifferential (E := Plane) (F := Plane) e y)
    (manifoldMapDifferential (E := Plane) (F := Plane) e y)) (1,0) (0,1)=_
  exact congrArg (fun L : Plane →L[ℝ] Plane →L[ℝ] ℝ => L (1,0) (0,1)) hs.symm

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem euclideanPullbackOneForm_spatial_smul (ρ : M → ℝ)
    (α : ManifoldOneForm Plane M) (e : Plane → M) (y : Plane) :
    euclideanPullbackOneForm (fun _ => fun x => ρ x • α x) e (0,y)=
      ρ (e y) • euclideanPullbackOneForm (fun _ => α) e (0,y) := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem partialChartCoefficient_sub
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    (Ω Λ : ManifoldTwoForm Plane M) (y : Plane) :
    partialChartCoefficient e (Ω-Λ) y=partialChartCoefficient e Ω y-partialChartCoefficient e Λ y := rfl

end

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

theorem curveEndAnnulus_subset_target {r R : ℝ} (hr : 0 < r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) (ε : Fin m → Bool) :
    curveEndAnnulus a ε r R⊆(infinityDiffeomorph a ε).target := by
  rintro x ⟨y,hy,rfl⟩
  exact (infinityDiffeomorph a ε).map_source (radialAnnulus_in_end a hr hR ε hy)

theorem endAnnulus_cover {r R : ℝ} (_hr : 0 < r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) {x : locus a}
    (hx : curveProjection a x≠0)
    (hb : Complex.normSq (curveProjection a x)⁻¹∈Icc r R) :
    x∈⋃ ε : Fin m → Bool,curveEndAnnulus a ε r R := by
  obtain ⟨ε,hε⟩ := exists_infinityBranch a hx (hR hb.2)
  apply mem_iUnion.mpr
  refine ⟨ε,(infinityDiffeomorph a ε).symm x,?_,?_⟩
  · change r ≤ radiusSq (Complex.equivRealProdCLM (curveProjection a x)⁻¹) ∧
      radiusSq (Complex.equivRealProdCLM (curveProjection a x)⁻¹)≤R
    rw [← radiusSq_complex,ContinuousLinearEquiv.symm_apply_apply]
    exact hb
  · exact (infinityDiffeomorph a ε).right_inv (by simpa only [infinityDiffeomorph_target] using hε)

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem curveEndCutoff_punctured_germ (g : ℝ → ℝ) {x : locus a}
    (hx : curveProjection a x≠0) :
    curveEndCutoff a g=ᶠ[𝓝 x] fun y => 1-g (Complex.normSq (curveProjection a y)⁻¹) := by
  have hn : ∀ᶠ y in 𝓝 x,curveProjection a y≠0 :=
    (isOpen_ne_fun (curveProjection_continuous a) continuous_const).mem_nhds hx
  filter_upwards [hn] with y hy
  exact ite_eq_right hy

theorem curveEndCutoff_locally_constant_off_annuli {g : ℝ → ℝ} {r R : ℝ}
    (hc : HasCompactSupport g) (hr : 0 < r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    {x : locus a} (hx : x∉⋃ ε : Fin m → Bool,curveEndAnnulus a ε r R) :
    ∃ c : ℝ,curveEndCutoff a g=ᶠ[𝓝 x] fun _ => c := by
  by_cases ht : curveProjection a x=0
  · refine ⟨1,?_⟩
    have hi := inverseComplementCutoff_one_near_zero (HasCompactSupport.comp_complex_normSq hc)
    have hp : Tendsto (curveProjection a) (𝓝 x) (𝓝 0) := by
      have hp := (curveProjection_continuous a).continuousAt (x := x)
      change Tendsto (curveProjection a) (𝓝 x) (𝓝 (curveProjection a x)) at hp
      rwa [ht] at hp
    exact hi.comp_tendsto hp
  · have hinv : ContinuousAt (fun y => Complex.normSq (curveProjection a y)⁻¹) x :=
      complex_normSq_smooth.continuous.continuousAt.comp
        ((curveProjection_continuous a).continuousAt.inv₀ ht)
    have hnot : Complex.normSq (curveProjection a x)⁻¹∉Icc r R :=
      fun hb => hx (endAnnulus_cover a hr hR ht hb)
    rcases not_and_or.mp hnot with hlow|hhigh
    · have hl : Complex.normSq (curveProjection a x)⁻¹∈Ioo (-r) r :=
        ⟨lt_of_lt_of_le (neg_neg_of_pos hr) (Complex.normSq_nonneg _),lt_of_not_ge hlow⟩
      have he : ∀ᶠ y in 𝓝 x,Complex.normSq (curveProjection a y)⁻¹∈Ioo (-r) r :=
        hinv (isOpen_Ioo.mem_nhds hl)
      refine ⟨0,?_⟩
      filter_upwards [curveEndCutoff_punctured_germ a g ht,he] with y hy he
      rw [hy,h1 _ he,sub_self]
    · have he : ∀ᶠ y in 𝓝 x,R<Complex.normSq (curveProjection a y)⁻¹ :=
        hinv (isOpen_Ioi.mem_nhds (lt_of_not_ge hhigh))
      refine ⟨1,?_⟩
      filter_upwards [curveEndCutoff_punctured_germ a g ht,he] with y hy he
      rw [hy,image_eq_zero_of_notMem_tsupport (fun hh => not_le_of_gt he (h0 hh)),sub_zero]

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

 theorem chartMass_exterior_eq_zero {c : M} {K : Set M}
    (hK : IsCompact K) (hKc : K⊆(extChartAt 𝓘(ℝ,Plane) c).source)
    {α : ManifoldOneForm Plane M} (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (hz : ∀ x,x∉K→α x=0) : chartMass c (manifoldExteriorOneForm α)=0 := by
  classical
  let e := extChartAt 𝓘(ℝ,Plane) c
  let L := e '' K
  have hL : IsCompact L := hK.image_of_continuousOn
    ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) c).mono hKc)
  have hLt : L⊆e.target := by
    rintro y ⟨x,hx,rfl⟩
    exact e.map_source (hKc hx)
  have hcz (p : ℝ) (y : Plane) (hy : y∈e.target) (hn : y∉L) :
      chartOneForm α c y=0 := by
    have hx : e.symm y∉K := fun hk => hn ⟨_,hk,e.right_inv hy⟩
    change (α (e.symm y)).comp (chartDifferential c (e.symm y)).inverse=0
    rw [hz _ hx,ContinuousLinearMap.zero_comp]
  let β : Plane → Plane →L[ℝ] ℝ := fun y =>
    spatialZeroExtension e.target (fun q : ℝ × Plane => chartOneForm α c q.2) (0,y)
  have hβs : ContDiff ℝ ∞ β := by
    exact (spatialZeroExtension_smooth (isOpen_extChartAt_target c) hL.isClosed hLt
      (hα c) hcz).comp (contDiff_const.prodMk contDiff_id)
  have hβz (y : Plane) (hy : y∉L) : β y=0 := spatialZeroExtension_zero hcz 0 hy
  have hβc : HasCompactSupport β := HasCompactSupport.intro hL hβz
  have he (y : Plane) : extendedChartCoefficient c (fun _ : ℝ => manifoldExteriorOneForm α) (0,y)=
      fderiv ℝ β y (1,0) (0,1)-fderiv ℝ β y (0,1) (1,0) := by
    by_cases hy : y∈e.target
    · have hg : β =ᶠ[𝓝 y] chartOneForm α c := by
        filter_upwards [(isOpen_extChartAt_target c).mem_nhds hy] with z hz
        exact ite_eq_left hz
      change (if y∈e.target then chartTwoForm (manifoldExteriorOneForm α) c y (1,0) (0,1) else 0)=_
      rw [ite_eq_left hy,manifoldExteriorOneForm_chart
        (fun b z hz => (hα.spatial_smooth 0 b hz).contDiffWithinAt) hy,hg.fderiv_eq]
      rfl
    · have hn : y∉L := fun hyL => hy (hLt hyL)
      have hg : β =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hL.isClosed.isOpen_compl.mem_nhds hn] with z hz
        exact hβz z hz
      change (if y∈e.target then chartTwoForm (manifoldExteriorOneForm α) c y (1,0) (0,1) else 0)=_
      rw [ite_eq_right hy,hg.fderiv_eq]
      simp only [fderiv_const_apply,zero_apply,sub_self]
  unfold chartMass
  simp_rw [he]
  exact compact_planar_stokes hβs hβc

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfacePrimitiveOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory
open scoped ContDiff Manifold Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem smoothSupportedTwoForms.skew {K : Set M} (Ω : smoothSupportedTwoForms (E := E) K)
    (x : M) (u v : E) : (Ω : ManifoldTwoForm E M) x u v = -(Ω : ManifoldTwoForm E M) x v u :=
  Ω.property.2.1 x u v

end

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

 theorem partitionFormMass_eq_chartMass {I : Type*} [Fintype I] {K L : Set M}
    (hor : PositivePlaneTransitions M) (hL : IsCompact L) (hLK : L⊆K)
    (c : M) (hLc : L⊆(extChartAt 𝓘(ℝ,Plane) c).source)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) (hz : ∀ x,x∉L→Ω x=0) :
    partitionFormMass B ρ Ω=chartMass c Ω := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let D : I → ManifoldTwoForm Plane M := fun i x => ρ i x • Ω x
  let C : I → Set M := fun i => L∩tsupport (ρ i)
  have hC (i : I) : IsCompact (C i) := hL.inter_right (isClosed_tsupport (ρ i))
  have hCB (i : I) : C i⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.2).1
  have hCc (i : I) : C i⊆(extChartAt 𝓘(ℝ,Plane) c).source := fun _ hx => hLc hx.1
  have hDs (i : I) : SmoothTwoForm (D i) :=
    ((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ρ i).contMDiff).eval 0
  have hDa (i : I) (x : M) (u v : Plane) : D i x u v= -D i x v u := by
    change ρ i x * Ω x u v= -(ρ i x * Ω x v u)
    rw [ha x u v,mul_neg]
  have hDz (i : I) (x : M) (hx : x∉C i) : D i x=0 := by
    by_cases hk : x∈L
    · have hi : x∉tsupport (ρ i) := fun hi => hx ⟨hk,hi⟩
      simp only [D,image_eq_zero_of_notMem_tsupport hi,zero_smul]
    · simp only [D,hz x hk,smul_zero]
  have hsum : (∑ i,D i)=Ω := by
    funext x
    simp only [Finset.sum_apply,D,← Finset.sum_smul]
    by_cases hx : x∈L
    · have hs : (∑ i,ρ i x)=1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (hLK hx)
      rw [hs,one_smul]
    · rw [hz x hx]
      apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      exact mul_zero _
  have hc (i : I) : chartMass (B i).center (D i)=chartMass c (D i) := by
    apply chartMass_change (hDa i) (hC i) (hCB i) (hCc i) (hDz i)
    rintro y ⟨x,hx,rfl⟩
    apply hor (B i).center c _ ((extChartAt 𝓘(ℝ,Plane) (B i).center).map_source (hCB i hx))
    simpa only [(extChartAt 𝓘(ℝ,Plane) (B i).center).left_inv (hCB i hx)] using hCc i hx
  change (∑ i,chartMass (B i).center (D i))=_
  simp_rw [hc]
  rw [← chartMass_sum Finset.univ c D
    (fun i _ => (hDs i).coefficient_integrable c (hC i) (hCc i) (hDz i)),hsum]

end

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

 theorem partitionFormMass_compact_stokes {I : Type*} [Fintype I] {K : Set M}
    (hor : PositivePlaneTransitions M) (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {α : ManifoldOneForm Plane M} (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (hz : ∀ x,x∉K→α x=0) : partitionFormMass B ρ (manifoldExteriorOneForm α)=0 := by
  classical
  let β : I → ManifoldOneForm Plane M := fun i x => ρ i x • α x
  let L : I → Set M := fun i => K∩tsupport (ρ i)
  have hL (i : I) : IsCompact (L i) := hK.inter_right (isClosed_tsupport (ρ i))
  have hLB (i : I) : L i⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.2).1
  have hβs (i : I) : SmoothOneFormFamily (fun _ : ℝ => β i) := hα.spatial_smul (ρ i).contMDiff
  have hβz (i : I) (x : M) (hx : x∉L i) : β i x=0 := by
    change ρ i x • α x=0
    by_cases hk : x∈K
    · rw [image_eq_zero_of_notMem_tsupport (fun hi => hx ⟨hk,hi⟩),zero_smul]
    · rw [hz x hk,smul_zero]
  have hdz (i : I) (x : M) (hx : x∉L i) : manifoldExteriorOneForm (β i) x=0 :=
    manifoldExteriorOneForm_zero_off (hL i).isClosed (hβz i) hx
  have hsum : (∑ i,β i)=α := by
    funext x
    simp only [Finset.sum_apply,β,← Finset.sum_smul]
    by_cases hx : x∈K
    · have hs : (∑ i,ρ i x)=1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hs,one_smul]
    · rw [hz x hx,smul_zero]
  let D : I → smoothSupportedTwoForms (E := Plane) K := fun i =>
    ⟨manifoldExteriorOneForm (β i),
      (manifoldExteriorOneForm_family_smooth (hβs i)).eval 0,
      manifoldExteriorOneForm_skew (β i),fun x hx => hdz i x (fun hi => hx hi.1)⟩
  have hdSum : ((∑ i,D i : smoothSupportedTwoForms (E := Plane) K) : ManifoldTwoForm Plane M)=
      manifoldExteriorOneForm α := by
    funext x
    simp only [Submodule.coe_sum,Finset.sum_apply]
    change (∑ i,manifoldExteriorOneForm (β i) x)=manifoldExteriorOneForm α x
    rw [← manifoldExteriorOneForm_sum Finset.univ (fun i _ => hβs i) (0 : ℝ),hsum]
  have hmass (i : I) : surfaceIntegralLinearMap hK B ρ hρ (D i)=0 := by
    change partitionFormMass B ρ (manifoldExteriorOneForm (β i))=0
    rw [partitionFormMass_eq_chartMass hor (hL i) inter_subset_left
      (B i).center (hLB i) B ρ hρ ((manifoldExteriorOneForm_family_smooth (hβs i)).eval 0)
      (manifoldExteriorOneForm_skew (β i)) (hdz i)]
    exact chartMass_exterior_eq_zero (hL i) (hLB i) (hβs i) (hβz i)
  rw [← hdSum]
  change surfaceIntegralLinearMap hK B ρ hρ (∑ i,D i)=0
  rw [map_sum]
  simp only [hmass,Finset.sum_const_zero]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfaceCutoffDefect
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem spatialCutoffDefect_smooth {κ : M → ℝ} {α : ManifoldOneForm Plane M}
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ) (hα : SmoothOneFormFamily (fun _ : ℝ => α)) :
    SmoothTwoForm (spatialCutoffDefect κ α) :=
  ((manifoldExteriorOneForm_family_smooth (hα.spatial_smul hκ)).sub
    ((manifoldExteriorOneForm_family_smooth hα).spatial_smul hκ)).eval 0

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem spatialCutoffDefect_skew (κ : M → ℝ) (α : ManifoldOneForm Plane M)
    (x : M) (u v : Plane) : spatialCutoffDefect κ α x u v= -spatialCutoffDefect κ α x v u := by
  change manifoldExteriorOneForm (fun x => κ x • α x) x u v-
    κ x*manifoldExteriorOneForm α x u v= -(manifoldExteriorOneForm (fun x => κ x • α x) x v u-
    κ x*manifoldExteriorOneForm α x v u)
  rw [manifoldExteriorOneForm_skew (fun x => κ x • α x) x u v,
    manifoldExteriorOneForm_skew α x u v]
  ring

theorem spatialCutoffDefect_zero_of_locally_constant {κ : M → ℝ} {α : ManifoldOneForm Plane M}
    (hα : SmoothOneFormFamily (fun _ : ℝ => α)) {x : M} {c : ℝ}
    (he : κ=ᶠ[𝓝 x] fun _ => c) : spatialCutoffDefect κ α x=0 := by
  have hform : (fun y => κ y • α y)=ᶠ[𝓝 x] c • α := by
    filter_upwards [he] with y hy
    change κ y • α y=c • α y
    rw [hy]
  have hc : κ x=c := he.eq_of_nhds
  unfold spatialCutoffDefect
  rw [Pi.sub_apply,manifoldExteriorOneForm_congr_of_eventuallyEq hform,
    manifoldExteriorOneForm_smul c (fun b y hy => (hα.spatial_smooth 0 b hy).contDiffWithinAt),hc]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change c*manifoldExteriorOneForm α x u v-c*manifoldExteriorOneForm α x u v=0
  ring

theorem spatialCutoffDefect_coefficient
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    {κ : M → ℝ} {α : ManifoldOneForm Plane M}
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ) (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    {y : Plane} (hy : y∈e.source) :
    partialChartCoefficient e (spatialCutoffDefect κ α) y=
      planarCurl (fun z => κ (e z) • euclideanPullbackOneForm (fun _ => α) e (0,z)) y-
        κ (e y)*planarCurl (fun z => euclideanPullbackOneForm (fun _ => α) e (0,z)) y := by
  unfold spatialCutoffDefect
  rw [partialChartCoefficient_sub,
    partialChartCoefficient_exterior e (hα.spatial_smul hκ) hy]
  have he : (fun z => euclideanPullbackOneForm (fun _ => fun x => κ x • α x) e (0,z))=
      (fun z => κ (e z) • euclideanPullbackOneForm (fun _ => α) e (0,z)) :=
    funext (euclideanPullbackOneForm_spatial_smul κ α e)
  rw [he]
  congr 1
  change κ (e y)*partialChartCoefficient e (manifoldExteriorOneForm α) y=_
  rw [partialChartCoefficient_exterior e hα hy]

end

theorem cutoffWedge_radial_angular {g : ℝ → ℝ} {z : Plane}
    (hg : DifferentiableAt ℝ g (radiusSq z)) (hz : radiusSq z≠0) :
    cutoffWedge (fun y => g (radiusSq y)) angularOneForm z=2*deriv g (radiusSq z) := by
  have hd := (hg.hasDerivAt.comp_hasFDerivAt z (radiusSq_hasFDerivAt z)).fderiv
  change fderiv ℝ (fun y => g (radiusSq y)) z=_ at hd
  unfold cutoffWedge
  rw [hd]
  simp only [smul_apply,smul_eq_mul,planarDot_apply,angularOneForm,
    planarArea_apply]
  unfold radiusSq at hz ⊢
  field_simp
  ring

theorem planar_residue_defect {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (hg : DifferentiableAt ℝ g (radiusSq z)) (hβ : DifferentiableAt ℝ β z)
    (hz : radiusSq z≠0) (c : ℝ) :
    planarCurl (fun y => (1-g (radiusSq y)) • (β y-(c/2) • angularOneForm y)) z-
      (1-g (radiusSq z))*planarCurl (fun y => β y-(c/2) • angularOneForm y) z=
      -cutoffWedge (fun y => g (radiusSq y)) β z+c*deriv g (radiusSq z) := by
  have hgs := hg.comp z (radiusSq_hasFDerivAt z).differentiableAt
  have hrs := (differentiableAt_const (c := (1:ℝ))).sub hgs
  have hbs := hβ.sub ((angularOneForm_contDiffAt hz).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.const_smul (c/2))
  change DifferentiableAt ℝ (fun y => 1-g (radiusSq y)) z at hrs
  change DifferentiableAt ℝ (fun y => β y-(c/2) • angularOneForm y) z at hbs
  change DifferentiableAt ℝ (fun y => g (radiusSq y)) z at hgs
  rw [planarCurl_spatial_smul hrs hbs,add_sub_cancel_right]
  have hd := (hasFDerivAt_const (1:ℝ) z).sub hgs.hasFDerivAt
  change HasFDerivAt (fun y => 1-g (radiusSq y)) _ z at hd
  have he : cutoffWedge (fun y => 1-g (radiusSq y)) (fun y => β y-(c/2) • angularOneForm y) z=
      -cutoffWedge (fun y => g (radiusSq y)) β z+(c/2)*cutoffWedge (fun y => g (radiusSq y)) angularOneForm z := by
    unfold cutoffWedge
    rw [hd.fderiv]
    simp only [sub_apply,zero_apply,smul_apply,smul_eq_mul]
    ring
  rw [he,cutoffWedge_radial_angular hg hz]
  ring

theorem planarCurl_congr_of_eventuallyEq {α β : Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (he : α=ᶠ[𝓝 z] β) : planarCurl α z=planarCurl β z := by
  unfold planarCurl
  rw [he.fderiv_eq]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem curveCutoffDefect_zero_off_annuli {g : ℝ → ℝ} {r R : ℝ}
    (hc : HasCompactSupport g) (hr : 0 < r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R) (c : ℝ)
    {x : locus a} (hx : x∉⋃ ε : Fin m → Bool,curveEndAnnulus a ε r R) :
    spatialCutoffDefect (curveEndCutoff a g) (curveFSPrimitive a c) x=0 := by
  obtain ⟨b,hb⟩ := curveEndCutoff_locally_constant_off_annuli a hc hr hR h1 h0 hx
  exact spatialCutoffDefect_zero_of_locally_constant (curveFSPrimitive_smooth a c) hb

theorem curveCutoffDefect_end_coefficient {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (ε : Fin m → Bool) (c : ℝ)
    {β : Plane → Plane →L[ℝ] ℝ} {y : Plane}
    (hy : y∈(infinityDiffeomorph a ε).source)
    (he : β=ᶠ[𝓝 y] infinityRegularPrimitive a ε c) :
    partialChartCoefficient (infinityDiffeomorph a ε)
      (spatialCutoffDefect (curveEndCutoff a g) (curveFSPrimitive a c)) y=
      -cutoffWedge (fun z => g (radiusSq z)) β y+c*deriv g (radiusSq y) := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain a := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hz : radiusSq y≠0 := by
    rw [← radiusSq_complex]
    exact ne_of_gt (Complex.normSq_pos.mpr hD.1)
  have hβ : DifferentiableAt ℝ β y :=
    ((infinityRegularPrimitive_contDiffAt a ε c hD.2).congr_of_eventuallyEq he).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hα : (fun z => euclideanPullbackOneForm (fun _ => curveFSPrimitive a c)
      (infinityDiffeomorph a ε) (0,z))=ᶠ[𝓝 y] fun z => β z-(c/2) • angularOneForm z := by
    filter_upwards [(infinityDiffeomorph a ε).open_source.mem_nhds hy,he] with z hz hez
    rw [curveFSPrimitive_infinity a ε c hz,hez]
  have hκα : (fun z => curveEndCutoff a g (infinityDiffeomorph a ε z) •
      euclideanPullbackOneForm (fun _ => curveFSPrimitive a c) (infinityDiffeomorph a ε) (0,z))=ᶠ[𝓝 y]
        fun z => (1-g (radiusSq z)) • (β z-(c/2) • angularOneForm z) := by
    filter_upwards [(infinityDiffeomorph a ε).open_source.mem_nhds hy,hα] with z hz haz
    rw [curveEndCutoff_infinity a g ε hz,haz]
  rw [spatialCutoffDefect_coefficient _ (curveEndCutoff_smooth a hg hc)
    (curveFSPrimitive_smooth a c) hy,planarCurl_congr_of_eventuallyEq hκα,
    planarCurl_congr_of_eventuallyEq hα,curveEndCutoff_infinity a g ε hy]
  exact planar_residue_defect (hg.differentiable (by simp) _) hβ hz c

end

variable {m : ℕ} (a : Fin m → ℂ)

theorem regular_extension_germ {R : ℝ} {ε : Fin m → Bool} {c : ℝ}
    {β : Plane → Plane →L[ℝ] ℝ}
    (he : β=ᶠ[𝓝ˢ (radialAnnulus 0 R)] infinityRegularPrimitive a ε c)
    {z : Plane} (hz : radiusSq z≤R) : β=ᶠ[𝓝 z] infinityRegularPrimitive a ε c :=
  he.filter_mono (nhds_le_nhdsSet ⟨radiusSq_nonneg z,hz⟩)

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Filter
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem partitionFormMass_eq_partialChart_supported_integral
    {I : Type*} [Fintype I] {K S : Set M}
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    (hpos : PositivePartialChart e) (hS : IsCompact S) (hSK : S⊆K) (hSe : S⊆e.target)
    (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) (hz : ∀ x,x∉S→Ω x=0) :
    partitionFormMass B ρ Ω=∫ y in e.symm '' S,partialChartCoefficient e Ω y := by
  classical
  let D : I → ManifoldTwoForm Plane M := fun i x => ρ i x • Ω x
  let L : I → Set M := fun i => S∩tsupport (ρ i)
  have hL (i : I) : IsCompact (L i) := hS.inter_right (isClosed_tsupport (ρ i))
  have hLB (i : I) : L i⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.2).1
  have hLe (i : I) : L i⊆e.target := fun _ hx => hSe hx.1
  have hDs (i : I) : SmoothTwoForm (D i) :=
    ((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ρ i).contMDiff).eval 0
  have hDa (i : I) (x : M) (u v : Plane) : D i x u v= -D i x v u := by
    change ρ i x * Ω x u v= -(ρ i x * Ω x v u)
    rw [ha x u v,mul_neg]
  have hDz (i : I) (x : M) (hx : x∉L i) : D i x=0 := by
    by_cases hk : x∈S
    · have hi : x∉tsupport (ρ i) := fun hi => hx ⟨hk,hi⟩
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change ρ i x * Ω x u v=0
      rw [image_eq_zero_of_notMem_tsupport hi,zero_mul]
    · apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change ρ i x * Ω x u v=0
      rw [hz x hk]
      simp
  have hCS : IsCompact (e.symm '' S) :=
    hS.image_of_continuousOn (e.symm.contMDiffOn.continuousOn.mono hSe)
  have hse : e.symm '' S⊆e.source := by
    rintro y ⟨x,hx,rfl⟩
    exact e.map_target (hSe hx)
  have hI (i : I) : IntegrableOn (partialChartCoefficient e (D i)) (e.symm '' S) :=
    ((partialChartCoefficient_contDiffOn e (hDs i)).continuousOn.mono hse).integrableOn_compact hCS
  have hmass (i : I) : chartMass (B i).center (D i)=
      ∫ y in e.symm '' S,partialChartCoefficient e (D i) y := by
    rw [chartMass_eq_partialChart_integral e (hDa i) (hL i) (hLe i) (hLB i) (hDz i)
      (by
        rintro y ⟨x,hx,rfl⟩
        apply hpos (B i).center _ (e.map_target (hLe i hx))
        have heq : e (e.symm x)=x := e.right_inv (hLe i hx)
        exact heq.symm ▸ hLB i hx)]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hCS.measurableSet
      (image_mono inter_subset_left)
    intro y hy
    have hyn : e y∉L i := by
      intro hyl
      exact hy.2 ⟨e y,hyl,e.left_inv (hse hy.1)⟩
    simp only [partialChartCoefficient,euclideanPullbackTwoForm,hDz i (e y) hyn]
    rfl
  change (∑ i,chartMass (B i).center (D i))=_
  simp_rw [hmass]
  rw [← integral_finsetSum Finset.univ (fun i _ => hI i)]
  apply setIntegral_congr_fun hCS.measurableSet
  intro y hy
  have hey : e y∈S := by
    obtain ⟨x,hx,rfl⟩ := hy
    have heq : e (e.symm x)=x := e.right_inv (hSe hx)
    rwa [heq]
  have hs : (∑ i,ρ i (e y))=1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (hSK hey)
  simp only [D,partialChartCoefficient_smul,← Finset.sum_mul,hs,one_mul]

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem SmoothTwoForm.indicator {U K : Set M} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K⊆U) {Ω : ManifoldTwoForm E M} (hΩ : SmoothTwoForm Ω)
    (hz : ∀ x,x∈U→x∉K→Ω x=0) : SmoothTwoForm (U.indicator Ω) := by
  classical
  intro c y hy
  let e := extChartAt 𝓘(ℝ,E) c
  let x := e.symm y
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hy)).continuousAt
  by_cases hx : x∈U
  · have hn := hi.preimage_mem_nhds (hU.mem_nhds hx)
    have he : chartTwoForm (U.indicator Ω) c=ᶠ[𝓝 y] chartTwoForm Ω c := by
      filter_upwards [hn] with z hz
      change ((U.indicator Ω) (e.symm z)).bilinearComp _ _=_
      rw [indicator_of_mem (show e.symm z∈U from hz)]
      rfl
    exact (((hΩ c).contDiffAt ((isOpen_extChartAt_target c).mem_nhds hy)).congr_of_eventuallyEq he).contDiffWithinAt
  · have hxK : x∉K := fun hk => hx (hKU hk)
    have hn := hi.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hxK)
    have he : chartTwoForm (U.indicator Ω) c=ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hn] with z hzk
      have hz0 : U.indicator Ω (e.symm z)=0 := by
        by_cases hzu : e.symm z∈U
        · rw [indicator_of_mem hzu,hz _ hzu hzk]
        · exact indicator_of_notMem hzu _
      change ((U.indicator Ω) (e.symm z)).bilinearComp _ _=0
      rw [hz0]
      ext u v
      rfl
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

 omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem indicator_twoForm_skew (U : Set M) {Ω : ManifoldTwoForm E M}
    (ha : ∀ x u v,Ω x u v= -Ω x v u) :
    ∀ x u v,(U.indicator Ω) x u v= -(U.indicator Ω) x v u := by
  classical
  intro x u v
  by_cases hx : x∈U
  · simpa only [indicator_of_mem hx] using ha x u v
  · simp only [indicator_of_notMem hx,zero_apply,neg_zero]

end
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

theorem partitionFormMass_finite_disjoint_charts
    {I J : Type*} [Fintype I] [Fintype J] {K : Set M} (hK : IsCompact K)
    (e : J → PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    (hpos : ∀ j,PositivePartialChart (e j))
    (hdisj : Pairwise fun i j => Disjoint (e i).target (e j).target)
    (S : J → Set M) (hS : ∀ j,IsCompact (S j))
    (hSK : ∀ j,S j⊆K) (hSe : ∀ j,S j⊆(e j).target)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) (hz : ∀ x,x∉⋃ j,S j→Ω x=0) :
    partitionFormMass B ρ Ω=∑ j,∫ y in (e j).symm '' S j,partialChartCoefficient (e j) Ω y := by
  classical
  have hzero (j : J) (x : M) (hx : x∈(e j).target) (hs : x∉S j) : Ω x=0 := by
    apply hz
    intro hall
    obtain ⟨i,hi⟩ := mem_iUnion.mp hall
    by_cases hij : i=j
    · exact hs (hij ▸ hi)
    · exact Set.disjoint_left.mp (hdisj hij) (hSe i hi) hx
  let D : J → smoothSupportedTwoForms (E := Plane) K := fun j =>
    ⟨(e j).target.indicator Ω,
      hΩ.indicator (e j).open_target (hS j).isClosed (hSe j) (hzero j),
      indicator_twoForm_skew _ ha,by
        intro x hx
        by_cases he : x∈(e j).target
        · rw [indicator_of_mem he]
          exact hzero j x he (fun hs => hx (hSK j hs))
        · exact indicator_of_notMem he _⟩
  have hDz (j : J) (x : M) (hx : x∉S j) : (D j : ManifoldTwoForm Plane M) x=0 := by
    change (e j).target.indicator Ω x=0
    by_cases he : x∈(e j).target
    · rw [indicator_of_mem he,hzero j x he hx]
    · exact indicator_of_notMem he _
  have hsum : ((∑ j,D j : smoothSupportedTwoForms (E := Plane) K) : ManifoldTwoForm Plane M)=Ω := by
    funext x
    simp only [Submodule.coe_sum,Finset.sum_apply]
    by_cases hex : ∃ j,x∈(e j).target
    · obtain ⟨j,hj⟩ := hex
      rw [Finset.sum_eq_single j]
      · exact indicator_of_mem hj _
      · intro i _ hij
        change (e i).target.indicator Ω x=0
        exact indicator_of_notMem (fun hi => Set.disjoint_left.mp (hdisj hij) hi hj) _
      · simp
    · have hx : ∀ j,x∉(e j).target := not_exists.mp hex
      have ho : Ω x=0 := hz x (by
        intro hall
        obtain ⟨j,hj⟩ := mem_iUnion.mp hall
        exact hx j (hSe j hj))
      rw [ho]
      apply Finset.sum_eq_zero
      intro j _
      exact indicator_of_notMem (hx j) _
  conv_lhs => rw [← hsum]
  change surfaceIntegralLinearMap hK B ρ hρ (∑ j,D j)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change partitionFormMass B ρ (D j : ManifoldTwoForm Plane M)=_
  rw [partitionFormMass_eq_partialChart_supported_integral (e j) (hpos j) (hS j)
    (hSK j) (hSe j) B ρ hρ (smoothSupportedTwoForms.smooth (D j))
    (smoothSupportedTwoForms.skew (D j)) (hDz j)]
  apply setIntegral_congr_fun ((hS j).image_of_continuousOn
    ((e j).symm.contMDiffOn.continuousOn.mono (hSe j))).measurableSet
  rintro y ⟨x,hx,rfl⟩
  have ht : e j ((e j).symm x)∈(e j).target :=
    (e j).map_source ((e j).map_target (hSe j hx))
  simp only [partialChartCoefficient,euclideanPullbackTwoForm,D,indicator_of_mem ht]

theorem partitionFormMass_cutoff_defect {I : Type*} [Fintype I] {K : Set M}
    (hor : PositivePlaneTransitions M) (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {κ : M → ℝ} {α : ManifoldOneForm Plane M}
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ) (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (hz : ∀ x,x∉K→κ x=0) :
    partitionFormMass B ρ (fun x => κ x • manifoldExteriorOneForm α x)=
      -partitionFormMass B ρ (spatialCutoffDefect κ α) := by
  have hκα : SmoothOneFormFamily (fun _ : ℝ => fun x => κ x • α x) := hα.spatial_smul hκ
  have hβ : SmoothTwoForm (fun x => κ x • manifoldExteriorOneForm α x) :=
    ((manifoldExteriorOneForm_family_smooth hα).spatial_smul hκ).eval 0
  have hzβ : ∀ x,x∉K→(fun x => κ x • manifoldExteriorOneForm α x) x=0 := by
    intro x hx
    change κ x • manifoldExteriorOneForm α x=0
    rw [hz x hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (0:ℝ)*manifoldExteriorOneForm α x u v=0
    exact zero_mul _
  have hzδ : ∀ x,x∉K→spatialCutoffDefect κ α x=0 := by
    intro x hx
    apply spatialCutoffDefect_zero_of_locally_constant hα
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hz y hy
  have he : spatialCutoffDefect κ α+(fun x => κ x • manifoldExteriorOneForm α x)=
      manifoldExteriorOneForm (fun x => κ x • α x) := by
    unfold spatialCutoffDefect
    exact sub_add_cancel (manifoldExteriorOneForm (fun x => κ x • α x))
      (fun x => κ x • manifoldExteriorOneForm α x)
  have hm := partitionFormMass_compact_stokes hor hK B ρ hρ hκα (by
    intro x hx
    rw [hz x hx,zero_smul])
  rw [←he,partitionFormMass_add hK B ρ hρ (spatialCutoffDefect_smooth hκ hα) hβ hzδ hzβ] at hm
  exact eq_neg_of_add_eq_zero_right hm

end

theorem radialCutoff_deriv_zero_off_annulus {g : ℝ → ℝ} {r R : ℝ}
    (hr : 0 < r) (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    {z : Plane} (hz : z∉radialAnnulus r R) : deriv g (radiusSq z)=0 := by
  change ¬(r ≤ radiusSq z ∧ radiusSq z≤R) at hz
  rcases not_and_or.mp hz with hl|hh
  · have he : g=ᶠ[𝓝 (radiusSq z)] fun _ => 1 := by
      filter_upwards [isOpen_Ioo.mem_nhds
        (show radiusSq z∈Ioo (-r) r from ⟨lt_of_lt_of_le (neg_neg_of_pos hr) (radiusSq_nonneg z),lt_of_not_ge hl⟩)] with t ht
      exact h1 t ht
    rw [he.deriv_eq,deriv_const]
  · have he : g=ᶠ[𝓝 (radiusSq z)] fun _ => 0 := by
      filter_upwards [isOpen_Ioi.mem_nhds (show R < radiusSq z from lt_of_not_ge hh)] with t ht
      exact image_eq_zero_of_notMem_tsupport (fun hs => not_le_of_gt (show R<t from ht) (show t≤R from h0 hs))
    rw [he.deriv_eq,deriv_const]

theorem planarResidueDensity_zero_off {g : ℝ → ℝ} {r R : ℝ}
    (hg : ContDiff ℝ ∞ g) (hr : 0 < r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (β : Plane → Plane →L[ℝ] ℝ) (c : ℝ) {z : Plane} (hz : z∉radialAnnulus r R) :
    -cutoffWedge (fun y => g (radiusSq y)) β z+c*deriv g (radiusSq z)=0 := by
  have hd := ((hg.differentiable (by simp) (radiusSq z)).hasDerivAt.comp_hasFDerivAt z
    (radiusSq_hasFDerivAt z)).fderiv
  change fderiv ℝ (fun y => g (radiusSq y)) z=_ at hd
  rw [radialCutoff_deriv_zero_off_annulus hr h1 h0 hz,zero_smul] at hd
  simp only [cutoffWedge,hd,zero_apply,zero_mul,sub_zero,neg_zero,
    radialCutoff_deriv_zero_off_annulus hr h1 h0 hz,mul_zero,add_zero]

theorem integral_planar_residue_annulus {g : ℝ → ℝ} {r R : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hr : 0 < r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) (c : ℝ) :
    (∫ z in radialAnnulus r R,-cutoffWedge (fun y => g (radiusSq y)) β z+c*deriv g (radiusSq z))=
      (∫ z : Plane,g (radiusSq z)*planarCurl β z)-c*Real.pi := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hz => planarResidueDensity_zero_off hg hr h1 h0 β c hz)]
  exact integral_planar_residue_cutoff hg hc (h1 0 ⟨neg_neg_of_pos hr,hr⟩) hβ c

end PackingSufficiencySupport.Hamiltonian
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

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem curveEndAnnulus_coordinates {r R : ℝ} (hr : 0 < r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) (ε : Fin m → Bool) :
    (infinityDiffeomorph a ε).symm '' curveEndAnnulus a ε r R=radialAnnulus r R :=
  (infinityDiffeomorph a ε).toPartialEquiv.symm_image_image_of_subset_source
    (radialAnnulus_in_end a hr hR ε)

theorem curveEndCutoff_partition_mass_bp240_oai {I : Type*} [Fintype I] {K : Set (locus a)}
    (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox (locus a))
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) (locus a) K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0 < r) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hκK : tsupport (curveEndCutoff a g)⊆K)
    (hSK : ∀ ε : Fin m → Bool,curveEndAnnulus a ε r R⊆K) (c : ℝ)
    (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
    (hβ : ∀ ε,ContDiff ℝ ∞ (β ε))
    (he : ∀ ε,β ε=ᶠ[𝓝ˢ (radialAnnulus 0 R)] infinityRegularPrimitive a ε c) :
    partitionFormMass B ρ (fun x => curveEndCutoff a g x • curveFSForm a c x)=
      (2:ℝ)^m*c*Real.pi-∑ ε : Fin m → Bool,∫ z : Plane,g (radiusSq z)*planarCurl (β ε) z := by
  have hκ := curveEndCutoff_smooth a hg hc
  have hα := curveFSPrimitive_smooth a c
  have hzκ (x : locus a) (hx : x∉K) : curveEndCutoff a g x=0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hx (hκK hh))
  have hm := partitionFormMass_cutoff_defect (positivePlaneTransitions a) hK B ρ hρ hκ hα hzκ
  rw [curveFSPrimitive_exterior] at hm
  rw [hm]
  have hd := partitionFormMass_finite_disjoint_charts hK (infinityDiffeomorph a)
    (infinityDiffeomorph_positive a)
    (fun i j hij => by simpa only [infinityDiffeomorph_target] using infinityBranch_disjoint a hij)
    (fun ε => curveEndAnnulus a ε r R) (curveEndAnnulus_compact a hr hR) hSK
    (curveEndAnnulus_subset_target a hr hR) B ρ hρ
    (spatialCutoffDefect_smooth hκ hα) (spatialCutoffDefect_skew _ _)
    (fun x hx => curveCutoffDefect_zero_off_annuli a hc hr hR h1 h0 c hx)
  rw [hd]
  have hi (ε : Fin m → Bool) :
      (∫ y in (infinityDiffeomorph a ε).symm '' curveEndAnnulus a ε r R,
        partialChartCoefficient (infinityDiffeomorph a ε)
          (spatialCutoffDefect (curveEndCutoff a g) (curveFSPrimitive a c)) y)=
        (∫ z : Plane,g (radiusSq z)*planarCurl (β ε) z)-c*Real.pi := by
    rw [curveEndAnnulus_coordinates a hr hR ε]
    calc
      _ = ∫ y in radialAnnulus r R,-cutoffWedge (fun z => g (radiusSq z)) (β ε) y+c*deriv g (radiusSq y) := by
        apply setIntegral_congr_fun (radialAnnulus_compact r R).measurableSet
        intro y hy
        exact curveCutoffDefect_end_coefficient a hg hc ε c (radialAnnulus_in_end a hr hR ε hy)
          (regular_extension_germ a (he ε) hy.2)
      _ = _ := integral_planar_residue_annulus hg hc hr h1 h0 (hβ ε) c
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,infinity_end_count,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndCutoff_partition_mass_bp240_oai.{u_1} := @OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndCutoff_partition_mass_bp240_oai.{u_1}
