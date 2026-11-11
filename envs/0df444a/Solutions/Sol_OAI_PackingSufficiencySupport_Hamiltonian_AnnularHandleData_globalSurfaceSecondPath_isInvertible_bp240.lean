-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:10.521031+00:00
-- url     : https://prove2.me/submissions/4a2d36f8-4ff1-4343-85ba-a934563ad1b2

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceSecondPath_isInvertible_annular_bp240

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

theorem fderiv_clm_eval {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → E →L[ℝ] F} {x : E} (hg : DifferentiableAt ℝ g x) (u v : E) :
    fderiv ℝ (fun y => g y v) x u = fderiv ℝ g x u v := by
  rw [(hg.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv]
  simp



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
-- module Solutions.OAIQ240_BP.BallPacking_Moser_SymplecticFamily
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Topology NNReal
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem hamiltonianField_contraction {A : E →L[ℝ] E →L[ℝ] ℝ} (hA : A.IsInvertible)
    (H : ℝ × E → ℝ) (p : ℝ × E) (w : E) :
    A (hamiltonianField A H p) w = -fderiv ℝ H p (0,w) := by
  exact congrArg (fun α : E →L[ℝ] ℝ => α w) (formMoserField_solve (fun _ => hA) p)



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
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricOrientation
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
namespace PackingSufficiencySupport.Hamiltonian
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

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

theorem phaseArea_injective : Injective (phaseArea : PlanePhase ι →L[ℝ] _) := by
  intro v w h
  funext i
  have h1 := congrArg (fun A : PlanePhase ι →L[ℝ] ℝ => A (Pi.single i (0,1))) h
  have h2 := congrArg (fun A : PlanePhase ι →L[ℝ] ℝ => A (Pi.single i (1,0))) h
  apply Prod.ext
  · simpa using h1
  · simpa using h2

theorem phase_decomposition (w : PlanePhase ι) :
    (∑ i, ((w i).1 • (Pi.single i ((1:ℝ),0) : PlanePhase ι) + (w i).2 • (Pi.single i ((0:ℝ),1) : PlanePhase ι))) = w := by
  funext j
  simp only [Finset.sum_apply,Pi.add_apply,Pi.smul_apply]
  rw [Finset.sum_eq_single j]
  · ext <;> simp
  · intro b _ hbj
    simp [Ne.symm hbj]
  · simp

theorem phaseArea_surjective : Surjective (phaseArea : PlanePhase ι →L[ℝ] _) := by
  intro α
  let v : PlanePhase ι := fun i => (α (Pi.single i (0,1)),-α (Pi.single i (1,0)))
  refine ⟨v,?_⟩
  ext w
  rw [←phase_decomposition w]
  simp only [map_sum,map_add,map_smul,smul_eq_mul,
    phaseArea_single_right,planarArea_apply,v,mul_zero,mul_one,sub_zero,zero_sub,neg_neg]

theorem phaseArea_isInvertible : (phaseArea : PlanePhase ι →L[ℝ] _).IsInvertible :=
  ⟨(LinearEquiv.ofBijective (phaseArea : PlanePhase ι →L[ℝ] _).toLinearMap
    ⟨phaseArea_injective,phaseArea_surjective⟩).toContinuousLinearEquiv,rfl⟩

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

end

end PackingSufficiencySupport.Hamiltonian

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

section

variable {F E V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem flatProductMap_smoothAt {g : F → M} {x : F × V}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1) :
    ContMDiffAt 𝓘(ℝ,F × V) 𝓘(ℝ,E × V) ∞ (flatProductMap g) x := by
  have h := hg.prodMap (contMDiffAt_id (I := 𝓘(ℝ,V)) (x := x.2))
  simp +instances only [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at h
  exact h

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem flatProductMap_derivative {g : F → M} {x : F × V}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1) :
    mfderiv 𝓘(ℝ,F × V) 𝓘(ℝ,E × V) (flatProductMap g) x=
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V) := by
  have hf := (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : F × V → F)).contMDiff.contMDiffAt (x := x)
  have hs := (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : F × V → V)).contMDiff.contMDiffAt (x := x)
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  have hd := mfderiv_prodMk (I := 𝓘(ℝ,F × V)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,V))
    (f := g ∘ Prod.fst) (g := Prod.snd) (x := x)
    ((hg.comp x hf).mdifferentiableAt (by simp)) (hs.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ,F × V) ((𝓘(ℝ,E)).prod 𝓘(ℝ,V))
    (fun y : F × V => (g y.1,y.2)) x=_
  apply hd.trans
  erw [mfderiv_comp x (hg.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv,mfderiv_eq_fderiv,fderiv_fst,fderiv_snd]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem productHorizontalLift_pullback_apply (Γ : V → ManifoldOneForm E M)
    {g : F → M} {x : F × V} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1)
    (w : F × V) :
    euclideanPullbackOneForm (fun _ => productHorizontalLift Γ) (flatProductMap g) (0,x) w=
      euclideanPullbackOneForm (fun _ => Γ x.2) g (0,x.1) w.1 := by
  change Γ x.2 (g x.1)
    ((mfderiv 𝓘(ℝ,F × V) 𝓘(ℝ,E × V) (flatProductMap g) x w).1)=
      Γ x.2 (g x.1) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1 w.1)
  rw [flatProductMap_derivative hg]
  rfl

theorem productHorizontalLift_exterior_pullback {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {g : F → M} {x : F × V}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1) :
    euclideanExteriorOneForm
      (fun y => euclideanPullbackOneForm (fun _ => productHorizontalLift Γ) (flatProductMap g) (0,y)) x=
      (manifoldExteriorOneForm (productHorizontalLift Γ) (flatProductMap g x)).bilinearComp
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V))
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V)) := by
  have hfam : SmoothOneFormFamily (fun _ : ℝ => productHorizontalLift Γ) := by
    apply productHorizontalLift_smooth (Γ := fun p : ℝ × V => Γ p.2)
    intro c
    have hm : ContDiffOn ℝ ∞ (fun p : (ℝ × V) × E => (p.1.2,p.2))
        (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
    exact (hΓ c).comp hm (fun _ hp => ⟨mem_univ _,hp.2⟩)
  have he := euclidean_manifold_pullback_exterior_at (flatProductMap_smoothAt hg)
    (hfam.spatial_smooth 0 (flatProductMap g x) (mem_extChartAt_target _))
  simpa only [manifoldMapDifferential,flatProductMap_derivative hg] using he

end

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem bilinearComp_equiv_isInvertible {A : E →L[ℝ] E →L[ℝ] ℝ}
    (c : F ≃L[ℝ] E) (hA : A.IsInvertible) :
    (A.bilinearComp (c : F →L[ℝ] E) (c : F →L[ℝ] E)).IsInvertible := by
  obtain ⟨a,rfl⟩ := hA
  refine ⟨(c.trans a).trans (c.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)),?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem bilinearComp_equiv_isInvertible_iff {A : E →L[ℝ] E →L[ℝ] ℝ}
    (c : F ≃L[ℝ] E) :
    (A.bilinearComp (c : F →L[ℝ] E) (c : F →L[ℝ] E)).IsInvertible ↔ A.IsInvertible := by
  constructor
  · intro h
    have he : (A.bilinearComp (c : F →L[ℝ] E) (c : F →L[ℝ] E)).bilinearComp
        (c.symm : E →L[ℝ] F) (c.symm : E →L[ℝ] F)=A := by
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.bilinearComp_apply,ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
    rw [← he]
    exact bilinearComp_equiv_isInvertible c.symm h
  · exact bilinearComp_equiv_isInvertible c

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
-- module Solutions.OAIQ240_BP.BallPacking_Forms_HorizontalCoupling
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
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
variable {F E V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem globalHorizontalCoupling_pullback {Ω : V →L[ℝ] V →L[ℝ] ℝ}
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {g : F → M} {x : F × V} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1) :
    (globalHorizontalCoupling Ω Γ (flatProductMap g x)).bilinearComp
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V))
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V))=
      Ω.bilinearComp (ContinuousLinearMap.snd ℝ F V) (ContinuousLinearMap.snd ℝ F V)+
        euclideanExteriorOneForm
          (fun y => euclideanPullbackOneForm (fun _ => productHorizontalLift Γ) (flatProductMap g) (0,y)) x := by
  rw [productHorizontalLift_exterior_pullback hΓ hg]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem globalHorizontalCoupling_isInvertible_coordinates {Ω : V →L[ℝ] V →L[ℝ] ℝ}
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {g : F → M} {x : F × V} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1)
    (c : F ≃L[ℝ] E) (hc : (c : F →L[ℝ] E)=mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1)
    (h : (Ω.bilinearComp (ContinuousLinearMap.snd ℝ F V) (ContinuousLinearMap.snd ℝ F V)+
        euclideanExteriorOneForm
          (fun y => euclideanPullbackOneForm (fun _ => productHorizontalLift Γ) (flatProductMap g) (0,y)) x).IsInvertible) :
    (globalHorizontalCoupling Ω Γ (flatProductMap g x)).IsInvertible := by
  apply (bilinearComp_equiv_isInvertible_iff (c.prodCongr (ContinuousLinearEquiv.refl ℝ V))).mp
  have he : ((c.prodCongr (ContinuousLinearEquiv.refl ℝ V)) : (F × V) →L[ℝ] E × V)=
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V) := by
    change (c : F →L[ℝ] E).prodMap (ContinuousLinearMap.id ℝ V)=_
    rw [hc]
    rfl
  rw [he,globalHorizontalCoupling_pullback hΓ hg]
  exact h


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldExteriorAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian


open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem handlePushforwardOneForm_zero
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {α : ManifoldOneForm E M} {K : Set M}
    (hz : ∀ x, x ∉ K → α x=0) {y : N} (hy : y ∉ e '' K) :
    handlePushforwardOneForm e α y=0 := by
  by_cases ht : y∈e.target
  · have hk : e.symm y∉K := by
      intro hk
      exact hy ⟨e.symm y,hk,e.right_inv ht⟩
    rw [handlePushforwardOneForm,extendManifoldOneForm_inside ht]
    simp only [manifoldPullbackOneForm,hz _ hk,ContinuousLinearMap.zero_comp]
  · exact extendManifoldOneForm_outside ht



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

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_smul_at (a : ℝ) {α : ManifoldOneForm E M} {x : M}
    (hα : ContDiffAt ℝ ∞ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)) :
    manifoldExteriorOneForm (a • α) x=a • manifoldExteriorOneForm α x := by
  have he : chartOneForm (a • α) x=a • chartOneForm α x :=
    funext (chartOneForm_smul a α x)
  simp only [manifoldExteriorOneForm,he,
    euclideanExteriorOneForm_smul a (hα.differentiableAt (by simp))]
  rfl

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialFamilyExtension
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
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

 theorem globalHorizontalCoupling_congr_germ (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    {Γ Γ' : V → ManifoldOneForm E M} {z : M × V}
    (h : ∀ᶠ x in 𝓝 z.1,∀ v,Γ v x=Γ' v x) :
    globalHorizontalCoupling Ω Γ z=globalHorizontalCoupling Ω Γ' z := by
  have he : productHorizontalLift Γ =ᶠ[𝓝 z] productHorizontalLift Γ' := by
    filter_upwards [continuousAt_fst.eventually h] with y hy
    exact congrArg (fun L : E →L[ℝ] ℝ => L.comp (ContinuousLinearMap.fst ℝ E V)) (hy y.2)
  exact congrArg (fun B => Ω.bilinearComp (ContinuousLinearMap.snd ℝ E V)
    (ContinuousLinearMap.snd ℝ E V)+B) (manifoldExteriorOneForm_congr_germ he)

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
-- module Solutions.OAIQ240_BP.BallPacking_Layers_PlanarRotation
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments
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

theorem radialArea_hasFDerivAt (x : Plane) :
    HasFDerivAt radialArea
      (Real.pi • ((2*x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2*x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
  have h₁ : HasFDerivAt (fun p : Plane => p.1^2)
      ((2*x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
    simpa using (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2
  have h₂ : HasFDerivAt (fun p : Plane => p.2^2)
      ((2*x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    simpa using (hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2
  exact (h₁.add h₂).const_mul Real.pi

@[simp] theorem radialArea_fderiv (x v : Plane) :
    fderiv ℝ radialArea x v = 2*Real.pi*(x.1*v.1+x.2*v.2) := by
  rw [(radialArea_hasFDerivAt x).fderiv]
  change Real.pi * (2*x.1*v.1+2*x.2*v.2) = _
  ring


end

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem oneCovectorForm_isInvertible [FiniteDimensional ℝ E] {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : A.IsInvertible) {c : ℝ} (hc : c ≠ 0) (η : E →L[ℝ] ℝ) :
    (oneCovectorForm A c η).IsInvertible := by
  let B := oneCovectorForm A c η
  have hAi : Injective A := by obtain ⟨e,he⟩ := hA; rw [←he]; exact e.injective
  have hBi : Injective B := by
    apply (injective_iff_map_eq_zero B).mpr
    intro v hv
    have ht := congrArg (fun α : (Plane × E) →L[ℝ] ℝ => α ((1,0),0)) hv
    have ht0 : v.1.2 = 0 := by
      simp only [B,oneCovectorForm_apply,map_zero,mul_zero,sub_zero,mul_one,zero_add,
        zero_sub,zero_apply] at ht
      have he : c*v.1.2 = 0 := by linarith
      exact (mul_eq_zero.mp he).resolve_left hc
    have hf : A v.2 = 0 := by
      apply ContinuousLinearMap.ext
      intro z
      have hz := congrArg (fun α : (Plane × E) →L[ℝ] ℝ => α ((0,0),z)) hv
      simpa [B,ht0] using hz
    have hf0 : v.2 = 0 := hAi (hf.trans A.map_zero.symm)
    have hs := congrArg (fun α : (Plane × E) →L[ℝ] ℝ => α ((0,1),0)) hv
    have hs0 : v.1.1 = 0 := by
      simp only [B,oneCovectorForm_apply,hf0,ht0,map_zero,mul_zero,mul_one,sub_zero,
        zero_add,add_zero,zero_apply] at hs
      exact (mul_eq_zero.mp hs).resolve_left hc
    exact Prod.ext (Prod.ext hs0 ht0) hf0
  have hBs : Surjective B := by
    intro β
    let t : ℝ := -β ((1,0),0)/c
    let α : E →L[ℝ] ℝ := β.comp (ContinuousLinearMap.inr ℝ Plane E) + t • η
    let z := A.inverse α
    let s := (β ((0,1),0)-η z)/c
    refine ⟨((s,t),z),?_⟩
    apply ContinuousLinearMap.ext
    intro v
    have hz : A z v.2 = β ((0,0),v.2)+t*η v.2 := by
      change A (A.inverse α) v.2 = _
      rw [hA.self_apply_inverse]
      rfl
    have ht : c*t = -β ((1,0),0) := by dsimp [t]; field_simp
    have hs : c*s = β ((0,1),0)-η z := by dsimp [s]; field_simp
    have hβ : β v = v.1.1*β ((1,0),0)+v.1.2*β ((0,1),0)+β ((0,0),v.2) := by
      conv_lhs => rw [show v = v.1.1 • (((1,0),0) : Plane × E) +
          v.1.2 • (((0,1),0) : Plane × E) + ((0,0),v.2) by ext <;> simp]
      simp only [map_add,map_smul,smul_eq_mul]
    change oneCovectorForm A c η ((s,t),z) v = _
    rw [oneCovectorForm_apply,hz,hβ]
    linear_combination v.1.2*hs-v.1.1*ht
  exact ⟨(LinearEquiv.ofBijective B.toLinearMap ⟨hBi,hBs⟩).toContinuousLinearEquiv,rfl⟩


end

open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RearrangementBounds
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem planeMoments_hasFDerivAt (z : PlanePhase ι) :
    HasFDerivAt planeMoments (momentDifferential z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (radialArea_smooth.differentiable (by simp) (z i)).hasFDerivAt.comp z
    (ContinuousLinearMap.proj i : PlanePhase ι →L[ℝ] Plane).hasFDerivAt

omit [DecidableEq ι] in
@[simp] theorem planeMoments_fderiv_apply (z v : PlanePhase ι) (i : ι) :
    fderiv ℝ planeMoments z v i = 2*Real.pi*((z i).1*(v i).1+(z i).2*(v i).2) := by
  rw [(planeMoments_hasFDerivAt z).fderiv]
  simp [momentDifferential]

theorem planeMoments_fderiv_single (i : ι) (z : PlanePhase ι) (w : Plane) :
    fderiv ℝ planeMoments z (Pi.single i w) =
      (2*Real.pi*((z i).1*w.1+(z i).2*w.2)) • Pi.single i (1:ℝ) := by
  funext j
  by_cases hji : j=i
  · subst j; simp
  · simp [hji]

theorem toricHamiltonian_fderiv_single {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (p : ℝ × PlanePhase ι) (i : ι) (w : Plane) :
    fderiv ℝ (toricHamiltonian F) p (0,Pi.single i w) =
      toricAngularSpeed F p.2 i*((p.2 i).1*w.1+(p.2 i).2*w.2) := by
  have hd := (hF.differentiable (by simp) (planeMoments p.2)).hasFDerivAt.comp p
    ((planeMoments_hasFDerivAt p.2).comp p (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))
  change HasFDerivAt (toricHamiltonian F) _ p at hd
  rw [hd.fderiv]
  change fderiv ℝ F (planeMoments p.2) (momentDifferential p.2 (Pi.single i w)) = _
  rw [←(planeMoments_hasFDerivAt p.2).fderiv,planeMoments_fderiv_single,map_smul]
  dsimp [toricAngularSpeed]
  ring

theorem toricHamiltonian_field {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (p : ℝ × PlanePhase ι) (i : ι) :
    hamiltonianField phaseArea (toricHamiltonian F) p i =
      toricAngularSpeed F p.2 i • (-(p.2 i).2,(p.2 i).1) := by
  have h₁ := hamiltonianField_contraction phaseArea_isInvertible (toricHamiltonian F) p
    (Pi.single i (0,1))
  have h₂ := hamiltonianField_contraction phaseArea_isInvertible (toricHamiltonian F) p
    (Pi.single i (1,0))
  rw [phaseArea_single_right,toricHamiltonian_fderiv_single hF] at h₁ h₂
  simp only [planarArea_apply,mul_one,mul_zero,sub_zero,zero_sub,zero_add,add_zero] at h₁ h₂
  apply Prod.ext
  · change _ = toricAngularSpeed F p.2 i * -(p.2 i).2
    linarith
  · change _ = toricAngularSpeed F p.2 i * (p.2 i).1
    linarith

theorem toricHamiltonian_preserves_moments {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (p : ℝ × PlanePhase ι) :
    fderiv ℝ planeMoments p.2 (hamiltonianField phaseArea (toricHamiltonian F) p) = 0 := by
  funext i
  rw [planeMoments_fderiv_apply,toricHamiltonian_field hF]
  simp only [Pi.zero_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_LayerCoordinates
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem twoCovectorForm_isInvertible [FiniteDimensional ℝ E]
    {A : E →L[ℝ] E →L[ℝ] ℝ} (hA : A.IsInvertible)
    (hskew : ∀ v w, A v w = -A w v) {c : ℝ} (hc : c ≠ 0)
    (η ζ : E →L[ℝ] ℝ) (hcomm : ζ (A.inverse η)=0) :
    (twoCovectorForm A c η ζ).IsInvertible := by
  have hAi : Injective A := by obtain ⟨e,he⟩ := hA; rw [←he]; exact e.injective
  have hself (α : E →L[ℝ] ℝ) : α (A.inverse α)=0 := by
    have hs := hskew (A.inverse α) (A.inverse α)
    rw [hA.self_apply_inverse] at hs
    linarith
  have hother : η (A.inverse ζ)=0 := by
    have hs := hskew (A.inverse η) (A.inverse ζ)
    rw [hA.self_apply_inverse,hA.self_apply_inverse,hcomm,neg_zero] at hs
    exact hs
  let B := twoCovectorForm A c η ζ
  have hBi : Injective B := by
    apply (injective_iff_map_eq_zero B).mpr
    intro v hv
    have hAz : A v.2 = v.1.1 • η + v.1.2 • ζ := by
      ext w
      have hh := congrArg (fun α : (Plane × E) →L[ℝ] ℝ => α ((0,0),w)) hv
      simp only [B,twoCovectorForm_apply,mul_zero,sub_zero,add_zero,zero_apply] at hh
      change A v.2 w=v.1.1*η w+v.1.2*ζ w
      linarith
    have hz : v.2=v.1.1 • A.inverse η+v.1.2 • A.inverse ζ := by
      apply hAi
      rw [map_add,map_smul,map_smul,hA.self_apply_inverse,hA.self_apply_inverse,hAz]
    have hη : η v.2=0 := by rw [hz]; simp only [map_add,map_smul,hself,hother,smul_zero,add_zero]
    have hζ : ζ v.2=0 := by rw [hz]; simp only [map_add,map_smul,hcomm,hself,smul_zero,add_zero]
    have ht := congrArg (fun α : (Plane × E) →L[ℝ] ℝ => α ((1,0),0)) hv
    have hs := congrArg (fun α : (Plane × E) →L[ℝ] ℝ => α ((0,1),0)) hv
    simp only [B,twoCovectorForm_apply,map_zero,mul_zero,mul_one,sub_zero,
      zero_sub,zero_add,add_zero,hη,hζ,zero_apply] at ht hs
    have hs0 : v.1.1=0 := (mul_eq_zero.mp hs).resolve_left hc
    have ht0 : v.1.2=0 := by
      have hh : c*v.1.2=0 := by linarith
      exact (mul_eq_zero.mp hh).resolve_left hc
    have hz0 : v.2=0 := by rw [hz,hs0,ht0,zero_smul,zero_smul,zero_add]
    exact Prod.ext (Prod.ext hs0 ht0) hz0
  obtain ⟨e,_⟩ := oneCovectorForm_isInvertible hA hc (0 : E →L[ℝ] ℝ)
  exact ⟨(B.toLinearMap.linearEquivOfInjective hBi e.toLinearEquiv.finrank_eq).toContinuousLinearEquiv,rfl⟩



theorem horizontalOneForm_fderiv {A B : Plane × E → ℝ} {x : Plane × E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (v w : Plane × E) :
    fderiv ℝ (horizontalOneForm A B) x v w =
      fderiv ℝ A x v*w.1.1+fderiv ℝ B x v*w.1.2 := by
  rw [←fderiv_clm_eval ((hA.smul_const _).add (hB.smul_const _))]
  simp only [horizontalOneForm_apply]
  change fderiv ℝ ((fun y => A y*w.1.1)+(fun y => B y*w.1.2)) x v = _
  rw [fderiv_add (hA.mul_const _) (hB.mul_const _),fderiv_mul_const hA,fderiv_mul_const hB]
  simp only [add_apply,smul_apply,smul_eq_mul,mul_comm]

theorem horizontalCoupling_eq {A B : Plane × E → ℝ} {x : Plane × E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (Ω : E →L[ℝ] E →L[ℝ] ℝ) :
    horizontalCoupling Ω A B x =
      twoCovectorForm Ω (fderiv ℝ B x ((1,0),0)-fderiv ℝ A x ((0,1),0))
        ((fderiv ℝ A x).comp (ContinuousLinearMap.inr ℝ Plane E))
        ((fderiv ℝ B x).comp (ContinuousLinearMap.inr ℝ Plane E)) := by
  have decomp (L : (Plane × E) →L[ℝ] ℝ) (v : Plane × E) :
      L v=v.1.1*L ((1,0),0)+v.1.2*L ((0,1),0)+L ((0,0),v.2) := by
    have he : v=v.1.1 • ((1,0),0)+v.1.2 • ((0,1),0)+((0,0),v.2) := by
      ext <;> simp
    conv_lhs => rw [he]
    simp only [map_add,map_smul,smul_eq_mul]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [horizontalCoupling,add_apply,ContinuousLinearMap.bilinearComp_apply,
    euclideanExteriorOneForm,sub_apply,
    ContinuousLinearMap.flip_apply,twoCovectorForm_apply,
    horizontalOneForm_fderiv hA hB,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]
  rw [decomp (fderiv ℝ A x) v,decomp (fderiv ℝ A x) w,
    decomp (fderiv ℝ B x) v,decomp (fderiv ℝ B x) w]
  change Ω v.2 w.2 +
      ((v.1.1*(fderiv ℝ A x) ((1,0),0)+v.1.2*(fderiv ℝ A x) ((0,1),0)+(fderiv ℝ A x) ((0,0),v.2))*w.1.1+
       (v.1.1*(fderiv ℝ B x) ((1,0),0)+v.1.2*(fderiv ℝ B x) ((0,1),0)+(fderiv ℝ B x) ((0,0),v.2))*w.1.2-
       ((w.1.1*(fderiv ℝ A x) ((1,0),0)+w.1.2*(fderiv ℝ A x) ((0,1),0)+(fderiv ℝ A x) ((0,0),w.2))*v.1.1+
        (w.1.1*(fderiv ℝ B x) ((1,0),0)+w.1.2*(fderiv ℝ B x) ((0,1),0)+(fderiv ℝ B x) ((0,0),w.2))*v.1.2)) = Ω v.2 w.2 +
      ((fderiv ℝ B x) ((1,0),0)-(fderiv ℝ A x) ((0,1),0))*(v.1.1*w.1.2-v.1.2*w.1.1)+
      (fderiv ℝ B x) ((0,0),v.2)*w.1.2-v.1.2*(fderiv ℝ B x) ((0,0),w.2)+
      (fderiv ℝ A x) ((0,0),v.2)*w.1.1-v.1.1*(fderiv ℝ A x) ((0,0),w.2)
  ring



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_BaseHorizontalForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory
open scoped ContDiff Manifold Topology

theorem intervalClock_zero {a b s : ℝ} (hab : a < b) (hs : s ≤ a) : intervalClock a b s=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sub_nonneg.mpr hab.le))

theorem intervalClock_one {a b s : ℝ} (hab : a < b) (hs : b ≤ s) : intervalClock a b s=1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).2 (by linarith))

theorem intervalClock_bounds (a b s : ℝ) : 0 ≤ intervalClock a b s ∧ intervalClock a b s ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

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

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_local_identity {U : Set E} {x : E} (hU : U ∈ 𝓝 x) :
    ∃ r : E → E, ContDiff ℝ ∞ r ∧ (∀ y, r y ∈ U) ∧ r =ᶠ[𝓝 x] id := by
  obtain ⟨a,ha,haU⟩ := Metric.mem_nhds_iff.mp hU
  let χ : ContDiffBump x := ⟨a/2,a,by positivity,by linarith⟩
  let r : E → E := fun y => x + χ y • (y-x)
  refine ⟨r,contDiff_const.add (χ.contDiff.smul (contDiff_id.sub contDiff_const)),?_,?_⟩
  · intro y
    apply haU
    by_cases hy : y ∈ ball x a
    · rw [mem_ball_iff_norm]
      change ‖x + χ y • (y-x) - x‖ < a
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg χ.nonneg]
      exact (mul_le_of_le_one_left (norm_nonneg _) χ.le_one).trans_lt (mem_ball_iff_norm.mp hy)
    · have hz : χ y = 0 := χ.zero_of_le_dist (not_lt.mp hy)
      simp only [r,hz,zero_smul,add_zero]
      exact mem_ball_self ha
  · filter_upwards [χ.eventuallyEq_one] with y hy
    change x + χ y • (y-x) = y
    rw [hy,Pi.one_apply,one_smul,add_sub_cancel]


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_LayerAreaForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem surfaceFinalLayer_lower {J R : E → ℝ} {h : ι → E → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} {s : ℝ} (hz : ∀ i, ρ i s=0) (hz₀ : ρ₀ s=0) (v : E) :
    surfaceFinalLayer J h R ρ ρ₀ (s,v)=J v := by simp [surfaceFinalLayer,hz,hz₀]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem surfaceFinalLayer_upper {K H : E → ℝ} {h : ι → E → ℝ} {ψ : E → E}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} {s : ℝ} (ho : ∀ i, ρ i s=1) (ho₀ : ρ₀ s=1) (v : E) :
    surfaceFinalLayer (K-H) h (surfaceRemainder K H h ψ) ρ ρ₀ (s,v)=K (ψ v) := by
  simp only [surfaceFinalLayer,surfaceRemainder,ho,ho₀,Pi.sub_apply,one_mul]
  ring


end

open scoped ContDiff
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_ConstructedSurfaceLayers
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.surfaceFirstCorrectionCoefficient_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.surfaceSecondExtraCoefficient_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.surfaceSuspensionCoefficient_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : E →L[ℝ] E →L[ℝ] ℝ}

variable {ι : Type*} [Fintype ι]

theorem surfaceInterpolatedLayer_endpoints (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (K H : E → ℝ) (h : ι → E → ℝ)
    (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ) (τ s : ℝ) (v : E) :
    (S s=0 → (∀ i, ρ i s=0) → ρ₀ s=0 →
      surfaceInterpolatedLayer S K H h (Φ.map 1).symm ρ ρ₀ τ (s,Φ.map (S s) v)=τ*(K v-H v)) ∧
    (S s=1 → (∀ i, ρ i s=1) → ρ₀ s=1 →
      surfaceInterpolatedLayer S K H h (Φ.map 1).symm ρ ρ₀ τ (s,Φ.map (S s) v)=
        H v+τ*(K v-H v)) := by
  constructor
  · intro hS hρ hρ₀
    simp [surfaceInterpolatedLayer,surfaceFirstLayer,surfaceFinalLayer_lower hρ hρ₀,
      hS,Φ.zero]
  · intro hS hρ hρ₀
    simp only [surfaceInterpolatedLayer,surfaceFirstLayer,surfaceFinalLayer_upper hρ hρ₀,
      hS,Homeomorph.symm_apply_apply,one_mul]
    ring



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularChartNormalization
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

namespace AnnularHandleData

theorem band_compact (b : ℝ) : IsCompact (band b) := isCompact_Icc.prod isCompact_univ

theorem band_subset_source (H : AnnularHandleData E M) {b : ℝ} (hb : b<H.width) :
    band b⊆H.chart.source := by
  rw [H.source_eq]
  intro z hz
  exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,hz.2⟩

theorem image_band_compact (H : AnnularHandleData E M) {b : ℝ} (hb : b<H.width) :
    IsCompact (H.chart '' band b) :=
  (band_compact b).image_of_continuousOn
    (H.chart.contMDiffOn.continuousOn.mono (H.band_subset_source hb))

end AnnularHandleData
end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem cylinderRadialForm_apply (b : ℝ) (z : HandleCylinder) (v : CylinderModel) :
    cylinderRadialForm b z v=deriv (intervalClock (-b) b) z.1*v.1 := by
  unfold cylinderRadialForm manifoldScalarDifferential
  change mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) (intervalClock (-b) b ∘ Prod.fst) z v=_
  rw [mfderiv_comp z ((intervalClock_smooth (-b) b).contMDiff.mdifferentiableAt (by simp))
    (cylinder_fst_smooth.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
  have he : mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) (Prod.fst : HandleCylinder → ℝ) z=
      ContinuousLinearMap.fst ℝ ℝ CircleModel := by
    rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod]
    exact mfderiv_fst
  rw [he]
  change fderiv ℝ (intervalClock (-b) b) z.1 v.1=_
  exact fderiv_eq_deriv_mul

theorem cylinderRadialForm_zero {b : ℝ} (hb : 0<b) {z : HandleCylinder}
    (hz : z∉AnnularHandleData.band b) : cylinderRadialForm b z=0 := by
  have hn : z.1∉Icc (-b) b := fun hk => hz ⟨hk,mem_univ _⟩
  have hd : deriv (intervalClock (-b) b) z.1=0 := by
    simp only [mem_Icc,not_and_or,not_le] at hn
    rcases hn with h|h
    · exact intervalClock_deriv_zero_left (by linarith) h
    · exact intervalClock_deriv_zero_right (by linarith) h
  apply ContinuousLinearMap.ext
  intro v
  simp [cylinderRadialForm_apply,hd]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularHandleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

namespace AnnularHandleData
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem densityChart_source (H : AnnularHandleData Plane M) :
    H.densityChart.source=Ioo (-H.width) H.width ×ˢ Ioo (0:ℝ) 1 := by
  ext y
  change (y∈univ ×ˢ Ioo (0:ℝ) 1 ∧ cylinderCover y∈H.chart.source) ↔ _
  rw [H.source_eq]
  simp only [mem_prod,mem_univ,true_and,and_true,cylinderCover]
  exact and_comm

end AnnularHandleData

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem off_band_inverse (D : AnnularHandleData E M) (b : ℝ) {x : M}
    (hx : x∈D.chart.target) (hn : x∉D.chart '' band b) : (D.chart.symm x).1∉Icc (-b) b := by
  intro hs
  exact hn ⟨D.chart.symm x,⟨hs,mem_univ _⟩,D.chart.right_inv hx⟩

theorem radial_zero (D : AnnularHandleData E M) {b : ℝ} (hb : 0<b)
    {x : M} (hx : x∉D.chart '' band b) : D.radial b x=0 :=
  handlePushforwardOneForm_zero D.chart (fun _ hy => cylinderRadialForm_zero hb hy) hx

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_SurfaceSuspensionCoefficients
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

theorem surfaceFirstCorrectionCoefficient_tails (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (H : V → ℝ) (p : ℝ × V) (s : ℝ) (hs : S s=0 ∨ S s=1) :
    surfaceFirstCorrectionCoefficient Φ S H (p,s)=0 := by
  rcases hs with hs|hs <;> simp [surfaceFirstCorrectionCoefficient,hs]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem handleFirstCorrection_off_band
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b)
    (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ) (p : ℝ × V) {x : M}
    (hx : x∈D.chart.target) (hn : x∉D.chart '' band b) :
    handleFirstCorrection D b Φ H p x=0 := by
  have hr : D.radial b x=0 :=
    D.radial_zero hb hn
  have ht : intervalClock (-b) b (D.chart.symm x).1=0 ∨
      intervalClock (-b) b (D.chart.symm x).1=1 := by
    have hs := D.off_band_inverse b hx hn
    simp only [mem_Icc,not_and_or,not_le] at hs
    rcases hs with hs|hs
    · exact Or.inl (intervalClock_zero (by linarith) hs.le)
    · exact Or.inr (intervalClock_one (by linarith) hs.le)
  simp only [handleFirstCorrection,hr,smul_zero,
    surfaceFirstCorrectionCoefficient_tails Φ _ H p _ ht,zero_smul,add_zero]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem globalSurfaceFirstPrimitive_off_band
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b)
    (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ) (Γ : V → ManifoldOneForm E M)
    (p : ℝ × V) {x : M} (hn : x∉D.chart '' band b) :
    globalSurfaceFirstPrimitive D b Φ H Γ p x=Γ p.2 x := by
  by_cases hx : x∈D.chart.target
  · simp [globalSurfaceFirstPrimitive,extendManifoldOneForm_inside hx,
      handleFirstCorrection_off_band D hb Φ H p hx hn]
  · simp [globalSurfaceFirstPrimitive,extendManifoldOneForm_outside hx]

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {ι : Type*} [Fintype ι]

theorem surfaceSecondExtraCoefficient_tails (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (p : ℝ × V) (s : ℝ)
    (hs : (S s=0 ∧ (∀ i,ρ i s=0) ∧ ρ₀ s=0) ∨
      (S s=1 ∧ (∀ i,ρ i s=1) ∧ ρ₀ s=1)) :
    surfaceSecondExtraCoefficient Φ S K H h ρ ρ₀ (p,s)=0 := by
  have he := surfaceInterpolatedLayer_endpoints Φ S K H h ρ ρ₀ p.1 s p.2
  rcases hs with ⟨hs,hρ,hρ₀⟩|⟨hs,hρ,hρ₀⟩
  · dsimp only [surfaceSecondExtraCoefficient,surfaceSecondCorrectionCoefficient]
    rw [he.1 hs hρ hρ₀,surfaceFirstCorrectionCoefficient_tails Φ S H (1,p.2) s (Or.inl hs),hs]
    ring
  · dsimp only [surfaceSecondExtraCoefficient,surfaceSecondCorrectionCoefficient]
    rw [he.2 hs hρ hρ₀,surfaceFirstCorrectionCoefficient_tails Φ S H (1,p.2) s (Or.inr hs),hs]
    ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {ι : Type*} [Fintype ι]

theorem handleSecondExtra_off_band
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (hlo : ∀ s, s ≤ -b → (∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s, b ≤ s → (∀ i,ρ i s=1) ∧ ρ₀ s=1)
    (p : ℝ × V) {x : M} (hx : x∈D.chart.target)
    (hn : x∉D.chart '' band b) : handleSecondExtra D b Φ K H h ρ ρ₀ p x=0 := by
  have hs := D.off_band_inverse b hx hn
  simp only [mem_Icc,not_and_or,not_le] at hs
  have ht : (intervalClock (-b) b (D.chart.symm x).1=0 ∧
      (∀ i,ρ i (D.chart.symm x).1=0) ∧
      ρ₀ (D.chart.symm x).1=0) ∨
    (intervalClock (-b) b (D.chart.symm x).1=1 ∧
      (∀ i,ρ i (D.chart.symm x).1=1) ∧
      ρ₀ (D.chart.symm x).1=1) := by
    rcases hs with hs|hs
    · exact Or.inl ⟨intervalClock_zero (by linarith) hs.le,hlo _ hs.le⟩
    · exact Or.inr ⟨intervalClock_one (by linarith) hs.le,hhi _ hs.le⟩
  simp only [handleSecondExtra,surfaceSecondExtraCoefficient_tails Φ _ K H h ρ ρ₀ p _ ht,zero_smul]

theorem globalSurfaceSecondPrimitive_off_band
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (hlo : ∀ s, s ≤ -b → (∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s, b ≤ s → (∀ i,ρ i s=1) ∧ ρ₀ s=1)
    (Γ : V → ManifoldOneForm E M) (p : ℝ × V) {x : M}
    (hn : x∉D.chart '' band b) :
    globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ p x=
      Γ p.2 x+(p.1*(K p.2-H p.2)) • D.dual x := by
  by_cases hx : x∈D.chart.target
  · simp [globalSurfaceSecondPrimitive,extendManifoldOneForm_inside hx,
      handleSecondExtra_off_band D hb Φ K H h ρ ρ₀ hlo hhi p hx hn,
      globalSurfaceFirstPrimitive_off_band D hb Φ H Γ (1,p.2) hn]
  · simp [globalSurfaceSecondPrimitive,extendManifoldOneForm_outside hx,
      globalSurfaceFirstPrimitive_off_band D hb Φ H Γ (1,p.2) hn]

end
section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 theorem handleAnnularCover_smoothAt
    (D : AnnularHandleData E M)
    {q : Plane} (hq : cylinderCover q∈D.chart.source) :
    ContMDiffAt 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ (D.handleAnnularCover) q :=
  (D.chart.contMDiffOn.contMDiffAt
    (D.chart.open_source.mem_nhds hq)).comp q cylinderCover_smooth.contMDiffAt

end

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularHandleCurvature
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
 theorem annularCoverDomain_eq
    (D : AnnularHandleData Plane M)
    :
    D.annularCoverDomain=Ioo (-D.width) D.width ×ˢ univ := by
  rw [annularCoverDomain,D.source_eq]
  rfl

 theorem annularCoverTwoCoefficient_smooth
    (D : AnnularHandleData Plane M)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ) :
    ContDiffOn ℝ ∞ (D.annularCoverTwoCoefficient Λ) (D.annularCoverDomain) := by
  intro q hq
  have hs := euclideanPullbackTwoForm_contDiffAt (Ω := fun _ : ℝ => Λ)
    (g := D.handleAnnularCover) (p := (0,q))
    (SmoothTwoFormFamily.const (P := ℝ) hΛ) (D.handleAnnularCover_smoothAt hq)
  exact (((hs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).comp q
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
 theorem annularCoverTwoCoefficient_ne_zero
    (D : AnnularHandleData Plane M)
    {Λ : ManifoldTwoForm Plane M}
    (hs : ∀ x u v,Λ x u v= -Λ x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 < chartTwoForm Λ c y (1,0) (0,1))
    {q : Plane} (hq : q∈D.annularCoverDomain) :
    D.annularCoverTwoCoefficient Λ q≠0 := by
  intro hz
  let L := D.handleAnnularCoverLinearEquiv hq
  let B := (Λ (D.handleAnnularCover q)).bilinearComp (L : Plane →L[ℝ] Plane) (L : Plane →L[ℝ] Plane)
  have hB : ∀ u v,B u v= -B v u := fun u v => hs _ _ _
  have hB0 : B (1,0) (0,1)=0 := hz
  have hzero : Λ (D.handleAnnularCover q)=0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    have hv := planar_skew_coefficient B hB (L.symm u) (L.symm v)
    simpa only [B,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply,hB0,zero_mul,zero_apply] using hv
  let c := D.handleAnnularCover q
  have hc := mem_extChartAt_source (I := 𝓘(ℝ,Plane)) c
  have hi := hp c (extChartAt 𝓘(ℝ,Plane) c c) ((extChartAt 𝓘(ℝ,Plane) c).map_source hc)
  have hcc : (extChartAt 𝓘(ℝ,Plane) c).symm (extChartAt 𝓘(ℝ,Plane) c c)=c :=
    (extChartAt 𝓘(ℝ,Plane) c).left_inv hc
  simp only [chartTwoForm,hcc,ContinuousLinearMap.bilinearComp_apply] at hi
  change 0<Λ (D.handleAnnularCover q) _ _ at hi
  rw [hzero] at hi
  exact (lt_irrefl 0) hi

 theorem annularCoverTwoCoefficient_positive
    (D : AnnularHandleData Plane M)
    (hor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hs : ∀ x u v,Λ x u v= -Λ x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 < chartTwoForm Λ c y (1,0) (0,1))
    {q : Plane} (hq : q∈D.annularCoverDomain) :
    0<D.annularCoverTwoCoefficient Λ q := by
  let z : Plane := (q.1,1/2)
  have hsdom : q.1∈Ioo (-D.width) D.width := by
    rw [D.annularCoverDomain_eq] at hq
    exact hq.1
  have hz : z∈D.densityChart.source := by
    rw [D.densityChart_source]
    exact ⟨hsdom,by norm_num [z]⟩
  have hzd : z∈D.annularCoverDomain := by
    rw [D.annularCoverDomain_eq]
    exact ⟨hsdom,mem_univ _⟩
  let c := D.densityChart z
  have hc : D.densityChart z∈(extChartAt 𝓘(ℝ,Plane) c).source := mem_extChartAt_source c
  have hpz : 0<D.annularCoverTwoCoefficient Λ z := by
    change 0<partialChartCoefficient D.densityChart Λ z
    rw [partialChartCoefficient_change _ hs hz hc]
    exact mul_pos (hor c z hz hc) (hp c _ ((extChartAt 𝓘(ℝ,Plane) c).map_source hc))
  by_contra hn
  have hn' : D.annularCoverTwoCoefficient Λ q≤0 := le_of_not_gt hn
  have hconn : IsPreconnected (D.annularCoverDomain) := by
    rw [D.annularCoverDomain_eq]
    exact isPreconnected_Ioo.prod isPreconnected_univ
  obtain ⟨y,hy,hy0⟩ := hconn.intermediate_value hq hzd
    (D.annularCoverTwoCoefficient_smooth hΛ).continuousOn ⟨hn',hpz.le⟩
  exact D.annularCoverTwoCoefficient_ne_zero hs hp hy hy0

theorem annularCover_positive_exterior
    (D : AnnularHandleData Plane M)
    (hor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hs : ∀ x u v,Λ x u v= -Λ x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 < chartTwoForm Λ c y (1,0) (0,1))
    {γ : ManifoldOneForm Plane M} {r : ℝ} (hr : 0 < r)
    (hγ : ∀ x∈D.chart.target,manifoldExteriorOneForm γ x=r • Λ x)
    {q : Plane} (hq : q∈D.annularCoverDomain) :
    0 < manifoldExteriorOneForm γ (D.handleAnnularCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (D.handleAnnularCover) q (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (D.handleAnnularCover) q (0,1)) := by
  have heq := hγ (D.handleAnnularCover q) (D.chart.map_source hq)
  have hv := congrArg (fun B : Plane →L[ℝ] Plane →L[ℝ] ℝ =>
    B (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (D.handleAnnularCover) q (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (D.handleAnnularCover) q (0,1))) heq
  have hp' := mul_pos hr (D.annularCoverTwoCoefficient_positive hor hΛ hs hp hq)
  exact lt_of_lt_of_eq hp' hv.symm

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem handleAnnularCover_surjOn
    (D : AnnularHandleData Plane M) :
    SurjOn (D.handleAnnularCover) (D.annularCoverDomain) D.chart.target := by
  intro x hx
  let z := D.chart.symm x
  let q : Plane := (z.1,shortCircleArgument z.2)
  have heq : cylinderCover q=z := by
    exact Prod.ext rfl (circleTurn_shortCircleArgument z.2)
  refine ⟨q,?_,?_⟩
  · change cylinderCover q∈D.chart.source
    rw [heq]
    exact D.chart.map_target hx
  · change D.chart (cylinderCover q)=x
    rw [heq]
    exact D.chart.right_inv hx

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_AnnularInverseDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open scoped Manifold
open Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : E →L[ℝ] E →L[ℝ] ℝ}

 theorem euclideanExteriorOneForm_congr_germ {α β : E → E →L[ℝ] ℝ} {x : E}
    (h : α =ᶠ[𝓝 x] β) : euclideanExteriorOneForm α x=euclideanExteriorOneForm β x := by
  simp only [euclideanExteriorOneForm,h.fderiv_eq]

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_StationaryManifoldPullback
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped Topology
open scoped Manifold
open Manifold

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem toric_differential_eq {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (z : PlanePhase ι) :
    fderiv ℝ (fun w => F (planeMoments w)) z =
      spatialDifferential (toricHamiltonian F) (t,z) := by
  have hs : ContDiff ℝ ∞ (toricHamiltonian F) := toricHamiltonian_smooth hF
  have hd := (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (t,z)).hasFDerivAt.comp z
    ((hasFDerivAt_const t z).prodMk (hasFDerivAt_id z))
  exact hd.fderiv

theorem toric_covectors_commute {F G : (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (z : PlanePhase ι) :
    fderiv ℝ (fun w => G (planeMoments w)) z
      (phaseArea.inverse (fderiv ℝ (fun w => F (planeMoments w)) z))=0 := by
  let X := hamiltonianField phaseArea (toricHamiltonian F) (0,z)
  have hX : X = -phaseArea.inverse (fderiv ℝ (fun w => F (planeMoments w)) z) := by
    rw [toric_differential_eq hF 0 z]
    rfl
  have hd := (hG.differentiable (by simp) (planeMoments z)).hasFDerivAt.comp z
    (planeMoments_hasFDerivAt z)
  change HasFDerivAt (fun w => G (planeMoments w)) _ z at hd
  have hm : fderiv ℝ planeMoments z X=0 := toricHamiltonian_preserves_moments hF (0,z)
  have hh : fderiv ℝ (fun w => G (planeMoments w)) z X=0 := by
    rw [hd.fderiv]
    change fderiv ℝ G (planeMoments z) (momentDifferential z X)=0
    rw [←(planeMoments_hasFDerivAt z).fderiv,hm,map_zero]
  rw [hX,map_neg] at hh
  exact neg_eq_zero.mp hh

theorem toric_twoCovectorForm_isInvertible {F G : (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (z : PlanePhase ι)
    {c : ℝ} (hc : 0 < c) :
    (twoCovectorForm phaseArea c (fderiv ℝ (fun w => F (planeMoments w)) z)
      (fderiv ℝ (fun w => G (planeMoments w)) z)).IsInvertible :=
  twoCovectorForm_isInvertible phaseArea_isInvertible phaseArea_skew hc.ne'
    _ _ (toric_covectors_commute hF hG z)

omit [DecidableEq ι] in
theorem toricHorizontalCoefficient_vertical {F : Plane × (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (x : Plane × PlanePhase ι) :
    (fderiv ℝ (toricHorizontalCoefficient F) x).comp (ContinuousLinearMap.inr ℝ Plane (PlanePhase ι)) =
      fderiv ℝ (fun z => F (x.1,planeMoments z)) x.2 := by
  have hd := ((toricHorizontalCoefficient_smooth hF).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasFDerivAt.comp x.2
    ((hasFDerivAt_const (𝕜 := ℝ) x.1 x.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) x.2))
  exact hd.fderiv.symm

theorem toric_horizontalCoupling_isInvertible {F G : Plane × (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (x : Plane × PlanePhase ι)
    (hpositive : 0 < fderiv ℝ (toricHorizontalCoefficient G) x ((1,0),0) -
      fderiv ℝ (toricHorizontalCoefficient F) x ((0,1),0)) :
    (horizontalCoupling phaseArea (toricHorizontalCoefficient F) (toricHorizontalCoefficient G) x).IsInvertible := by
  rw [horizontalCoupling_eq ((toricHorizontalCoefficient_smooth hF).differentiable (by simp) x)
    ((toricHorizontalCoefficient_smooth hG).differentiable (by simp) x),
    toricHorizontalCoefficient_vertical hF,toricHorizontalCoefficient_vertical hG]
  apply toric_twoCovectorForm_isInvertible (F := fun p => F (x.1,p))
    (G := fun p => G (x.1,p)) _ _ x.2 hpositive
  · exact hF.comp (contDiff_const.prodMk contDiff_id)
  · exact hG.comp (contDiff_const.prodMk contDiff_id)

omit [DecidableEq ι] in
theorem toricHorizontalCoefficient_contDiffAt {F : Plane × (ι → ℝ) → ℝ}
    {U : Set Plane} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ))
    {x : Plane × PlanePhase ι} (hx : x.1∈U) :
    ContDiffAt ℝ ∞ (toricHorizontalCoefficient F) x :=
  (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx,mem_univ _⟩)).comp x
    (contDiffAt_fst.prodMk (planeMoments_smooth.contDiffAt.comp x contDiffAt_snd))

omit [DecidableEq ι] in
theorem toricHorizontalCoefficient_base {F : Plane × (ι → ℝ) → ℝ}
    {U : Set Plane} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ))
    {x : Plane × PlanePhase ι} (hx : x.1∈U) (w : Plane) :
    fderiv ℝ (toricHorizontalCoefficient F) x (w,0)=
      fderiv ℝ (fun y => F (y,planeMoments x.2)) x.1 w := by
  have hi : HasFDerivAt (fun y : Plane => (y,x.2))
      (ContinuousLinearMap.inl ℝ Plane (PlanePhase ι)) x.1 :=
    (hasFDerivAt_id x.1).prodMk (hasFDerivAt_const x.2 x.1)
  have h := ((toricHorizontalCoefficient_contDiffAt hU hF hx).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp x.1 hi
  exact (congrArg (fun L : Plane →L[ℝ] ℝ => L w) h.fderiv).symm

theorem toric_horizontalCoupling_isInvertible_local {F G : Plane × (ι → ℝ) → ℝ}
    {U : Set Plane} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) (hG : ContDiffOn ℝ ∞ G (U ×ˢ univ))
    (x : Plane × PlanePhase ι) (hx : x.1∈U)
    (hpositive : 0 < fderiv ℝ (toricHorizontalCoefficient G) x ((1,0),0) -
      fderiv ℝ (toricHorizontalCoefficient F) x ((0,1),0)) :
    (horizontalCoupling phaseArea (toricHorizontalCoefficient F) (toricHorizontalCoefficient G) x).IsInvertible := by
  obtain ⟨r,hr,hrU,he⟩ := exists_smooth_local_identity
    ((hU.prod isOpen_univ).mem_nhds (show (x.1,planeMoments x.2)∈U ×ˢ univ from ⟨hx,mem_univ _⟩))
  let F' := F ∘ r
  let G' := G ∘ r
  have hF' : ContDiff ℝ ∞ F' := hF.comp_contDiff hr hrU
  have hG' : ContDiff ℝ ∞ G' := hG.comp_contDiff hr hrU
  have hm : ContinuousAt (fun y : Plane × PlanePhase ι => (y.1,planeMoments y.2)) x :=
    continuousAt_fst.prodMk (planeMoments_smooth.continuous.continuousAt.comp continuousAt_snd)
  have heF : toricHorizontalCoefficient F' =ᶠ[𝓝 x] toricHorizontalCoefficient F := by
    filter_upwards [hm.preimage_mem_nhds he] with y hy
    exact congrArg F hy
  have heG : toricHorizontalCoefficient G' =ᶠ[𝓝 x] toricHorizontalCoefficient G := by
    filter_upwards [hm.preimage_mem_nhds he] with y hy
    exact congrArg G hy
  have hp' : 0 < fderiv ℝ (toricHorizontalCoefficient G') x ((1,0),0) -
      fderiv ℝ (toricHorizontalCoefficient F') x ((0,1),0) := by
    rwa [heF.fderiv_eq,heG.fderiv_eq]
  have hi := toric_horizontalCoupling_isInvertible hF' hG' x hp'
  have hform : horizontalOneForm (toricHorizontalCoefficient F') (toricHorizontalCoefficient G') =ᶠ[𝓝 x]
      horizontalOneForm (toricHorizontalCoefficient F) (toricHorizontalCoefficient G) := by
    filter_upwards [heF,heG] with y hyF hyG
    simp only [horizontalOneForm,hyF,hyG]
  unfold horizontalCoupling at hi ⊢
  rwa [euclideanExteriorOneForm_congr_germ hform] at hi

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

omit [DecidableEq ι] [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem toricChart_coefficients_smooth {Γ : (ι → ℝ) → ManifoldOneForm Plane M}
    (hΓ : SmoothOneFormFamily Γ) (c : M) :
    ContDiffOn ℝ ∞ (toricChartA Γ c) ((extChartAt 𝓘(ℝ,Plane) c).target ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (toricChartB Γ c) ((extChartAt 𝓘(ℝ,Plane) c).target ×ˢ univ) := by
  have hs := (hΓ c).comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
    (show MapsTo (fun q : Plane × (ι → ℝ) => (q.2,q.1))
      ((extChartAt 𝓘(ℝ,Plane) c).target ×ˢ univ) (univ ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target)
      from fun _ hq => ⟨mem_univ _,hq.1⟩)
  exact ⟨hs.clm_apply contDiffOn_const,hs.clm_apply contDiffOn_const⟩

omit [DecidableEq ι] in
theorem toricChart_curl {Γ : (ι → ℝ) → ManifoldOneForm Plane M}
    (hΓ : SmoothOneFormFamily Γ) (c : M) {x : Plane × PlanePhase ι}
    (hx : x.1∈(extChartAt 𝓘(ℝ,Plane) c).target) :
    fderiv ℝ (toricHorizontalCoefficient (toricChartB Γ c)) x ((1,0),0)-
      fderiv ℝ (toricHorizontalCoefficient (toricChartA Γ c)) x ((0,1),0)=
      chartTwoForm (manifoldExteriorOneForm (Γ (planeMoments x.2))) c x.1 (1,0) (0,1) := by
  have hs := toricChart_coefficients_smooth hΓ c
  rw [toricHorizontalCoefficient_base (isOpen_extChartAt_target c) hs.2 hx,
    toricHorizontalCoefficient_base (isOpen_extChartAt_target c) hs.1 hx]
  have hα := (hΓ.spatial_smooth (planeMoments x.2) c hx).differentiableAt (by simp)
  rw [manifoldExteriorOneForm_chart (fun z y hy =>
    (hΓ.spatial_smooth (planeMoments x.2) z hy).contDiffWithinAt) hx]
  change fderiv ℝ (fun y => chartOneForm (Γ (planeMoments x.2)) c y (0,1)) x.1 (1,0)-
      fderiv ℝ (fun y => chartOneForm (Γ (planeMoments x.2)) c y (1,0)) x.1 (0,1)=_
  rw [fderiv_clm_eval hα,fderiv_clm_eval hα]
  rfl

omit [DecidableEq ι] in
theorem toricChart_horizontal_pullback (Γ : (ι → ℝ) → ManifoldOneForm Plane M)
    (c : M) {x : Plane × PlanePhase ι} (hx : x.1∈(extChartAt 𝓘(ℝ,Plane) c).target) :
    euclideanPullbackOneForm (fun _ => productHorizontalLift (Γ ∘ planeMoments))
      (flatProductMap (extChartAt 𝓘(ℝ,Plane) c).symm) (0,x)=
    horizontalOneForm (toricHorizontalCoefficient (toricChartA Γ c))
      (toricHorizontalCoefficient (toricChartB Γ c)) x := by
  have hg := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hx)
  apply ContinuousLinearMap.ext
  intro v
  rw [productHorizontalLift_pullback_apply _ hg]
  have he : euclideanPullbackOneForm (fun _ => (Γ ∘ planeMoments) x.2)
      (extChartAt 𝓘(ℝ,Plane) c).symm (0,x.1)=chartOneForm (Γ (planeMoments x.2)) c x.1 := by
    simp only [euclideanPullbackOneForm,chartOneForm,chartDifferential_inverse hx,Function.comp_apply]
  rw [he,horizontalOneForm_apply]
  let L := chartOneForm (Γ (planeMoments x.2)) c x.1
  change L v.1=L (1,0)*v.1.1+L (0,1)*v.1.2
  have hv : v.1=v.1.1 • (1,0)+v.1.2 • (0,1) := by ext <;> simp
  rw [show L v.1=L (v.1.1 • (1,0)+v.1.2 • (0,1)) from congrArg L hv]
  simp only [map_add,map_smul,smul_eq_mul]
  ring

theorem globalToricCoupling_isInvertible_chart {Γ : (ι → ℝ) → ManifoldOneForm Plane M}
    (hΓ : SmoothOneFormFamily Γ) (c : M) {x : Plane × PlanePhase ι}
    (hx : x.1∈(extChartAt 𝓘(ℝ,Plane) c).target)
    (hpos : 0 < chartTwoForm (manifoldExteriorOneForm (Γ (planeMoments x.2))) c x.1 (1,0) (0,1)) :
    (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments)
      ((extChartAt 𝓘(ℝ,Plane) c).symm x.1,x.2)).IsInvertible := by
  have hs := toricChart_coefficients_smooth hΓ c
  have hp : 0 < fderiv ℝ (toricHorizontalCoefficient (toricChartB Γ c)) x ((1,0),0)-
      fderiv ℝ (toricHorizontalCoefficient (toricChartA Γ c)) x ((0,1),0) := by
    rwa [toricChart_curl hΓ c hx]
  have hi := toric_horizontalCoupling_isInvertible_local
    (isOpen_extChartAt_target c) hs.1 hs.2 x hx hp
  have hg := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hx)
  have hC : (chartDifferential (E := Plane) c ((extChartAt 𝓘(ℝ,Plane) c).symm x.1)).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,Plane))
      ((extChartAt 𝓘(ℝ,Plane) c).map_target hx) using 1
    all_goals try with_reducible_and_instances rfl
  have hD : (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (extChartAt 𝓘(ℝ,Plane) c).symm x.1).IsInvertible := by
    rw [← chartDifferential_inverse hx]
    exact hC.inverse
  obtain ⟨d,hd⟩ := hD
  have he : (fun y => euclideanPullbackOneForm (fun _ => productHorizontalLift (Γ ∘ planeMoments))
        (flatProductMap (extChartAt 𝓘(ℝ,Plane) c).symm) (0,y)) =ᶠ[𝓝 x]
      horizontalOneForm (toricHorizontalCoefficient (toricChartA Γ c))
        (toricHorizontalCoefficient (toricChartB Γ c)) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target c).mem_nhds hx)] with y hy
    exact toricChart_horizontal_pullback Γ c hy
  have hext := euclideanExteriorOneForm_congr_germ he
  apply globalHorizontalCoupling_isInvertible_coordinates (hΓ.comp planeMoments_smooth) hg d hd
  exact hext.symm ▸ hi

theorem globalToricCoupling_isInvertible {Γ : (ι → ℝ) → ManifoldOneForm Plane M}
    (hΓ : SmoothOneFormFamily Γ) (z : M × PlanePhase ι)
    (hpos : 0 < chartTwoForm (manifoldExteriorOneForm (Γ (planeMoments z.2)))
      z.1 (extChartAt 𝓘(ℝ,Plane) z.1 z.1) (1,0) (0,1)) :
    (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments) z).IsInvertible := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,Plane)) z.1
  have hi := globalToricCoupling_isInvertible_chart hΓ z.1
    (x := (extChartAt 𝓘(ℝ,Plane) z.1 z.1,z.2)) ((extChartAt 𝓘(ℝ,Plane) z.1).map_source hx) hpos
  simpa only [(extChartAt 𝓘(ℝ,Plane) z.1).left_inv hx,Prod.mk.eta] using hi

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_ToricClosedShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem toricClosedShift_smooth {Γ : P → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {J : P → ℝ} (hJ : ContDiff ℝ ∞ J) {β : ManifoldOneForm E M}
    (hβ : SmoothOneFormFamily (fun _ : ℝ => β)) (t : ℝ) :
    SmoothOneFormFamily (toricClosedShift Γ J β t) := by
  exact hΓ.add ((hβ.comp (f := fun _ : P => (0:ℝ)) contDiff_const).smul (contDiff_const.mul hJ))

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem toricClosedShift_exterior {Γ : P → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    (J : P → ℝ) {β : ManifoldOneForm E M}
    (hβ : SmoothOneFormFamily (fun _ : ℝ => β)) (hdβ : ∀ x,manifoldExteriorOneForm β x=0)
    (t : ℝ) (p : P) : manifoldExteriorOneForm (toricClosedShift Γ J β t p)=manifoldExteriorOneForm (Γ p) := by
  funext x
  have hx := (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source (I := 𝓘(ℝ,E)) x)
  have ha := hΓ.spatial_smooth p x hx
  have hb := hβ.spatial_smooth 0 x hx
  have hs : ContDiffAt ℝ ∞ (chartOneForm ((t*J p) • β) x) (extChartAt 𝓘(ℝ,E) x x) := by
    have he : chartOneForm ((t*J p) • β) x=(t*J p) • chartOneForm β x := funext (chartOneForm_smul _ _ _)
    rw [he]
    exact contDiffAt_const.smul hb
  change manifoldExteriorOneForm (Γ p+(t*J p) • β) x=_
  rw [manifoldExteriorOneForm_add_at ha hs,manifoldExteriorOneForm_smul_at _ hb,hdβ]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change manifoldExteriorOneForm (Γ p) x v w+(t*J p)*0=manifoldExteriorOneForm (Γ p) x v w
  simp only [mul_zero,add_zero]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

 theorem globalSurfaceSecondPrimitive_isInvertible_outside {κ : Type*} [Fintype κ]
    (D : AnnularHandleData Plane M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := ι)))
    {K H : (ι → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (h : κ → PlanePhase ι → ℝ) (ρ : κ → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (hlo : ∀ s,s ≤ -b → (∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s,b ≤ s → (∀ i,ρ i s=1) ∧ ρ₀ s=1)
    {Γ : (ι → ℝ) → ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    (τ : ℝ) (z : M × PlanePhase ι) (hn : z.1∉D.chart '' band b)
    (hp : 0 < chartTwoForm (manifoldExteriorOneForm (Γ (planeMoments z.2))) z.1
      (extChartAt 𝓘(ℝ,Plane) z.1 z.1) (1,0) (0,1)) :
    (globalHorizontalCoupling phaseArea (fun v =>
      globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments)
        h ρ ρ₀ (Γ ∘ planeMoments) (τ,v)) z).IsInvertible := by
  have hβ := D.dual_smooth
  let Γ' := toricClosedShift Γ (K-H) (D.dual) τ
  have hs : SmoothOneFormFamily Γ' := toricClosedShift_smooth hΓ (hK.sub hH) hβ τ
  have hp' : 0 < chartTwoForm (manifoldExteriorOneForm (Γ' (planeMoments z.2))) z.1
      (extChartAt 𝓘(ℝ,Plane) z.1 z.1) (1,0) (0,1) := by
    change 0 < chartTwoForm (manifoldExteriorOneForm (toricClosedShift Γ (K-H) (D.dual) τ
      (planeMoments z.2))) z.1 _ _ _
    rw [toricClosedShift_exterior hΓ _ hβ D.dual_closed]
    exact hp
  have heq := globalHorizontalCoupling_congr_germ phaseArea
    (Γ := fun v => globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments)
      h ρ ρ₀ (Γ ∘ planeMoments) (τ,v))
    (Γ' := Γ' ∘ planeMoments) (z := z) (by
      filter_upwards [((D.image_band_compact hbw).isClosed.isOpen_compl).mem_nhds hn] with x hx
      intro v
      exact globalSurfaceSecondPrimitive_off_band D hb Φ (K ∘ planeMoments) (H ∘ planeMoments)
        h ρ ρ₀ hlo hhi (Γ ∘ planeMoments) (τ,v) hx)
  exact heq.symm ▸ globalToricCoupling_isInvertible hs z hp'

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_AnnularSecondPositivity
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

 theorem globalSurfaceSecondPath_isInvertible_bp240_oai {κ : Type*} [Fintype κ]
    (D : AnnularHandleData Plane M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (hor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0 < chartTwoForm Λ c y (1,0) (0,1))
    {r : ℝ} (hr : 0 < r) {γ : ManifoldOneForm Plane M}
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x))
    (hdγ : ∀ x∈D.chart.target,manifoldExteriorOneForm γ x=r • Λ x)
    {Γ : (ι → ℝ) → ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    {K H : (ι → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H) {Y : Set (ι → ℝ)} (hHp : ∀ p∈Y,0≤H p)
    {Kbase : Set M}
    (hbase : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
    (hWA : W⊆D.chart.target)
    (hN : ∀ p x,x∈W→Γ p x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := ι)))
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    {h : κ → PlanePhase ι → ℝ} (hh : ∀ i,ContDiff ℝ ∞ (h i))
    {ρ : κ → ℝ → ℝ} (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (hlo : ∀ s,s ≤ -b →(∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s,b ≤ s →(∀ i,ρ i s=1) ∧ ρ₀ s=1)
    (hclock : ∀ i s,0≤deriv (ρ i) s) (hclock₀ : ∀ s,0≤deriv ρ₀ s)
    (hcap : ∀ v,planeMoments v∈Y→∀ i,0≤h i v)
    (hres : ∀ v,planeMoments v∈Y→0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments) h (Φ.map 1).symm v)
    {τ : ℝ} (hτ : τ∈Icc (0:ℝ) 1) {z : M × PlanePhase ι} (hz : z∈Kbase ×ˢ (planeMoments ⁻¹' Y)) :
    (globalHorizontalCoupling phaseArea (fun v =>
      globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments) h ρ ρ₀
        (Γ ∘ planeMoments) (τ,v)) z).IsInvertible := by
  by_cases hband : z.1∈D.chart '' band b
  · obtain ⟨q,hq,heq⟩ := D.handleAnnularCover_surjOn (hWA (hBW hband))
    have hS := intervalClock_bounds (-b) b q.1
    have hv := (hΦ _ hS).1 hz.2
    have hm := (hΦ 1 (by norm_num)).2 hv
    have hi := globalSurfaceSecondPath_isInvertible_annular_bp240 phaseArea_isInvertible phaseArea_skew
      D hb hbw Φ (hK.comp planeMoments_smooth) (hH.comp planeMoments_smooth)
      hh hρ hρ₀ hlo hhi (hΓ.comp planeMoments_smooth) hγ hW
      (fun v x hx => hN (planeMoments v) x hx) τ hτ (q,z.2) hq (heq.symm ▸ hBW hband)
      (D.annularCover_positive_exterior hor hΛ hsΛ hpΛ hr hdγ hq) (D.clock_nonneg _) (hHp _ hm)
      (fun i => hclock i q.1) (hclock₀ q.1) (hcap _ hv) (hres _ hv)
    simpa only [heq,Prod.mk.eta] using hi
  · exact globalSurfaceSecondPrimitive_isInvertible_outside D hb hbw Φ hK hH h ρ ρ₀ hlo hhi
      hΓ τ z hband (hbase _ hz.2 _ hz.1)

end

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_bp240_oai.{u_1, u_2, u_3} := @OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_bp240_oai.{u_1, u_2, u_3}
