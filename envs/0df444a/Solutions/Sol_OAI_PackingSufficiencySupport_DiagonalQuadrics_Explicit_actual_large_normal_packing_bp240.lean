-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_large_normal_packing_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:45.887848+00:00
-- url     : https://prove2.me/submissions/4428eac9-d69b-4f51-a145-be984a145570

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_exists_actual_compact_normalized_dual_fixed_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_largeHorizontalPrimitive_area_limit_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_MomentPolytope_Annular_exhausted_surface_packing_bp240

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

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

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

theorem vector_chartTwoForm (Ω : E → E →L[ℝ] E →L[ℝ] ℝ) (c y : E) :
    chartTwoForm Ω c y=Ω y := by
  ext v w
  simp only [chartTwoForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,id_eq,
    ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.id_apply]

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

theorem curveFSPrimitive_smooth (c : ℝ) :
    SmoothOneFormFamily (fun _ : ℝ => curveFSPrimitive a c) := by
  have hα : SmoothOneFormFamily (fun _ : ℝ =>
      (affineFSPrimitive c : PlanePhase (Option (Fin m)) → _)) :=
    vector_oneForm_smooth (affineFSPrimitive_smooth c)
  intro b
  exact manifoldPullbackOneForm_smooth (α := fun _ : ℝ =>
    (affineFSPrimitive c : PlanePhase (Option (Fin m)) → _))
    (phaseInclusion_smooth a) hα b

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

namespace PackingSufficiencySupport
open scoped BigOperators
open Set MeasureTheory

theorem momentSimplex_isClosed (m : ℕ) (h : ℝ) : IsClosed (momentSimplex m h) := by
  have h₁ : IsClosed {p : Fin m → ℝ | ∀ i, 0 ≤ p i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact h₁.inter (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

theorem momentSimplex_isCompact (m : ℕ) (h : ℝ) : IsCompact (momentSimplex m h) := by
  refine (isCompact_Icc (a := (fun _ : Fin m => (0:ℝ))) (b := fun _ => h)).of_isClosed_subset (momentSimplex_isClosed m h) ?_
  intro p hp
  refine ⟨hp.1,fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)).trans hp.2

theorem momentSimplex_cons {m : ℕ} (h t : ℝ) (p : Fin m → ℝ) :
    Fin.cons t p ∈ momentSimplex (m+1) h ↔ 0 ≤ t ∧ p ∈ momentSimplex m (h-t) := by
  simp only [momentSimplex,mem_ofPred_eq,Fin.forall_fin_succ,Fin.cons_zero,
    Fin.cons_succ,Fin.sum_univ_succ]
  constructor
  · rintro ⟨⟨ht,hp⟩,hs⟩
    exact ⟨ht,hp,by linarith⟩
  · rintro ⟨ht,hp,hs⟩
    exact ⟨⟨ht,hp⟩,by linarith⟩

theorem integrable_simplex_power (m k : ℕ) (h : ℝ) :
    Integrable ((momentSimplex m h).indicator (fun p => (h-∑ i,p i)^k)) := by
  apply (integrable_indicator_iff (momentSimplex_isClosed m h).measurableSet).2
  exact (((continuous_const.sub (continuous_finsetSum _ fun i _ => continuous_apply i)).pow k).continuousOn).integrableOn_compact (momentSimplex_isCompact m h)

theorem simplex_power_cons {m k : ℕ} (h t : ℝ) (p : Fin m → ℝ) :
    (momentSimplex (m+1) h).indicator (fun q => (h-∑ i,q i)^k) (Fin.cons t p) =
      (Icc 0 h).indicator (fun s => (momentSimplex m (h-s)).indicator
        (fun q => (h-s-∑ i,q i)^k) p) t := by
  by_cases ht : t ∈ Icc 0 h
  · rw [indicator_of_mem ht]
    by_cases hp : p ∈ momentSimplex m (h-t)
    · rw [indicator_of_mem hp,indicator_of_mem ((momentSimplex_cons h t p).2 ⟨ht.1,hp⟩)]
      congr 1
      simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
      ring
    · rw [indicator_of_notMem hp,indicator_of_notMem (by
        intro hh; exact hp ((momentSimplex_cons h t p).1 hh).2)]
  · rw [indicator_of_notMem ht,indicator_of_notMem (by
      intro hh
      obtain ⟨ht0,hp⟩ := (momentSimplex_cons h t p).1 hh
      have hs : 0 ≤ ∑ i,p i := Finset.sum_nonneg fun i _ => hp.1 i
      exact ht ⟨ht0,by linarith [hp.2]⟩)]

theorem integral_simplex_power_step (m k : ℕ) (h : ℝ) :
    (∫ p in momentSimplex (m+1) h, (h-∑ i,p i)^k) =
      ∫ t in Icc 0 h, ∫ p in momentSimplex m (h-t), (h-t-∑ i,p i)^k := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm
  let f := (momentSimplex (m+1) h).indicator (fun p => (h-∑ i,p i)^k)
  have hi : Integrable (f ∘ e) := (he.integrable_comp_emb e.measurableEmbedding).2
    (integrable_simplex_power (m+1) k h)
  rw [←integral_indicator (momentSimplex_isClosed (m+1) h).measurableSet]
  change (∫ p, f p) = _
  rw [←he.integral_comp e.measurableEmbedding]
  change (∫ x, (f ∘ e) x ∂(volume.prod volume)) = _
  rw [integral_prod _ hi]
  have hes (x : ℝ × (Fin m → ℝ)) : e x = Fin.cons x.1 x.2 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  simp only [Function.comp_apply,hes,f,simplex_power_cons]
  rw [←integral_indicator measurableSet_Icc]
  congr 1
  funext t
  by_cases ht : t ∈ Icc 0 h
  · simp only [indicator_of_mem ht]
    exact integral_indicator (momentSimplex_isClosed m (h-t)).measurableSet
  · simp [ht]

theorem integral_simplex_power (m k : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ p in momentSimplex m h, (h-∑ i,p i)^k) =
      (k.factorial : ℝ) / ((m+k).factorial : ℝ) * h^(m+k) := by
  induction m generalizing h with
  | zero =>
    have hv : (volume : Measure (Fin 0 → ℝ)) univ = 1 := Measure.pi_empty_univ _
    have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
    simp [momentSimplex,hh,hv,measureReal_def,hfac]
  | succ m ih =>
    rw [integral_simplex_power_step]
    have hc : (∫ t in Icc 0 h, ∫ p in momentSimplex m (h-t), (h-t-∑ i,p i)^k) =
        ∫ t in Icc 0 h, (k.factorial : ℝ) / ((m+k).factorial : ℝ) * (h-t)^(m+k) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact ih (by linarith [ht.2])
    rw [hc,integral_const_mul,integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le hh,
      intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^(m+k)) h]
    rw [sub_self,sub_zero,integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero _),sub_zero]
    rw [show m+1+k=m+k+1 by omega,Nat.factorial_succ,Nat.cast_mul]
    simp only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_inv_rev]
    ring

theorem volumeReal_momentSimplex (m : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    volume.real (momentSimplex m h) = h^m / (m.factorial : ℝ) := by
  simpa [div_eq_mul_inv,mul_comm] using integral_simplex_power m 0 hh

theorem integral_simplex_tent (m : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ p in momentSimplex m h, (h-∑ i,p i)) = h^(m+1) / ((m+1).factorial : ℝ) := by
  simpa [div_eq_mul_inv,mul_comm] using integral_simplex_power m 1 hh

theorem tent_indicator_eq {m : ℕ} {r : ℝ} {D : Set (Fin m → ℝ)}
    (hD : ∀ p ∈ D, ∀ i, 0 ≤ p i) (hcap : momentSimplex m r ⊆ D) :
    D.indicator (fun p => max (r-∑ i,p i) 0) =
      (momentSimplex m r).indicator (fun p => r-∑ i,p i) := by
  funext p
  by_cases hp : p ∈ momentSimplex m r
  · rw [indicator_of_mem hp,indicator_of_mem (hcap hp),max_eq_left (sub_nonneg.mpr hp.2)]
  · rw [indicator_of_notMem hp]
    by_cases hd : p ∈ D
    · rw [indicator_of_mem hd,max_eq_right]
      exact le_of_lt (sub_neg.mpr (lt_of_not_ge (fun hs => hp ⟨hD p hd,hs⟩)))
    · exact indicator_of_notMem hd _

theorem integrableOn_tent {m : ℕ} {r : ℝ} {D : Set (Fin m → ℝ)}
    (hDmeas : MeasurableSet D) (hD : ∀ p ∈ D, ∀ i, 0 ≤ p i)
    (hcap : momentSimplex m r ⊆ D) :
    IntegrableOn (fun p => max (r-∑ i,p i) 0) D := by
  rw [←integrable_indicator_iff hDmeas,tent_indicator_eq hD hcap]
  simpa using integrable_simplex_power m 1 r

theorem integral_tent {m : ℕ} {r : ℝ} (hr : 0 ≤ r) {D : Set (Fin m → ℝ)}
    (hDmeas : MeasurableSet D) (hD : ∀ p ∈ D, ∀ i, 0 ≤ p i)
    (hcap : momentSimplex m r ⊆ D) :
    (∫ p in D, max (r-∑ i,p i) 0) = r^(m+1) / ((m+1).factorial : ℝ) := by
  rw [←integral_indicator hDmeas,tent_indicator_eq hD hcap,
    integral_indicator (momentSimplex_isClosed m r).measurableSet]
  exact integral_simplex_tent m hr

theorem integral_sum_tents {m : ℕ} {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) {D : Set (Fin m → ℝ)}
    (hDmeas : MeasurableSet D) (hD : ∀ p ∈ D, ∀ j, 0 ≤ p j)
    (hcap : ∀ i, momentSimplex m (r i) ⊆ D) :
    (∫ p in D, ∑ i, max (r i-∑ j,p j) 0) =
      (∑ i,r i^(m+1)) / ((m+1).factorial : ℝ) := by
  rw [integral_finsetSum _ (fun i _ => integrableOn_tent hDmeas hD (hcap i))]
  simp_rw [integral_tent (hr _) hDmeas hD (hcap _)]
  exact (Finset.sum_div _ _ _).symm

theorem continuous_smallModelMean (m : ℕ) : Continuous (smallModelMean m) := by
  unfold smallModelMean
  fun_prop

theorem smallModelMean_half (m : ℕ) : smallModelMean m (1/2) =
    1 / ((m+1).factorial : ℝ) := by
  have hp : (2:ℝ)^m*(1/2)^m=1 := by rw [←mul_pow]; norm_num
  dsimp [smallModelMean]
  rw [hp,Nat.factorial_succ,Nat.cast_mul]
  simp only [Nat.cast_add,Nat.cast_one]
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  have hm : (m:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem concaveOn_cappedAffine {m : ℕ} {ι : Type*} [Fintype ι]
    (A : ℝ) (B : Fin m → ℝ) (r w : ι → ℝ) (hw : ∀ i,0 ≤ w i)
    {D : Set (Fin m → ℝ)} (hD : Convex ℝ D) : ConcaveOn ℝ D (cappedAffine A B r w) := by
  refine ⟨hD,?_⟩
  intro x hx y hy a b ha hb hab
  have hsum : (∑ j,(a • x+b • y) j)=a*(∑ j,x j)+b*(∑ j,y j) := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,Finset.mul_sum]
  have hB : (∑ j,B j*(a • x+b • y) j)=a*(∑ j,B j*x j)+b*(∑ j,B j*y j) := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  have hcap (i : ι) : max (r i-∑ j,(a • x+b • y) j) 0 ≤
      a*max (r i-∑ j,x j) 0+b*max (r i-∑ j,y j) 0 := by
    apply max_le
    · rw [hsum]
      have hx := mul_le_mul_of_nonneg_left (le_max_left (r i-∑ j,x j) 0) ha
      have hy := mul_le_mul_of_nonneg_left (le_max_left (r i-∑ j,y j) 0) hb
      have he := congrArg (fun t : ℝ => t*r i) hab
      nlinarith only [hx,hy,he]
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hcap i) (hw i))
  have he : (∑ i,w i*(a*max (r i-∑ j,x j) 0+b*max (r i-∑ j,y j) 0)) =
      a*(∑ i,w i*max (r i-∑ j,x j) 0)+b*(∑ i,w i*max (r i-∑ j,y j) 0) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  rw [he] at hc
  have hA : a*A+b*A=A := by rw [←add_mul,hab,one_mul]
  dsimp [cappedAffine]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hB hc
  rw [hB]
  nlinarith only [hA,hc]

end PackingSufficiencySupport
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

theorem exists_rational_below_in_open {ι : Type*} [Fintype ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) {r : ι → ℝ} (hr : r ∈ U) :
    ∃ q : ι → ℚ, (∀ i, (q i : ℝ) < r i) ∧ (fun i => (q i : ℝ)) ∈ U := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.1 hU r hr
  have hinterval (i : ι) : ∃ q : ℚ, r i-ε/2 < q ∧ (q : ℝ) < r i :=
    exists_rat_btwn (by linarith)
  choose q hlo hhi using hinterval
  refine ⟨q,hhi,hball ?_⟩
  rw [Metric.mem_ball]
  apply (dist_pi_lt_iff hε).2
  intro i
  rw [Real.dist_eq,abs_of_neg (sub_neg.mpr (hhi i))]
  linarith [hlo i]

theorem rational_truncation_2d (F : ℝ×ℝ → ℝ) (hF : Continuous F)
    {s₁ s₂ l c : ℝ} (hl₁ : l < s₁) (hl₂ : l < s₂) (hc : c<F (s₁,s₂)) :
    ∃ h₁ h₂ d₁ d₂ : ℚ,
      l<h₁ ∧ h₁<d₁ ∧ (d₁:ℝ) < s₁ ∧
      l<h₂ ∧ h₂<d₂ ∧ (d₂:ℝ) < s₂ ∧ c<F (h₁,h₂) := by
  let U : Set (Fin 2 → ℝ) := {p | l<p 0 ∧ l<p 1 ∧ c<F (p 0,p 1)}
  have hU : IsOpen U := (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_lt continuous_const (hF.comp ((continuous_apply 0).prodMk (continuous_apply 1)))))
  let r : Fin 2 → ℝ := ![s₁,s₂]
  have hr : r∈U := ⟨hl₁,hl₂,hc⟩
  obtain ⟨h,hlt,hmem⟩ := exists_rational_below_in_open hU hr
  have hh₁ : (h 0:ℝ) < s₁ := hlt 0
  have hh₂ : (h 1:ℝ) < s₂ := hlt 1
  obtain ⟨d₁,hd₁,hs₁⟩ := exists_rat_btwn hh₁
  obtain ⟨d₂,hd₂,hs₂⟩ := exists_rat_btwn hh₂
  exact ⟨h 0,h 1,d₁,d₂,hmem.1,by exact_mod_cast hd₁,hs₁,
    hmem.2.1,by exact_mod_cast hd₂,hs₂,hmem.2.2⟩

end PackingSufficiencySupport

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_CubicPhysicalLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped BigOperators
open MeasureTheory Set
open scoped Pointwise
open MomentPolytope

theorem continuous_momentHeadTail_symm (q : ℕ) : Continuous (momentHeadTail q).symm := by
  change Continuous (fun x : ℝ×(Fin q → ℝ) => (momentHeadTail q).symm x)
  simp_rw [momentHeadTail_symm_apply]
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Fin.cons_zero,Fin.cons_succ] <;> fun_prop

theorem isCompact_preimage_momentHeadTail (q : ℕ) {D : Set (ℝ×(Fin q → ℝ))}
    (hD : IsCompact D) : IsCompact ((momentHeadTail q) ⁻¹' D) := by
  have he : (momentHeadTail q) ⁻¹' D = (momentHeadTail q).symm '' D := by
    ext p
    constructor
    · intro hp
      exact ⟨momentHeadTail q p,hp,(momentHeadTail q).symm_apply_apply p⟩
    · rintro ⟨x,hx,rfl⟩
      simpa using hx
  rw [he]
  exact hD.image (continuous_momentHeadTail_symm q)

theorem integral_momentHeadTail (q : ℕ) {D : Set (ℝ×(Fin q → ℝ))}
    (hD : MeasurableSet D) (f : ℝ×(Fin q → ℝ) → ℝ) :
    (∫ p in (momentHeadTail q) ⁻¹' D, f (momentHeadTail q p)) = ∫ x in D,f x := by
  let e := momentHeadTail q
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ : Fin (q+1) => ℝ) 0
  rw [←integral_indicator (hD.preimage e.measurable),←integral_indicator hD]
  have hf : (e ⁻¹' D).indicator (fun p => f (e p)) = (D.indicator f) ∘ e := by
    funext p
    by_cases hp : e p∈D <;> simp [hp]
  rw [hf]
  exact he.integral_comp e.measurableEmbedding _

end PackingSufficiencySupport

namespace PackingSufficiencySupport
open Set
open scoped BigOperators Pointwise
open MomentPolytope

theorem cap_into_scaled_region {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν j,b ν j ≤ 1) {τ r : ℝ} (hτ : 0 < τ)
    (hr : ∀ ν,r ≤ τ*c ν) : momentSimplex m r ⊆ τ • region b c := by
  intro p hp
  let q := τ⁻¹ • p
  have hq (j : Fin m) : 0 ≤ q j := mul_nonneg (inv_nonneg.2 hτ.le) (hp.1 j)
  have hsum : (∑ j,q j) ≤ τ⁻¹*r := by
    simpa only [q,Pi.smul_apply,smul_eq_mul,←Finset.mul_sum] using
      mul_le_mul_of_nonneg_left hp.2 (inv_nonneg.2 hτ.le)
  refine ⟨q,⟨hq,fun ν => ?_⟩,?_⟩
  · have hweighted : (∑ j,b ν j*q j) ≤ ∑ j,q j := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb ν j) (hq j)
    have hc : τ⁻¹*r ≤ c ν := by
      have ht := mul_le_mul_of_nonneg_left (hr ν) (inv_nonneg.2 hτ.le)
      simpa only [←mul_assoc,inv_mul_cancel₀ hτ.ne',one_mul] using ht
    exact hweighted.trans (hsum.trans hc)
  · simp [q,smul_smul,hτ.ne']

theorem sum_caps_zero_outside {m : ℕ} {ι : Type*} [Fintype ι]
    (r : ι → ℝ) {D A : Set (Fin m → ℝ)}
    (hD : ∀ p ∈ D,∀ j,0 ≤ p j) (hcap : ∀ i,momentSimplex m (r i) ⊆ A)
    {p : Fin m → ℝ} (hp : p ∈ D) (hout : p ∉ A) :
    (∑ i,max (r i-∑ j,p j) 0)=0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply max_eq_right
  have hn : ¬ (∑ j,p j) ≤ r i := fun he => hout (hcap i ⟨hD p hp,he⟩)
  linarith [not_le.1 hn]

end PackingSufficiencySupport
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_LiouvilleRadialCalculus
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped BigOperators
open MeasureTheory Set
open scoped Pointwise
open MomentPolytope

theorem largeMomentDomain_isClosed (q : ℕ) (h₁ h₂ : ℝ) :
    IsClosed (largeMomentDomain q h₁ h₂) := by
  have hn : IsClosed {x : ℝ × (Fin q → ℝ) | ∀ i,0≤x.2 i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)
  exact (isClosed_Icc.preimage continuous_fst).inter (hn.inter
    (isClosed_le (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_snd)
      (continuous_const.mul (continuous_const.sub continuous_fst))))

theorem largeMomentDomain_isCompact (q : ℕ) (h₁ : ℝ) {h₂ : ℝ} (hh₂ : 0 ≤ h₂) :
    IsCompact (largeMomentDomain q h₁ h₂) := by
  refine (isCompact_Icc (a := (0,fun _ : Fin q => (0:ℝ)))
    (b := (h₁,fun _ => h₂))).of_isClosed_subset (largeMomentDomain_isClosed q h₁ h₂) ?_
  intro x hx
  refine ⟨⟨hx.1.1,hx.2.1⟩,hx.1.2,fun i => ?_⟩
  have hi := (Finset.single_le_sum (fun j _ => hx.2.1 j) (Finset.mem_univ i)).trans hx.2.2
  have hu : h₂*(1-x.1)≤h₂ := by nlinarith [hx.1.1]
  exact hi.trans hu

theorem integral_scaled_small_model (q : ℕ) {h A : ℝ} (hh : 0≤h) (hA : 0≤A) :
    (∫ p in momentSimplex q (h*A), (2:ℝ)^q*(A-2*∑ i,p i)) =
      smallModelMean q h * A^(q+1) := by
  have ht : IntegrableOn (fun p : Fin q → ℝ => h*A-∑ i,p i) (momentSimplex q (h*A)) :=
    ((continuous_const.sub (continuous_finsetSum _ fun i _ => continuous_apply i)).continuousOn).integrableOn_compact (momentSimplex_isCompact q (h*A))
  have hc : IntegrableOn (fun _ : Fin q → ℝ => A-2*(h*A)) (momentSimplex q (h*A)) :=
    continuousOn_const.integrableOn_compact (momentSimplex_isCompact q (h*A))
  have heq (p : Fin q → ℝ) : A-2*∑ i,p i = (A-2*(h*A))+2*(h*A-∑ i,p i) := by ring
  simp_rw [heq]
  rw [integral_const_mul,integral_add hc (ht.const_mul 2),integral_const_mul,
    setIntegral_const,integral_simplex_tent q (mul_nonneg hh hA)]
  simp only [smul_eq_mul,volumeReal_momentSimplex q (mul_nonneg hh hA)]
  dsimp [smallModelMean]
  rw [Nat.factorial_succ,Nat.cast_mul]
  simp only [Nat.cast_add,Nat.cast_one,pow_succ,mul_pow]
  have hf : (q.factorial : ℝ) ≠ 0 := by positivity
  have hq : (q:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem integral_large_model (q : ℕ) {h₁ h₂ : ℝ}
    (hh₁ : 0≤h₁) (hh₁' : h₁≤1) (hh₂ : 0≤h₂) :
    (∫ x in largeMomentDomain q h₁ h₂, (2:ℝ)^q*(1-x.1-2*∑ i,x.2 i)) =
      largeModelMean q h₁ h₂ := by
  let D := largeMomentDomain q h₁ h₂
  let f : ℝ × (Fin q → ℝ) → ℝ := fun x => (2:ℝ)^q*(1-x.1-2*∑ i,x.2 i)
  have hD := (largeMomentDomain_isClosed q h₁ h₂).measurableSet
  have hf : IntegrableOn f D := ContinuousOn.integrableOn_compact
    (largeMomentDomain_isCompact q h₁ hh₂) (by dsimp [f]; fun_prop)
  have hi : Integrable (D.indicator f) := (integrable_indicator_iff hD).2 hf
  rw [←integral_indicator hD]
  change (∫ x, D.indicator f x ∂(volume.prod volume)) = _
  rw [integral_prod _ hi]
  have slice (u : ℝ) : (∫ p, D.indicator f (u,p)) =
      (Icc 0 h₁).indicator (fun u => ∫ p in momentSimplex q (h₂*(1-u)),
        (2:ℝ)^q*(1-u-2*∑ i,p i)) u := by
    by_cases hu : u ∈ Icc 0 h₁
    · rw [indicator_of_mem hu,←integral_indicator (momentSimplex_isClosed q (h₂*(1-u))).measurableSet]
      congr 1
      funext p
      by_cases hp : p∈momentSimplex q (h₂*(1-u))
      · rw [indicator_of_mem (show (u,p)∈D from ⟨hu,hp⟩),indicator_of_mem hp]
      · rw [indicator_of_notMem (show (u,p)∉D from fun hx => hp hx.2),indicator_of_notMem hp]
    · rw [indicator_of_notMem hu]
      have hz (p : Fin q → ℝ) : D.indicator f (u,p)=0 :=
        indicator_of_notMem (show (u,p)∉D from fun hx => hu hx.1) f
      simp_rw [hz]
      exact integral_zero _ _
  simp_rw [slice]
  rw [integral_indicator measurableSet_Icc]
  have heq : (∫ u in Icc 0 h₁, ∫ p in momentSimplex q (h₂*(1-u)),
      (2:ℝ)^q*(1-u-2*∑ i,p i)) =
      ∫ u in Icc 0 h₁, smallModelMean q h₂*(1-u)^(q+1) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact integral_scaled_small_model q hh₂ (by linarith [hu.2])
  rw [heq,integral_const_mul,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le hh₁,
    intervalIntegral.integral_comp_sub_left (fun u : ℝ => u^(q+1)) 1,
    sub_zero,integral_pow]
  simp only [one_pow]
  simp only [largeModelMean,Nat.cast_add,Nat.cast_one]
  rw [show q+1+1=q+2 by omega,show (q:ℝ)+1+1=(q:ℝ)+2 by ring]
  ring

theorem continuous_largeModelMean (q : ℕ) :
    Continuous (fun h : ℝ×ℝ => largeModelMean q h.1 h.2) := by
  unfold largeModelMean
  exact ((continuous_smallModelMean q).comp continuous_snd).mul
    (continuous_const.sub ((continuous_const.sub continuous_fst).pow (q+2))) |>.div_const _

theorem largeModelMean_limit_value (q : ℕ) (a : ℝ) :
    largeModelMean q (1-a) (1/2) = (1-a^(q+2))/((q+2).factorial : ℝ) := by
  unfold largeModelMean
  rw [smallModelMean_half]
  have ha : 1-(1-a)=a := by ring
  rw [ha]
  have hf : ((q+2).factorial : ℝ)=((q:ℝ)+2)*((q+1).factorial : ℝ) := by
    rw [show q+2=(q+1)+1 by omega,Nat.factorial_succ,Nat.cast_mul]
    push_cast
    ring
  rw [hf]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem largeModelBounds_nonneg (q : ℕ) {h₂ : ℝ} (hh₂ : 0 ≤ h₂) :
    ∀ ν i,0 ≤ largeModelBounds q h₂ ν i := by
  intro ν i
  fin_cases ν <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [largeModelBounds,hh₂]

theorem largeModelRegion_eq (q : ℕ) (h₁ h₂ : ℝ) :
    region (largeModelBounds q h₂) ![h₁,h₂] =
      (momentHeadTail q) ⁻¹' largeMomentDomain q h₁ h₂ := by
  ext p
  have hrow0 : (∑ j,largeModelBounds q h₂ 0 j*p j)=p 0 := by
    simp [largeModelBounds,Fin.sum_univ_succ]
  have hrow1 : (∑ j,largeModelBounds q h₂ 1 j*p j)=h₂*p 0+∑ j : Fin q,p j.succ := by
    simp [largeModelBounds,Fin.sum_univ_succ]
  change ((∀ j,0≤p j) ∧ ∀ ν,∑ j,largeModelBounds q h₂ ν j*p j ≤ ![h₁,h₂] ν) ↔
    (p 0∈Icc 0 h₁ ∧ (fun j : Fin q => p j.succ)∈momentSimplex q (h₂*(1-p 0)))
  constructor
  · rintro ⟨hp,hbound⟩
    have h0 := hbound 0
    have h1 := hbound 1
    rw [hrow0] at h0
    rw [hrow1] at h1
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
    exact ⟨⟨hp 0,h0⟩,fun j => hp j.succ,by linarith⟩
  · rintro ⟨⟨hp,hh₁⟩,hp',hh₂⟩
    refine ⟨fun j => Fin.cases hp hp' j,fun ν => ?_⟩
    fin_cases ν
    · change (∑ j,largeModelBounds q h₂ 0 j*p j) ≤ h₁
      rw [hrow0]
      exact hh₁
    · change (∑ j,largeModelBounds q h₂ 1 j*p j) ≤ h₂
      rw [hrow1]
      linarith

theorem largeModelRegion_isCompact (q : ℕ) (h₁ : ℝ) {h₂ : ℝ} (hh₂ : 0 ≤ h₂) :
    IsCompact (region (largeModelBounds q h₂) ![h₁,h₂]) := by
  rw [largeModelRegion_eq]
  exact isCompact_preimage_momentHeadTail q (largeMomentDomain_isCompact q h₁ hh₂)

theorem largeModelRegion_contains_cap (q : ℕ) {r h₁ h₂ : ℝ}
    (hr₁ : r ≤ h₁) (hr₂ : r ≤ h₂) (hh₂ : h₂ ≤ 1) :
    momentSimplex (q+1) r ⊆ region (largeModelBounds q h₂) ![h₁,h₂] := by
  rw [largeModelRegion_eq]
  intro p hp
  change p 0∈Icc 0 h₁ ∧ (fun j : Fin q => p j.succ)∈momentSimplex q (h₂*(1-p 0))
  have hsum : p 0+∑ j : Fin q,p j.succ ≤ r := by simpa only [Fin.sum_univ_succ] using hp.2
  have htail : 0 ≤ ∑ j : Fin q,p j.succ := Finset.sum_nonneg fun j _ => hp.1 j.succ
  refine ⟨⟨hp.1 0,by linarith⟩,fun j => hp.1 j.succ,?_⟩
  have hu := mul_le_mul_of_nonneg_right hh₂ (hp.1 0)
  dsimp
  linarith

theorem integral_largeModelDensity (q : ℕ) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁' : h₁ ≤ 1) (hh₂ : 0 ≤ h₂) :
    (∫ p in region (largeModelBounds q h₂) ![h₁,h₂], largeModelDensity q p) =
      largeModelMean q h₁ h₂ := by
  rw [largeModelRegion_eq]
  have heq : largeModelDensity q =
      (fun x : ℝ×(Fin q→ℝ) => (2:ℝ)^q*(1-x.1-2*∑ j,x.2 j)) ∘ momentHeadTail q := rfl
  rw [heq]
  simp only [Function.comp_apply]
  rw [integral_momentHeadTail q (largeMomentDomain_isClosed q h₁ h₂).measurableSet
    (fun x : ℝ×(Fin q→ℝ) => (2:ℝ)^q*(1-x.1-2*∑ j,x.2 j))]
  exact integral_large_model q hh₁ hh₁' hh₂

theorem integral_largeModelGap {q : ℕ} {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i,0 ≤ r i) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁' : h₁ ≤ 1) (hh₂ : 0 ≤ h₂) (hh₂' : h₂ ≤ 1)
    (hr₁ : ∀ i,r i ≤ h₁) (hr₂ : ∀ i,r i ≤ h₂) :
    (∫ p in region (largeModelBounds q h₂) ![h₁,h₂], largeModelGap r p) =
      largeModelMean q h₁ h₂-(∑ i,r i^(q+2))/((q+2).factorial : ℝ) := by
  have hC := largeModelRegion_isCompact q h₁ hh₂
  have hcap (i : ι) := largeModelRegion_contains_cap q (hr₁ i) (hr₂ i) hh₂'
  unfold largeModelGap
  rw [integral_sub]
  · rw [integral_largeModelDensity q hh₁ hh₁' hh₂,
      integral_sum_tents r hr hC.measurableSet (fun _ hp => hp.1) hcap]
  · apply ContinuousOn.integrableOn_compact hC
    unfold largeModelDensity
    fun_prop
  · apply ContinuousOn.integrableOn_compact hC
    fun_prop

theorem largeModelGap_eq_cappedAffine {q : ℕ} {ι : Type*} [Fintype ι]
    (r : ι → ℝ) : @largeModelGap q ι _ r =
      cappedAffine ((2:ℝ)^q) (Fin.cons ((2:ℝ)^q) (fun _ => (2:ℝ)^q*2)) r (fun _ => 1) := by
  funext p
  simp only [largeModelGap,largeModelDensity,cappedAffine,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ,one_mul,←Finset.mul_sum]
  ring

theorem largeModelDensity_lower (q : ℕ) {h₁ h₂ : ℝ} (hh₂ : h₂ ≤ 1/2)
    {p : Moments (q+1)} (hp : p ∈ region (largeModelBounds q h₂) ![h₁,h₂]) :
    (2:ℝ)^q*(1-h₁)*(1-2*h₂) ≤ largeModelDensity q p := by
  rw [largeModelRegion_eq] at hp
  change p 0∈Icc 0 h₁ ∧ (fun j => p j.succ)∈momentSimplex q (h₂*(1-p 0)) at hp
  have he : (1-h₁)*(1-2*h₂) ≤ 1-p 0-2*∑ j : Fin q,p j.succ := by
    have hm := mul_le_mul_of_nonneg_right (show 1-h₁ ≤ 1-p 0 by linarith [hp.1.2])
      (show 0 ≤ 1-2*h₂ by linarith)
    nlinarith [hp.2.2]
  unfold largeModelDensity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ 2^q)

theorem exists_large_model_comparison_data {q : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ι → ℝ) (hr : ∀ i,0 < r i) {a : ℝ} (ha : 0<a) (_ha1 : a<1)
    (hrs : ∀ i,r i<1-a) (hrhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(q+2)<1-a^(q+2)) :
    ∃ h₁ h₂ d₁ d₂ : ℚ, ∃ τ ε : ℝ,
      (∀ i,r i<h₁) ∧ h₁<d₁ ∧ (d₁:ℝ)<1-a ∧
      (∀ i,r i<h₂) ∧ h₂<d₂ ∧ (d₂:ℝ)<1/2 ∧
      0<(h₁:ℝ) ∧ 0<(h₂:ℝ) ∧ 0<τ ∧ τ<1 ∧ 0<ε ∧
      (∀ i,momentSimplex (q+1) (r i) ⊆ τ • region (largeModelBounds q h₂) ![h₁,h₂]) ∧
      ConcaveOn ℝ (region (largeModelBounds q h₂) ![h₁,h₂]) (largeModelGap r) ∧
      (0 < ∫ p in region (largeModelBounds q h₂) ![h₁,h₂], largeModelGap r p) ∧
      ∀ p ∈ region (largeModelBounds q h₂) ![h₁,h₂],
        p ∉ τ • region (largeModelBounds q h₂) ![h₁,h₂] → ε ≤ largeModelGap r p := by
  classical
  let S := Finset.univ.image r
  have hS : S.Nonempty := Finset.image_nonempty.2 Finset.univ_nonempty
  let R := S.max' hS
  have hR (i : ι) : r i ≤ R := Finset.le_max' S (r i) (Finset.mem_image_of_mem r (Finset.mem_univ i))
  have hRs : R<1-a := (Finset.max'_lt_iff S hS).2 (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 hx
    exact hrs i)
  have hRhalf : R<1/2 := (Finset.max'_lt_iff S hS).2 (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 hx
    exact hrhalf i)
  have hRpos : 0<R := (hr (Classical.arbitrary ι)).trans_le (hR _)
  have hfac : (0:ℝ)<((q+2).factorial : ℝ) := by positivity
  have hlim : (∑ i,r i^(q+2))/((q+2).factorial : ℝ)<largeModelMean q (1-a) (1/2) := by
    rw [largeModelMean_limit_value]
    exact div_lt_div_of_pos_right hvol hfac
  obtain ⟨h₁,h₂,d₁,d₂,hRh₁,hhd₁,hd₁,hRh₂,hhd₂,hd₂,hmean⟩ :=
    rational_truncation_2d (fun h => largeModelMean q h.1 h.2)
      (continuous_largeModelMean q) hRs hRhalf hlim
  have hh₁ : (0:ℝ)<h₁ := hRpos.trans hRh₁
  have hh₂ : (0:ℝ)<h₂ := hRpos.trans hRh₂
  have hh₁s : (h₁:ℝ)<1-a := (by exact_mod_cast hhd₁ : (h₁:ℝ)<d₁).trans hd₁
  have hh₂half : (h₂:ℝ)<1/2 := (by exact_mod_cast hhd₂ : (h₂:ℝ)<d₂).trans hd₂
  have hratio : max (R/(h₁:ℝ)) (R/(h₂:ℝ))<1 := max_lt
    ((div_lt_one hh₁).2 hRh₁) ((div_lt_one hh₂).2 hRh₂)
  obtain ⟨τ,hτlo,hτhi⟩ := exists_between hratio
  have hτlo₁ : R/(h₁:ℝ)<τ := (le_max_left _ _).trans_lt hτlo
  have hτlo₂ : R/(h₂:ℝ)<τ := (le_max_right _ _).trans_lt hτlo
  have hτ : 0<τ := (div_pos hRpos hh₁).trans hτlo₁
  have hRτ₁ : R<τ*(h₁:ℝ) := (div_lt_iff₀ hh₁).1 hτlo₁
  have hRτ₂ : R<τ*(h₂:ℝ) := (div_lt_iff₀ hh₂).1 hτlo₂
  let ε := (2:ℝ)^q*(1-(h₁:ℝ))*(1-2*(h₂:ℝ))
  have hε : 0<ε := mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
  have hb : ∀ ν j,largeModelBounds q (h₂:ℝ) ν j ≤ 1 := by
    intro ν j
    fin_cases ν
    · change (@Fin.cons q (fun _ => ℝ) 1 (fun _ => 0)) j ≤ 1
      exact Fin.cases (by norm_num) (fun _ => by norm_num) j
    · change (@Fin.cons q (fun _ => ℝ) (h₂:ℝ) (fun _ => 1)) j ≤ 1
      exact Fin.cases (by simpa using (show (h₂:ℝ) ≤ 1 by linarith)) (fun _ => le_rfl) j
  have hcap (i : ι) : momentSimplex (q+1) (r i) ⊆
      τ • region (largeModelBounds q h₂) ![h₁,h₂] := by
    apply cap_into_scaled_region _ _ hb hτ
    intro ν
    fin_cases ν
    · exact (hR i).trans hRτ₁.le
    · exact (hR i).trans hRτ₂.le
  refine ⟨h₁,h₂,d₁,d₂,τ,ε,fun i => (hR i).trans_lt hRh₁,hhd₁,hd₁,
    fun i => (hR i).trans_lt hRh₂,hhd₂,hd₂,hh₁,hh₂,hτ,hτhi,hε,hcap,?_,?_,?_⟩
  · rw [largeModelGap_eq_cappedAffine]
    exact concaveOn_cappedAffine _ _ _ _ (fun _ => by norm_num) (convex_region _ _)
  · rw [integral_largeModelGap r (fun i => (hr i).le) hh₁.le (by linarith) hh₂.le
      (by linarith) (fun i => (hR i).trans hRh₁.le) (fun i => (hR i).trans hRh₂.le)]
    linarith
  · intro p hp hout
    have hz := sum_caps_zero_outside r (fun _ hp => hp.1) hcap hp hout
    simp only [largeModelGap,hz,sub_zero]
    exact largeModelDensity_lower q hh₂half.le hp

end PackingSufficiencySupport

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open Hamiltonian MomentPolytope

 theorem largeNormalCoefficient_smooth (q : ℕ) : ContDiff ℝ ∞ (largeNormalCoefficient q) := by
  unfold largeNormalCoefficient
  fun_prop

 theorem largeNormalCoefficient_pos {q : ℕ} {h₁ h₂ : ℝ} (hh₁ : h₁<1) (hh₂ : h₂<1/2)
    {p : Fin (q+1) → ℝ} (hp : p∈region (largeModelBounds q h₂) ![h₁,h₂]) :
    0<largeNormalCoefficient q p := by
  have he := largeModelDensity_lower q hh₂.le hp
  have hpos : 0<(2:ℝ)^q*(1-h₁)*(1-2*h₂) :=
    mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
  have hh : 0 < (2:ℝ)^q * largeNormalCoefficient q p := hpos.trans_le he
  exact (mul_pos_iff_of_pos_left (by positivity)).mp hh

 variable {m q : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 attribute [local instance] OAI.PackingSufficiencySupport.DiagonalQuadrics.liouvilleRadialSigmaCompact
theorem largeHorizontalPrimitive_smooth : SmoothOneFormFamily (largeHorizontalPrimitive (q := q) a) :=
  ((curveFSPrimitive_smooth a (1/Real.pi)).comp
    (f := fun _ : Fin (q+1) → ℝ => (0:ℝ)) contDiff_const).smul (largeNormalCoefficient_smooth q)

 theorem largeHorizontalPrimitive_exterior (p : Fin (q+1) → ℝ) (x : locus a) :
    manifoldExteriorOneForm (largeHorizontalPrimitive a p) x=
      largeNormalCoefficient q p • curveFSForm a (1/Real.pi) x := by
  have hx := (extChartAt 𝓘(ℝ,Plane) x).map_source (mem_extChartAt_source x)
  rw [largeHorizontalPrimitive,manifoldExteriorOneForm_smul_at _
    ((curveFSPrimitive_smooth a (1/Real.pi)).spatial_smooth 0 x hx),curveFSPrimitive_exterior]

namespace Explicit

 attribute [local instance] OAI.PackingSufficiencySupport.DiagonalQuadrics.liouvilleRadialSigmaCompact
theorem actual_large_normal_packing_bp240_oai (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) {a₀ : ℝ} (ha₀ : 0<a₀) (ha₁ : a₀<1)
    (hrs : ∀ i,r i<1-a₀) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+4)<1-a₀^(m+4)) :
    ∃ h₁ h₂ d₁ d₂ : ℚ, (∀ i,r i<h₁) ∧ h₁<d₁ ∧ (d₁:ℝ)<1-a₀ ∧
      (∀ i,r i<h₂) ∧ h₂<d₂ ∧ (d₂:ℝ)<1/2 ∧
      ∃ ℓ,∃ φ : Fin N → Ambient (m+4) → Surface m × PlanePhase (Fin (m+3)),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+4) (r' i))
          (fun _ => successorStandardForm (m+3))
          (globalHorizontalCoupling phaseArea
            (largeHorizontalPrimitive (q := m+2) (parameters m) ∘ planeMoments)) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall (m+4) (r' i))
          (interior (projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ) ×ˢ
            planeRegion (largeModelBounds (m+2) h₂) ![h₁,h₂]))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+4) (r' i))
          (φ j '' closedBall (m+4) (r' j))) := by
  classical
  obtain ⟨h₁,h₂,d₁,d₂,τ,ε,hr₁,hhd₁,hd₁,hr₂,hhd₂,hd₂,hh₁,hh₂,hτ,hτ1,hε,
    _hcap,hconc,hmean,houter⟩ := exists_large_model_comparison_data r hr ha₀ ha₁ hrs hhalf hvol
  have hh₁1 : (h₁:ℝ)<1 := lt_trans (show (h₁:ℝ)<(d₁:ℝ) by exact_mod_cast hhd₁) (by linarith)
  have hh₂half : (h₂:ℝ)<1/2 := (show (h₂:ℝ)<d₂ by exact_mod_cast hhd₂).trans hd₂
  let bF := largeModelBounds (m+2) (h₂:ℝ)
  let cF : Fin 2 → ℝ := ![h₁,h₂]
  have hcomp : IsCompact (region bF cF) := largeModelRegion_isCompact (m+2) h₁ hh₂.le
  let K := fun ℓ => projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ)
  have hK ℓ : IsCompact (K ℓ) := projectionDomain_compact (parameters m) _
  have hKn ℓ : K ℓ⊆interior (K (ℓ+1)) := by
    apply projectionDomain_nested
    simp only [exhaustionRadius,Nat.cast_add,Nat.cast_one]
    linarith
  have hKc ℓ : IsConnected (interior (K ℓ)) :=
    projectionDomain_interior_connected (exhaustionRadius_pos (parameters m) ℓ)
      (exhaustionRadius_branch (parameters m) ℓ)
  obtain ⟨H,_hw,hclock,hpos⟩ := exists_positive_fixed_annularHandleData m
  have hsimp i p (hp : ∀ j,0≤p j) (ht : (∑ j,p j) ≤ r i) : p∈region bF cF :=
    largeModelRegion_contains_cap (m+2) (hr₁ i).le (hr₂ i).le (by linarith) ⟨hp,ht⟩
  have hbLe : ∀ ν j,bF ν j≤1 := by
    intro ν j
    fin_cases ν
    · exact Fin.cases (by norm_num [bF,largeModelBounds])
        (fun _ => by norm_num [bF,largeModelBounds]) j
    · exact Fin.cases (by simpa [bF,largeModelBounds] using (show (h₂:ℝ)≤1 by linarith))
        (fun _ => by norm_num [bF,largeModelBounds]) j
  have hface (i : Fin N) (p : Moments (m+3)) (hp : ∀ j,0≤p j) (ht : (∑ j,p j) ≤ r i) ν :
      (∑ j,bF ν j*p j)≠cF ν := by
    have hb : (∑ j,bF ν j*p j) ≤ r i :=
      (Finset.sum_le_sum (fun j _ => mul_le_of_le_one_left (hp j) (hbLe ν j))).trans ht
    apply ne_of_lt (hb.trans_lt ?_)
    fin_cases ν
    · exact hr₁ i
    · exact hr₂ i
  obtain ⟨ℓ,φ,hφ,hφK,hdisj⟩ := Annular.exhausted_surface_packing_bp240 bF cF
    (largeModelBounds_nonneg _ hh₂.le)
    (fun ν => Fin.cases hh₁ (fun j => by fin_cases j; exact hh₂) ν) hcomp
    (largeModelDensity (m+2))
    ((continuous_const.mul (largeNormalCoefficient_smooth (m+2)).continuous).continuousOn)
    (fun p hp => mul_pos (by positivity) (largeNormalCoefficient_pos hh₁1 hh₂half hp))
    r r' hr' hrr hsimp hface hconc hmean hτ hτ1 hε houter
    K hK hKn (projectionDomain_cover (parameters m) (2+∑ j,‖parameters m j‖))
    (fun ℓ => (hKc ℓ).isPreconnected) (fun ℓ => (hKc ℓ).nonempty)
    (fun ℓ => projectionDomain_smoothBoundary (exhaustionRadius_pos (parameters m) ℓ)
      (exhaustionRadius_branch (parameters m) ℓ)) (positivePlaneTransitions (parameters m))
    H (half_pos H.width_pos) (by linarith [H.width_pos]) (by norm_num : (0:ℝ)<1/4)
    (by norm_num : (1:ℝ)/4<1/2) hpos hclock
    (curveFSForm_smooth (parameters m) (1/Real.pi)) (curveFSForm_skew (parameters m) (1/Real.pi))
    (fun c y hy => curveFSForm_positive (parameters m) (one_div_pos.mpr Real.pi_pos) c hy)
    (fun _ p => largeNormalCoefficient (m+2) p.1)
    (fun _ => (largeNormalCoefficient_smooth (m+2)).contMDiff.comp contMDiff_fst)
    (fun _ p hp _ _ => largeNormalCoefficient_pos hh₁1 hh₂half hp)
    (fun _ => largeHorizontalPrimitive (q := m+2) (parameters m))
    (fun _ => largeHorizontalPrimitive_smooth (q := m+2) (parameters m))
    (fun _ => largeHorizontalPrimitive_exterior (parameters m))
    (largeHorizontalPrimitive_area_limit_bp240 (parameters m) hh₁1 hh₂half)
  exact ⟨h₁,h₂,d₁,d₂,hr₁,hhd₁,hd₁,hr₂,hhd₂,hd₂,ℓ,φ,hφ,hφK,hdisj⟩

end Explicit

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_large_normal_packing_bp240_oai := @OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_large_normal_packing_bp240_oai
