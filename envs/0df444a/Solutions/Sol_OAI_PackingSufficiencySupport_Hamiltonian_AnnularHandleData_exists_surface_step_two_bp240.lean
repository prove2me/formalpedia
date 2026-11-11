-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_step_two_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:05.425199+00:00
-- url     : https://prove2.me/submissions/4d9b309b-b7ed-4eb7-8d9a-3a45055b925b

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_normalize_primitive_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_surface_area_redistribution_bp240

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

section
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem parameterSegmentPath_smooth (a : ℝ) : ContDiff ℝ ∞ (parameterSegmentPath (P := P) a) :=
  contDiff_const.add ((parameterSegmentLinear (P := P)).contDiff.comp (contDiff_id.sub contDiff_const))

theorem parameter_segment_integral_eq (f : P × ℝ → ℝ) (hf : Continuous f)
    (a : ℝ) (p : P × ℝ) :
    (∫ x in a..p.2, f (p.1,x)) =
      (p.2-a) * pathAverage ((⟨f,hf⟩ : C(P × ℝ,ℝ)).comp (parameterSegmentPath a p)) := by
  let u := (⟨f,hf⟩ : C(P × ℝ,ℝ)).comp (parameterSegmentPath a p)
  have he : (∫ s in (0:ℝ)..1, extendPath u s) =
      ∫ s in (0:ℝ)..1, f (p.1,a+s*(p.2-a)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    rw [show extendPath u s = u ⟨s,hs⟩ from extendPath_coe u ⟨s,hs⟩]
    change f (parameterSegmentPath a p ⟨s,hs⟩) = _
    rw [parameterSegmentPath_apply]
  change _ = (p.2-a) * (∫ s in (0:ℝ)..1, extendPath u s)
  rw [he]
  have hi := intervalIntegral.smul_integral_comp_add_mul (fun x => f (p.1,x))
    (a := (0:ℝ)) (b := 1) (p.2-a) a
  simpa only [smul_eq_mul,mul_zero,mul_one,add_zero,add_sub_cancel,mul_comm] using hi.symm

variable [FiniteDimensional ℝ P]

theorem contDiff_parameter_segment_integral {f : P × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : P × ℝ => ∫ x in a..p.2, f (p.1,x)) := by
  have he : (fun p : P × ℝ => ∫ x in a..p.2, f (p.1,x)) =
      fun p => (p.2-a)*pathAverage
        ((⟨f,hf.continuous⟩ : C(P × ℝ,ℝ)).comp (parameterSegmentPath a p)) := by
    funext p
    exact parameter_segment_integral_eq f hf.continuous a p
  rw [he]
  exact (contDiff_snd.sub contDiff_const).mul
    (pathAverage.contDiff.comp ((postcomp_contDiff (K := Time) (E := P × ℝ) (F := ℝ) hf).comp (parameterSegmentPath_smooth (P := P) a)))


end

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
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
open MeasureTheory Set

theorem planarCovector_smooth {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U V : P → ℝ} (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun p => planarCovector (U p) (V p)) := by
  exact (hU.smul contDiff_const).add (hV.smul contDiff_const)

theorem planar_deriv_first {f : Plane → ℝ} {p : Plane} (hf : DifferentiableAt ℝ f p) :
    deriv (fun x => f (x,p.2)) p.1 = fderiv ℝ f p (1,0) := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.deriv

theorem planar_deriv_second {f : Plane → ℝ} {p : Plane} (hf : DifferentiableAt ℝ f p) :
    deriv (fun y => f (p.1,y)) p.2 = fderiv ℝ f p (0,1) := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact hd.deriv

theorem planarCovector_exterior {U V : Plane → ℝ}
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (p : Plane) :
    euclideanExteriorOneForm (fun x => planarCovector (U x) (V x)) p =
      (deriv (fun x => V (x,p.2)) p.1 - deriv (fun y => U (p.1,y)) p.2) • planarArea := by
  let α : Plane → Plane →L[ℝ] ℝ := fun x => planarCovector (U x) (V x)
  have ha : DifferentiableAt ℝ α p := (planarCovector_smooth hU hV).contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hV' : fderiv ℝ α p (1,0) (0,1) = fderiv ℝ V p (1,0) := by
    rw [← fderiv_clm_eval ha]
    simp only [α,planarCovector_apply,mul_zero,mul_one,zero_add]
  have hU' : fderiv ℝ α p (0,1) (1,0) = fderiv ℝ U p (0,1) := by
    rw [← fderiv_clm_eval ha]
    simp only [α,planarCovector_apply,mul_zero,mul_one,add_zero]
  rw [planar_deriv_first (hV.contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    planar_deriv_second (hU.contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ α p u v - fderiv ℝ α p v u = _
  rw [bilinear_skew_plane,hV',hU']
  rfl


end

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

noncomputable section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory



namespace PackingSufficiencySupport.Hamiltonian
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem partitionFormMass_eq_partialChart_integral
    {I : Type*} [Fintype I] {K : Set M}
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    (hpos : PositivePartialChart e) (hK : IsCompact K) (hKe : K⊆e.target)
    (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) (hz : ∀ x,x∉K→Ω x=0) :
    partitionFormMass B ρ Ω=∫ y in e.symm '' K,partialChartCoefficient e Ω y := by
  classical
  let D : I → ManifoldTwoForm Plane M := fun i x => ρ i x • Ω x
  let L : I → Set M := fun i => K∩tsupport (ρ i)
  have hL (i : I) : IsCompact (L i) := hK.inter_right (isClosed_tsupport (ρ i))
  have hLB (i : I) : L i⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.2).1
  have hLe (i : I) : L i⊆e.target := fun _ hx => hKe hx.1
  have hDs (i : I) : SmoothTwoForm (D i) :=
    ((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ρ i).contMDiff).eval 0
  have hDa (i : I) (x : M) (u v : Plane) : D i x u v= -D i x v u := by
    change ρ i x * Ω x u v= -(ρ i x * Ω x v u)
    rw [ha x u v,mul_neg]
  have hDz (i : I) (x : M) (hx : x∉L i) : D i x=0 := by
    by_cases hk : x∈K
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
  have hS : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (e.symm.contMDiffOn.continuousOn.mono hKe)
  have hse : e.symm '' K⊆e.source := by
    rintro y ⟨x,hx,rfl⟩
    exact e.map_target (hKe hx)
  have hI (i : I) : IntegrableOn (partialChartCoefficient e (D i)) (e.symm '' K) :=
    ((partialChartCoefficient_contDiffOn e (hDs i)).continuousOn.mono hse).integrableOn_compact hS
  have hmass (i : I) : chartMass (B i).center (D i)=
      ∫ y in e.symm '' K,partialChartCoefficient e (D i) y := by
    rw [chartMass_eq_partialChart_integral e (hDa i) (hL i) (hLe i) (hLB i) (hDz i)
      (by
        rintro y ⟨x,hx,rfl⟩
        apply hpos (B i).center _ (e.map_target (hLe i hx))
        have heq : e (e.symm x)=x := e.right_inv (hLe i hx)
        exact heq.symm ▸ hLB i hx)]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS.measurableSet
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
  apply setIntegral_congr_fun hS.measurableSet
  intro y hy
  have hey : e y∈K := by
    obtain ⟨x,hx,rfl⟩ := hy
    have heq : e (e.symm x)=x := e.right_inv (hKe hx)
    rwa [heq]
  have hs : (∑ i,ρ i (e y))=1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hey
  simp only [D,partialChartCoefficient_smul,← Finset.sum_mul,hs,one_mul]

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
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartOneForm_manifoldPullback_at {α : ℝ → ManifoldOneForm E M} {e : N → M}
    {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target)
    (he : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) e ((extChartAt 𝓘(ℝ,F) b).symm p.2)) :
    chartOneForm (manifoldPullbackOneForm α e p.1) b p.2 =
      euclideanPullbackOneForm α (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := (he.hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackOneForm,hd,chartOneForm,manifoldPullbackOneForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v
  rfl

theorem manifoldPullbackOneForm_smooth_on {α : ℝ → ManifoldOneForm E M}
    {e : N → M} {U : Set N} (hU : IsOpen U)
    (he : ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e U)
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (b : N) :
    ContDiffOn ℝ ∞ (fun q : ℝ × F => chartOneForm (manifoldPullbackOneForm α e q.1) b q.2)
      (univ ×ˢ ((extChartAt 𝓘(ℝ,F) b).target ∩ (extChartAt 𝓘(ℝ,F) b).symm ⁻¹' U)) := by
  intro p hp
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2.1)
  have hg := (he.contMDiffAt (hU.mem_nhds hp.2.2)).comp p.2 hi
  apply ((euclideanPullbackOneForm_contDiffAt hα hg).congr_of_eventuallyEq _).contDiffWithinAt
  have ht := continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2.1)
  have hu := (hi.continuousAt.comp continuousAt_snd).preimage_mem_nhds (hU.mem_nhds hp.2.2)
  filter_upwards [ht,hu] with q hqt hqu
  exact chartOneForm_manifoldPullback_at hqt
    ((he.contMDiffAt (hU.mem_nhds hqu)).mdifferentiableAt (by simp))

end

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

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [NormedSpace ℝ P] in

theorem parameterManifoldPullback_chart_germ
    (α : P → ManifoldOneForm E M) {g : N → M} (p : P) {b : N}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g b) :
    (fun q : P × F => chartOneForm (parameterManifoldPullbackOneForm α g q.1) b q.2)
      =ᶠ[𝓝 (p,extChartAt 𝓘(ℝ,F) b b)]
    parameterEuclideanPullbackOneForm α (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) := by
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hn₁ : {x | ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) 1 g x} ∈
      𝓝 ((extChartAt 𝓘(ℝ,F) b).symm (extChartAt 𝓘(ℝ,F) b b)) := by
    rw [he]; exact hn
  have hn' := (hi.continuousAt.comp (f := Prod.snd) (continuousAt_snd (p := (p,extChartAt 𝓘(ℝ,F) b b)))).preimage_mem_nhds hn₁
  filter_upwards [hn',continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)] with q hq hqt
  exact chartOneForm_manifoldPullback_at (α := fun _ => α q.1) (p := (0,q.2)) hqt
    (hq.mdifferentiableAt (by simp))

theorem parameterManifoldPullbackOneForm_contDiffAt
    {α : P → ManifoldOneForm E M} {g : N → M} {p : P} {b : N}
    (hα : ContDiffAt ℝ ∞
      (fun q : P × E => chartOneForm (α q.1) (g b) q.2)
      (p,extChartAt 𝓘(ℝ,E) (g b) (g b)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g b) :
    ContDiffAt ℝ ∞
      (fun q : P × F => chartOneForm (parameterManifoldPullbackOneForm α g q.1) b q.2)
      (p,extChartAt 𝓘(ℝ,F) b b) := by
  let y := extChartAt 𝓘(ℝ,F) b b
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy : y∈(extChartAt 𝓘(ℝ,F) b).target := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he : (extChartAt 𝓘(ℝ,F) b).symm y=b := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hg' : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g ((extChartAt 𝓘(ℝ,F) b).symm y) := by
    rw [he]; exact hg
  have hα' : ContDiffAt ℝ ∞
      (fun q : P × E => chartOneForm (α q.1) ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y) q.2)
      (p,extChartAt 𝓘(ℝ,E) ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)
        ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)) := by
    simpa only [Function.comp_apply,he] using hα
  have hs := parameterEuclideanPullbackOneForm_contDiffAt
    (α := α) (g := g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (p := (p,y)) hα' (hg'.comp y hi)
  exact hs.congr_of_eventuallyEq (parameterManifoldPullback_chart_germ α p hg)

theorem manifold_pullback_exterior_at {α : ManifoldOneForm E M}
    {g : N → M} {b : N}
    (hα : ContDiffAt ℝ ∞ (chartOneForm α (g b))
      (extChartAt 𝓘(ℝ,E) (g b) (g b)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g b) :
    manifoldExteriorOneForm (E := F) (M := N)
      (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =
      manifoldPullbackTwoForm (E := E) (F := F) (fun _ => manifoldExteriorOneForm α) g 0 b := by
  let y := extChartAt 𝓘(ℝ,F) b b
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy : y ∈ (extChartAt 𝓘(ℝ,F) b).target := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he : (extChartAt 𝓘(ℝ,F) b).symm y=b := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hgy : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g ((extChartAt 𝓘(ℝ,F) b).symm y) := by
    rw [he]
    exact hg
  have hc : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y :=
    hgy.comp y hi
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hgy.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hu := hi.continuousAt.preimage_mem_nhds hn
  have hh : chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =ᶠ[𝓝 y]
      fun z => euclideanPullbackOneForm (fun _ => α) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (0,z) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy,hu] with z hz hzU
    exact chartOneForm_manifoldPullback_at (α := fun _ => α) (b := b) (p := (0,z)) hz
      (hzU.mdifferentiableAt (by simp))
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
      _ = _ := by
        have hα' : ContDiffAt ℝ ∞
            (chartOneForm α ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y))
            (extChartAt 𝓘(ℝ,E) ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)
              ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)) := by
          simpa only [Function.comp_apply,he] using hα
        simpa only [Function.comp_apply,he] using euclidean_manifold_pullback_exterior_at hc hα'
  have hd := mfderiv_comp y (hgy.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  have hD : manifoldMapDifferential (E := E) (F := F)
      (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y =
      (manifoldMapDifferential (E := E) (F := F) g b).comp
        (chartDifferential (E := F) b b).inverse := by
    change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y = _
    rw [hd,← chartDifferential_inverse hy]
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

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem extendManifoldOneForm_smooth {U K : Set M} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {α : P → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ ((extChartAt 𝓘(ℝ,E) c).target ∩ (extChartAt 𝓘(ℝ,E) c).symm ⁻¹' U)))
    (hz : ∀ p x, x ∈ U → x ∉ K → α p x=0) :
    SmoothOneFormFamily (fun p => extendManifoldOneForm U (α p)) := by
  intro c p hp
  let x := (extChartAt 𝓘(ℝ,E) c).symm p.2
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hp.2)).continuousAt
  by_cases hx : x ∈ U
  · have hn := (hi.comp continuousAt_snd).preimage_mem_nhds (hU.mem_nhds hx)
    have ht := continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hp.2)
    have hnh : univ ×ˢ ((extChartAt 𝓘(ℝ,E) c).target ∩
        (extChartAt 𝓘(ℝ,E) c).symm ⁻¹' U) ∈ 𝓝 p := by
      filter_upwards [hn,ht] with q hq hqt
      exact ⟨mem_univ _,hqt,hq⟩
    apply (((hα c).contDiffAt hnh).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hn] with q hq
    change (extendManifoldOneForm U (α q.1) ((extChartAt 𝓘(ℝ,E) c).symm q.2)).comp _ = _
    change (extChartAt 𝓘(ℝ,E) c).symm q.2 ∈ U at hq
    rw [extendManifoldOneForm_inside hq]
    rfl
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hn := (hi.comp continuousAt_snd).preimage_mem_nhds (hK.isOpen_compl.mem_nhds hxK)
    apply ((contDiffAt_const (c := (0 : E →L[ℝ] ℝ))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hn] with q hq
    change (extendManifoldOneForm U (α q.1) ((extChartAt 𝓘(ℝ,E) c).symm q.2)).comp _ = 0
    by_cases hu : (extChartAt 𝓘(ℝ,E) c).symm q.2 ∈ U
    · rw [extendManifoldOneForm_inside hu,hz _ _ hu hq]
      exact ContinuousLinearMap.zero_comp _
    · rw [extendManifoldOneForm_outside hu]
      exact ContinuousLinearMap.zero_comp _

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_HorizontalCoupling
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

theorem manifoldWedge_skew (α β : ManifoldOneForm E M) (z : M) (v w : E) :
    manifoldWedge α β z v w= -manifoldWedge α β z w v := by
  simp only [manifoldWedge_apply]
  ring

theorem chartTwoForm_wedge (α β : ManifoldOneForm E M) (c : M) (y : E) :
    chartTwoForm (manifoldWedge α β) c y =
      (chartOneForm α c y).smulRight (chartOneForm β c y)-
      (chartOneForm β c y).smulRight (chartOneForm α c y) := by
  ext v w
  rfl

theorem manifoldWedge_smooth {α β : ManifoldOneForm E M}
    (hα : ∀ c,ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target) :
    SmoothTwoForm (manifoldWedge α β) := by
  intro c
  have he : chartTwoForm (manifoldWedge α β) c = fun y =>
      (chartOneForm α c y).smulRight (chartOneForm β c y)-
      (chartOneForm β c y).smulRight (chartOneForm α c y) :=
    funext (chartTwoForm_wedge α β c)
  rw [he]
  exact ((hα c).smulRight (hβ c)).sub ((hβ c).smulRight (hα c))


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem manifoldScalarDifferential_chart {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f) {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartOneForm (manifoldScalarDifferential f) c y=
      fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ,E) c).symm) y := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hy)
  have hd := mfderiv_comp y (hf.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  rw [chartOneForm,chartDifferential_inverse hy]
  exact hd.symm

theorem manifoldScalar_chart_smooth {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f) (c : M) :
    ContDiffOn ℝ ∞ (f ∘ (extChartAt 𝓘(ℝ,E) c).symm)
      (extChartAt 𝓘(ℝ,E) c).target :=
  (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c)).contDiffOn

theorem manifoldScalarDifferential_smooth {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f) (c : M) :
    ContDiffOn ℝ ∞ (chartOneForm (manifoldScalarDifferential f) c)
      (extChartAt 𝓘(ℝ,E) c).target := by
  intro y hy
  have hs := (manifoldScalar_chart_smooth hf c).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hy)
  have he : chartOneForm (manifoldScalarDifferential f) c =ᶠ[𝓝 y]
      fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ,E) c).symm) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hy] with z hz
    exact manifoldScalarDifferential_chart hf hz
  exact ((hs.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).congr_of_eventuallyEq he).contDiffWithinAt


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

theorem handlePushforwardOneForm_smooth [T2Space N]
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {α : ManifoldOneForm E M} {K : Set M} (hK : IsCompact K) (hKs : K⊆e.source)
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (hz : ∀ x, x∉K → α x=0) :
    SmoothOneFormFamily (fun _ : ℝ => handlePushforwardOneForm e α) := by
  have hKi : IsCompact (e '' K) :=
    hK.image_of_continuousOn (e.contMDiffOn.continuousOn.mono hKs)
  change SmoothOneFormFamily (fun p : ℝ => extendManifoldOneForm e.target
    (manifoldPullbackOneForm (fun _ : ℝ => α) e.symm p))
  apply extendManifoldOneForm_smooth e.open_target hKi.isClosed
  · rintro y ⟨x,hx,rfl⟩
    exact e.map_source (hKs hx)
  · exact manifoldPullbackOneForm_smooth_on (α := fun _ : ℝ => α)
      e.open_target e.symm.contMDiffOn
      (fun c => (hα c).comp contDiffOn_snd (fun _ hp => hp.2))
  · intro p y hyt hy
    have hk : e.symm y∉K := by
      intro hk
      exact hy ⟨e.symm y,hk,e.right_inv hyt⟩
    simp only [manifoldPullbackOneForm,hz _ hk,ContinuousLinearMap.zero_comp]

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem handlePushforwardOneForm_pullback
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    (α : ManifoldOneForm E M) {x : M} (hx : x∈e.source) :
    manifoldPullbackOneForm (fun _ => handlePushforwardOneForm e α) e 0 x=α x := by
  have hd := handle_mfderiv_symm_comp e hx
  change (extendManifoldOneForm e.target
    (manifoldPullbackOneForm (fun _ => α) e.symm 0) (e x)).comp _ = _
  rw [extendManifoldOneForm_inside (e.map_source hx)]
  ext v
  change α (e.symm (e x))
    ((manifoldMapDifferential (E := E) (F := F) e.symm (e x))
      ((manifoldMapDifferential (E := F) (F := E) e x) v)) = α x v
  have hαx : α (e.symm (e x))=α x := congrArg α (e.left_inv hx)
  rw [hαx]
  exact congrArg (α x) (congrArg (fun D : E →L[ℝ] E => D v) hd)



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

theorem IsPrimitiveFamily.intrinsic {Ω : P → ManifoldTwoForm E M}
    {α : P → ManifoldOneForm E M} (hα : IsPrimitiveFamily Ω α) (p : P) (x : M) :
    manifoldExteriorOneForm (α p) x=Ω p x := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have he := hα.exterior p x (extChartAt 𝓘(ℝ,E) x x) ((extChartAt 𝓘(ℝ,E) x).map_source hx)
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change euclideanExteriorOneForm (chartOneForm (α p) x) (extChartAt 𝓘(ℝ,E) x x)
    (chartDifferential x x v) (chartDifferential x x w)=Ω p x v w
  rw [he]
  exact chartTwoForm_apply_chart hx v w

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
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_LayerCoordinates
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
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiffAt_parameter_segment_integral {f : P × ℝ → ℝ} {U : Set (P × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a : ℝ) (p : P × ℝ)
    (hseg : ∀ s ∈ Icc (0:ℝ) 1, (p.1,a+s*(p.2-a)) ∈ U) :
    ContDiffAt ℝ ∞ (fun q : P × ℝ => ∫ x in a..q.2, f (q.1,x)) p := by
  let K : Set (P × ℝ) := (fun s : ℝ => (p.1,a+s*(p.2-a))) '' Icc (0:ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image
    (continuous_const.prodMk (continuous_const.add (continuous_id.mul continuous_const)))
  obtain ⟨χ,_,_,_,_,_,hg,_,he⟩ := exists_smooth_compact_extension hK hU
    (by rintro _ ⟨s,hs,rfl⟩; exact hseg s hs) hf
  let g : P × ℝ → ℝ := fun q => χ q • f q
  have hnear : ∀ᶠ q in 𝓝 p, ∀ s ∈ Icc (0:ℝ) 1,
      g (q.1,a+s*(q.2-a)) = f (q.1,a+s*(q.2-a)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hc : Continuous (fun z : (P × ℝ) × ℝ => (z.1.1,a+z.2*(z.1.2-a))) :=
      (continuous_fst.fst).prodMk
        (continuous_const.add (continuous_snd.mul (continuous_fst.snd.sub continuous_const)))
    have hk : (p.1,a+s*(p.2-a)) ∈ K := ⟨s,hs,rfl⟩
    exact (hc.continuousAt (x := (p,s))).eventually (he.filter_mono (nhds_le_nhdsSet hk))
  apply (contDiff_parameter_segment_integral hg a).contDiffAt.congr_of_eventuallyEq
  filter_upwards [hnear] with q hq
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ segment ℝ a q.2 := by simpa only [segment_eq_uIcc] using hx
  rw [segment_eq_image' ℝ a q.2] at hx'
  obtain ⟨s,hs,rfl⟩ := hx'
  exact (hq s hs).symm

theorem contDiffOn_parameter_segment_integral {f : P × ℝ → ℝ} {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) (a : ℝ) (ha : a ∈ I)
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ I)) :
    ContDiffOn ℝ ∞ (fun q : P × ℝ => ∫ x in a..q.2, f (q.1,x)) (V ×ˢ I) := by
  intro p hp
  apply (contDiffAt_parameter_segment_integral (hV.prod hI) hf a p ?_).contDiffWithinAt
  intro s hs
  refine ⟨hp.1,?_⟩
  have hm := hc ha hp.2 (sub_nonneg.mpr hs.2) hs.1 (by ring : (1-s)+s=1)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  simp only [smul_eq_mul]
  ring


end

open scoped ContDiff
open Set Function



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

theorem ambientAngular_smooth : ContDiff ℝ ∞ ambientAngular := by
  apply ContDiff.const_smul
  exact contDiff_const.clm_comp
    ((ContinuousLinearMap.mul ℝ ℂ).contDiff.comp Complex.conjCLE.contDiff)

theorem chartOneForm_euclidean (α : ℂ → ℂ →L[ℝ] ℝ) (c y : ℂ) :
    chartOneForm α c y=α y := by
  simp only [chartOneForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,ContinuousLinearMap.comp_id,id_eq]

theorem ambientAngular_chart_smooth (c : ℂ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℂ => chartOneForm ambientAngular c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,ℂ) c).target) := by
  simpa only [chartOneForm_euclidean,Function.comp_def] using
    (ambientAngular_smooth.comp contDiff_snd).contDiffOn

theorem circleAngular_joint_smooth (c : Circle) :
    ContDiffOn ℝ ∞ (fun q : ℝ × CircleModel => chartOneForm circleAngular c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,CircleModel) c).target) := by
  exact manifoldPullbackOneForm_smooth (α := fun _ => ambientAngular)
    circle_coe_smooth ambientAngular_chart_smooth c

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

theorem cylinderAngular_smooth (c : HandleCylinder) :
    ContDiffOn ℝ ∞ (chartOneForm cylinderAngular c)
      (extChartAt 𝓘(ℝ,CylinderModel) c).target := by
  have ht := manifoldPullbackOneForm_smooth (α := fun _ => circleAngular)
    cylinder_snd_smooth circleAngular_joint_smooth c
  exact ht.comp (f := fun y => ((0:ℝ),y))
    (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)

theorem weightedCylinderAngular_chart (f : HandleCylinder → ℝ) (c : HandleCylinder)
    (y : CylinderModel) : chartOneForm (weightedCylinderAngular f) c y=
      f ((extChartAt 𝓘(ℝ,CylinderModel) c).symm y) • chartOneForm cylinderAngular c y := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem weightedCylinderAngular_smoothAt {f : HandleCylinder → ℝ} {c : HandleCylinder}
    (hf : ContMDiffAt 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ f c) :
    ContDiffAt ℝ ∞ (chartOneForm (weightedCylinderAngular f) c)
      (extChartAt 𝓘(ℝ,CylinderModel) c c) := by
  have he : chartOneForm (weightedCylinderAngular f) c=
      fun y => f ((extChartAt 𝓘(ℝ,CylinderModel) c).symm y) • chartOneForm cylinderAngular c y :=
    funext (weightedCylinderAngular_chart f c)
  rw [he]
  have hc := (extChartAt 𝓘(ℝ,CylinderModel) c).map_source (mem_extChartAt_source c)
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,CylinderModel)) c).mem_nhds hc
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,CylinderModel)) (n := ∞) c).contMDiffAt hn
  have hfc : ContMDiffAt 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ f
      ((extChartAt 𝓘(ℝ,CylinderModel) c).symm (extChartAt 𝓘(ℝ,CylinderModel) c c)) := by
    simpa only [(extChartAt 𝓘(ℝ,CylinderModel) c).left_inv (mem_extChartAt_source c)] using hf
  exact ((hfc.comp _ hi).contDiffAt).smul ((cylinderAngular_smooth c).contDiffAt hn)





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

theorem periodic_eq_of_circleTurn_eq {F : ℝ → ℝ} (hF : Periodic F 1)
    {s t : ℝ} (h : circleTurn s=circleTurn t) : F s=F t := by
  obtain ⟨m,rfl⟩ := (circleTurn_eq_iff s t).mp h
  simpa only [mul_one] using hF.int_mul m t

theorem circlePeriodicDescent_turn {F : ℝ → ℝ} (hF : Periodic F 1) (t : ℝ) :
    circlePeriodicDescent F (circleTurn t)=F t :=
  periodic_eq_of_circleTurn_eq hF (circleTurn_shortCircleArgument _)

theorem localCircleLift_turn (c z : Circle) : circleTurn (localCircleLift c z)=z := by
  rw [localCircleLift,circleTurn_add,circleTurn_shortCircleArgument,
    circleTurn_shortCircleArgument,div_mul_cancel]

theorem localCircleLift_smooth_at (c : Circle) :
    ContMDiffAt 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ (localCircleLift c) c := by
  have hdiv : ContMDiffAt 𝓘(ℝ,CircleModel) 𝓘(ℝ,CircleModel) ∞
      (fun z : Circle => z/c) c := contMDiffAt_id.div contMDiffAt_const
  have hslit : ((c/c : Circle) : ℂ) ∈ Complex.slitPlane := by
    simpa only [div_self',Circle.coe_one] using Complex.one_mem_slitPlane
  exact ((shortCircleArgument_smooth_at hslit).comp (f := fun z : Circle => z/c) c hdiv).add contMDiffAt_const

theorem circlePeriodicDescent_local {F : ℝ → ℝ} (hF : Periodic F 1)
    (c z : Circle) : circlePeriodicDescent F z=F (localCircleLift c z) :=
  periodic_eq_of_circleTurn_eq hF ((circleTurn_shortCircleArgument z).trans
    (localCircleLift_turn c z).symm)

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem circleFamilyDescent_turn {F : P × ℝ → ℝ} {p : P}
    (hp : Periodic (fun t => F (p,t)) 1) (t : ℝ) :
    circleFamilyDescent F (p,circleTurn t)=F (p,t) :=
  circlePeriodicDescent_turn hp t

theorem circleFamilyDescent_smoothOn {V : Set P} (hV : IsOpen V)
    {F : P × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (V ×ˢ univ))
    (hp : ∀ p ∈ V, Periodic (fun t => F (p,t)) 1) :
    ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
      (circleFamilyDescent F) (V ×ˢ univ) := by
  intro q hq
  have hl : ContMDiffAt ((𝓘(ℝ,P)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
      (fun w : P × Circle => localCircleLift q.2 w.2) q :=
    (localCircleLift_smooth_at q.2).comp q contMDiffAt_snd
  have hm := (contMDiffAt_fst (I := 𝓘(ℝ,P))
    (J := 𝓘(ℝ,CircleModel)) (n := ∞) (p := q)).prodMk_space hl
  have hfat : ContDiffAt ℝ ∞ F (q.1,localCircleLift q.2 q.2) :=
    hF.contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hq.1,mem_univ _⟩)
  have ht := hfat.contMDiffAt.comp q hm
  apply (ht.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(hV.prod isOpen_univ).mem_nhds hq] with w hw
  exact circlePeriodicDescent_local (hp w.1 hw.1) q.2 w.2


end

open scoped ContDiff Topology
open Set Function MeasureTheory



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
open Set Function MeasureTheory
variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_primitive_on {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {f : ℝ → ℝ} (hf : ContinuousOn f I) {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    HasDerivAt (fun t => ∫ s in a..t, f s) (f b) b := by
  have hseg : uIcc a b ⊆ I := by
    rw [← segment_eq_uIcc]
    exact hc.segment_subset ha hb
  exact intervalIntegral.integral_hasDerivAt_right
    ((hf.mono hseg).intervalIntegrable) (hf.stronglyMeasurableAtFilter hI b hb)
    (hf.continuousAt (hI.mem_nhds hb))


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem annularScalarDescent_turn {F : P × Plane → ℝ} {p : P} {s : ℝ}
    (hp : Periodic (fun t => F (p,(s,t))) 1) (t : ℝ) :
    annularScalarDescent F ((p,s),circleTurn t)=F (p,(s,t)) :=
  circleFamilyDescent_turn hp t

theorem annularScalarDescent_smoothOn {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) {F : P × Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ univ)))
    (hp : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => F (p,(s,t))) 1) :
    ContMDiffOn ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
      (annularScalarDescent F) ((V ×ˢ I) ×ˢ univ) := by
  apply circleFamilyDescent_smoothOn (hV.prod hI)
  · apply hF.comp
      ((contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)).contDiffOn)
    intro q hq
    exact ⟨hq.1.1,hq.1.2,hq.2⟩
  · intro q hq
    exact hp q.1 hq.1 q.2 hq.2



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularCurvaturePrimitive
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
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
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem annularRadialIntegral_smooth {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ))) :
    ContDiffOn ℝ ∞ (annularRadialIntegral a κ) (V ×ˢ (I ×ˢ univ)) := by
  have hG : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℝ => κ (q.1.1,(q.2,q.1.2)))
      ((V ×ˢ univ) ×ˢ I) :=
    hκ.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd)).contDiffOn
      (fun _ hq => ⟨hq.1.1,hq.2,hq.1.2⟩)
  have hi := contDiffOn_parameter_segment_integral (hV.prod isOpen_univ) hI hc a ha hG
  exact hi.comp ((contDiff_fst.prodMk contDiff_snd.snd).prodMk contDiff_snd.fst).contDiffOn
    (fun _ hq => ⟨⟨hq.1,hq.2.2⟩,hq.2.1⟩)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem annularRadialIntegral_periodic {V : Set P} {I : Set ℝ} (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I) {κ : P × Plane → ℝ}
    (hκ : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1)
    {p : P} (hp : p∈V) {s : ℝ} (hs : s∈I) :
    Periodic (fun t => annularRadialIntegral a κ (p,(s,t))) 1 := by
  intro t
  apply intervalIntegral.integral_congr
  intro u hu
  have huI : u∈I := hc.segment_subset ha hs (by simpa only [segment_eq_uIcc] using hu)
  exact hκ p hp u huI t

omit [FiniteDimensional ℝ P] in
theorem annularRadialIntegral_hasDerivAt {V : Set P} {I : Set ℝ}
    (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ)))
    {p : P} (hp : p∈V) {q : Plane} (hq : q.1∈I) :
    HasDerivAt (fun s => annularRadialIntegral a κ (p,(s,q.2))) (κ (p,q)) q.1 := by
  change HasDerivAt (fun s => ∫ u in a..s,κ (p,(u,q.2))) (κ (p,(q.1,q.2))) q.1
  apply hasDerivAt_primitive_on hI hc _ ha hq
  exact hκ.continuousOn.comp
    (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousOn
    (fun _ hs => ⟨hp,hs,mem_univ _⟩)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem planarCovector_exterior_at {U V : Plane → ℝ} {p : Plane}
    (hU : ContDiffAt ℝ ∞ U p) (hV : ContDiffAt ℝ ∞ V p) :
    euclideanExteriorOneForm (fun x => planarCovector (U x) (V x)) p=
      (fderiv ℝ V p (1,0)-fderiv ℝ U p (0,1)) • planarArea := by
  let α : Plane → Plane →L[ℝ] ℝ := fun x => planarCovector (U x) (V x)
  have ha : DifferentiableAt ℝ α p :=
    ((hU.smul contDiffAt_const).add (hV.smul contDiffAt_const)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hV' : fderiv ℝ α p (1,0) (0,1)=fderiv ℝ V p (1,0) := by
    rw [← fderiv_clm_eval ha]
    simp only [α,planarCovector_apply,mul_zero,mul_one,zero_add]
  have hU' : fderiv ℝ α p (0,1) (1,0)=fderiv ℝ U p (0,1) := by
    rw [← fderiv_clm_eval ha]
    simp only [α,planarCovector_apply,mul_zero,mul_one,add_zero]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ α p u v-fderiv ℝ α p v u=_
  rw [bilinear_skew_plane,hV',hU']
  rfl

theorem annular_curvature_primitive {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1) :
    ContMDiffOn ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
      (annularScalarDescent (annularRadialIntegral a κ)) ((V ×ˢ I) ×ˢ univ) ∧
      (∀ p∈V,∀ q : Plane,q.1∈I →
        euclideanExteriorOneForm (fun z => planarCovector 0 (annularRadialIntegral a κ (p,z))) q=
          κ (p,q) • planarArea) := by
  have hB := annularRadialIntegral_smooth hV hI hc ha hκ
  refine ⟨annularScalarDescent_smoothOn hV hI hB
    (fun _ hp _ hs => annularRadialIntegral_periodic hc ha hper hp hs),?_⟩
  intro p hp q hq
  have hBp : ContDiffOn ℝ ∞ (fun z => annularRadialIntegral a κ (p,z)) (I ×ˢ univ) :=
    hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩)
  have hBa := hBp.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨hq,mem_univ _⟩)
  have hd := (hBa.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  have he : fderiv ℝ (fun z => annularRadialIntegral a κ (p,z)) q (1,0)=κ (p,q) :=
    hd.unique (annularRadialIntegral_hasDerivAt hI hc ha hκ hp hq)
  rw [planarCovector_exterior_at contDiffAt_const hBa,he]
  simp


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem annularCylinderScalar_smoothAt {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) {F : P × Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => F (p,(s,t))) 1)
    {p : P} (hp : p∈V) {z : HandleCylinder} (hz : z.1∈I) :
    ContMDiffAt 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ (annularCylinderScalar F p) z := by
  have hd := (annularScalarDescent_smoothOn hV hI hF hper).contMDiffAt
    (((hV.prod hI).prod isOpen_univ).mem_nhds (show ((p,z.1),z.2)∈_
      from ⟨⟨hp,hz⟩,mem_univ _⟩))
  have hi : ContMDiff 𝓘(ℝ,CylinderModel) ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) ∞
      (fun z : HandleCylinder => ((p,z.1),z.2)) := by
    rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
      modelWithCornersSelf_prod]
    have hfst : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
        (Prod.fst : HandleCylinder → ℝ) := contMDiff_fst
    have hsnd : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,CircleModel) ∞
        (Prod.snd : HandleCylinder → Circle) := contMDiff_snd
    have hpair : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,P × ℝ) ∞
        (fun z : HandleCylinder => (p,z.1)) :=
      ((contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun s : ℝ => (p,s))).contMDiff).comp hfst
    exact hpair.prodMk hsnd
  exact hd.comp z hi.contMDiffAt

variable [FiniteDimensional ℝ P]

theorem cylinderCurvaturePrimitive_smoothAt {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1)
    {p : P} (hp : p∈V) {z : HandleCylinder} (hz : z.1∈I) :
    ContDiffAt ℝ ∞ (chartOneForm (cylinderCurvaturePrimitive a κ p) z)
      (extChartAt 𝓘(ℝ,CylinderModel) z z) :=
  weightedCylinderAngular_smoothAt (annularCylinderScalar_smoothAt hV hI
    (annularRadialIntegral_smooth hV hI hc ha hκ)
    (fun _ hp _ hs => annularRadialIntegral_periodic hc ha hper hp hs) hp hz)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem cylinderCurvaturePrimitive_cover {V : Set P} {I : Set ℝ}
    (hc : Convex ℝ I) {a : ℝ} (ha : a∈I) {κ : P × Plane → ℝ}
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1)
    {p : P} (hp : p∈V) {q : Plane} (hq : q.1∈I) (v : Plane) :
    cylinderCurvaturePrimitive a κ p (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v)=
      annularRadialIntegral a κ (p,q)*v.2 := by
  change annularCylinderScalar (annularRadialIntegral a κ) p (cylinderCover q)*
    cylinderAngular (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v)=_
  rw [cylinderAngular_cover]
  change annularScalarDescent (annularRadialIntegral a κ) ((p,q.1),circleTurn q.2)*v.2=_
  rw [annularScalarDescent_turn (annularRadialIntegral_periodic hc ha hper hp hq)]

theorem cylinderCurvaturePrimitive_exterior_cover {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1)
    {p : P} (hp : p∈V) {q : Plane} (hq : q.1∈I) :
    (manifoldExteriorOneForm (cylinderCurvaturePrimitive a κ p) (cylinderCover q)).bilinearComp
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q)=κ (p,q) • planarArea := by
  have hn := euclidean_manifold_pullback_exterior_at cylinderCover_smooth.contMDiffAt
    (cylinderCurvaturePrimitive_smoothAt hV hI hc ha hκ hper hp hq)
  have he : (fun y => euclideanPullbackOneForm (fun _ => cylinderCurvaturePrimitive a κ p)
      cylinderCover (0,y)) =ᶠ[𝓝 q]
      (fun y => planarCovector 0 (annularRadialIntegral a κ (p,y))) := by
    filter_upwards [(hI.prod isOpen_univ).mem_nhds (show q∈I ×ˢ univ from ⟨hq,mem_univ _⟩)] with y hy
    apply ContinuousLinearMap.ext
    intro v
    change cylinderCurvaturePrimitive a κ p (cylinderCover y)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover y v)=_
    rw [cylinderCurvaturePrimitive_cover hc ha hper hp hy.1]
    simp only [planarCovector_apply,zero_mul,zero_add]
  calc
    _ = euclideanExteriorOneForm (fun y => euclideanPullbackOneForm
        (fun _ => cylinderCurvaturePrimitive a κ p) cylinderCover (0,y)) q := hn.symm
    _ = euclideanExteriorOneForm
        (fun y => planarCovector 0 (annularRadialIntegral a κ (p,y))) q := by
      unfold euclideanExteriorOneForm
      rw [he.fderiv_eq]
    _ = _ := (annular_curvature_primitive hV hI hc ha hκ hper).2 p hp q hq


end


open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem cylinderCurvaturePrimitive_exterior_covered {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1)
    {p : P} (hp : p∈V) {q : Plane} (hq : q.1∈I) :
    manifoldExteriorOneForm (cylinderCurvaturePrimitive a κ p) (cylinderCover q)=
      κ (p,q) • cylinderAreaForm (cylinderCover q) := by
  let L : Plane →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q
  have he : (manifoldExteriorOneForm (cylinderCurvaturePrimitive a κ p) (cylinderCover q)).bilinearComp
      L L=κ (p,q) • planarArea :=
    cylinderCurvaturePrimitive_exterior_cover hV hI hc ha hκ hper hp hq
  have hL (v : CylinderModel) : L (v.1,circleAngular (circleTurn q.2) v.2)=v :=
    cylinderCover_derivative_right_inverse q v
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have hv := congrArg (fun Ω : Plane →L[ℝ] Plane →L[ℝ] ℝ =>
    Ω (v.1,circleAngular (circleTurn q.2) v.2) (w.1,circleAngular (circleTurn q.2) w.2)) he
  simp only [ContinuousLinearMap.bilinearComp_apply,smul_apply,smul_eq_mul] at hv
  rw [hL v,hL w] at hv
  simpa only [planarArea_apply,cylinderAreaForm_apply,smul_apply,smul_eq_mul,cylinderCover] using hv



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_CylinderAnnularNormalization
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderComplexMap_norm _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
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

theorem cylinderCover_period_one (q : Plane) :
    cylinderCover (q+(0,1))=cylinderCover q := by
  apply Prod.ext
  · simp [cylinderCover]
  · exact circleTurn_period_one q.2

theorem cylinderCover_derivative_period_one (q : Plane) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover (q+(0,1))=
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q := by
  have hT : HasFDerivAt (fun z : Plane => z+(0,1)) (ContinuousLinearMap.id ℝ Plane) q :=
    (hasFDerivAt_id q).add_const (0,1)
  have hd := ((cylinderCover_smooth.mdifferentiableAt (by simp)
    (x := q+(0,1))).hasMFDerivAt.comp q
    (hasMFDerivAt_iff_hasFDerivAt.mpr hT)).mfderiv
  have he : cylinderCover ∘ (fun z : Plane => z+(0,1))=cylinderCover :=
    funext cylinderCover_period_one
  rw [he] at hd
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun D : Plane →L[ℝ] CylinderModel => D v) hd
  exact hv.symm


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


open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularChartNormalization
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

theorem cylinderClockPrimitive_smoothAt {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (z : HandleCylinder) :
    ContDiffAt ℝ ∞ (chartOneForm (cylinderClockPrimitive S f) z)
      (extChartAt 𝓘(ℝ,CylinderModel) z z) := by
  have hp : ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ (Prod.fst : HandleCylinder → ℝ) := by
    rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod]
    exact contMDiff_fst
  exact weightedCylinderAngular_smoothAt
    (((hS.contMDiff.comp hp).mul (hf.comp cylinder_snd_smooth)).contMDiffAt)

theorem cylinderClockPrimitive_exterior_cover {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f) (q : Plane) :
    (manifoldExteriorOneForm (cylinderClockPrimitive S f) (cylinderCover q)).bilinearComp
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q)=
      (deriv S q.1*f (circleTurn q.2)) • planarArea := by
  have hn := euclidean_manifold_pullback_exterior_at cylinderCover_smooth.contMDiffAt
    (cylinderClockPrimitive_smoothAt hS hf (cylinderCover q))
  have he : (fun y => euclideanPullbackOneForm (fun _ => cylinderClockPrimitive S f) cylinderCover (0,y))=
      (fun y => planarCovector 0 (S y.1*f (circleTurn y.2))) := by
    funext y
    apply ContinuousLinearMap.ext
    intro v
    change (S y.1*f (circleTurn y.2))*cylinderAngular (cylinderCover y)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover y v)=_
    rw [cylinderAngular_cover]
    simp only [planarCovector_apply,zero_mul,zero_add]
  have hc : ContDiff ℝ ∞ (fun y : Plane => S y.1*f (circleTurn y.2)) :=
    (hS.comp contDiff_fst).mul (((hf.comp circleTurn_smooth).contDiff).comp contDiff_snd)
  have hd : deriv (fun s => S s*f (circleTurn q.2)) q.1=deriv S q.1*f (circleTurn q.2) :=
    ((hS.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) q.1).hasDerivAt.mul_const _).deriv
  calc
    _ = euclideanExteriorOneForm
        (fun y => euclideanPullbackOneForm (fun _ => cylinderClockPrimitive S f) cylinderCover (0,y)) q := hn.symm
    _ = _ := by
      rw [he,planarCovector_exterior contDiff_const hc,hd,deriv_const,sub_zero]

theorem cylinderClockPrimitive_exterior {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (z : HandleCylinder) :
    manifoldExteriorOneForm (cylinderClockPrimitive S f) z=
      (deriv S z.1*f z.2) • cylinderAreaForm z := by
  let q : Plane := (z.1,shortCircleArgument z.2)
  have hq : cylinderCover q=z := by
    apply Prod.ext
    · rfl
    · exact circleTurn_shortCircleArgument z.2
  rw [← hq]
  let D : Plane →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q
  have he : (manifoldExteriorOneForm (cylinderClockPrimitive S f) (cylinderCover q)).bilinearComp D D=
      (deriv S q.1*f (circleTurn q.2)) • planarArea :=
    cylinderClockPrimitive_exterior_cover hS hf q
  have hd (u : CylinderModel) : D (u.1,circleAngular (circleTurn q.2) u.2)=u :=
    cylinderCover_derivative_right_inverse q u
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have hv := congrArg (fun Ω : Plane →L[ℝ] Plane →L[ℝ] ℝ =>
    Ω (v.1,circleAngular (circleTurn q.2) v.2) (w.1,circleAngular (circleTurn q.2) w.2)) he
  simp only [ContinuousLinearMap.bilinearComp_apply,smul_apply,smul_eq_mul] at hv
  rw [hd v,hd w] at hv
  simpa only [planarArea_apply,cylinderAreaForm_apply,cylinderCover,smul_apply,smul_eq_mul] using hv

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

namespace AnnularHandleData

theorem band_compact (b : ℝ) : IsCompact (band b) := isCompact_Icc.prod isCompact_univ

theorem core_compact (H : AnnularHandleData E M) (b : ℝ) : IsCompact (H.core b) :=
  isCompact_Icc.prod (isClosed_tsupport H.clock).isCompact

theorem core_subset_band (H : AnnularHandleData E M) (b : ℝ) : H.core b⊆band b :=
  prod_mono_right (subset_univ _)

theorem band_subset_source (H : AnnularHandleData E M) {b : ℝ} (hb : b<H.width) :
    band b⊆H.chart.source := by
  rw [H.source_eq]
  intro z hz
  exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,hz.2⟩

theorem image_core_compact (H : AnnularHandleData E M) {b : ℝ} (hb : b<H.width) :
    IsCompact (H.chart '' H.core b) :=
  (H.core_compact b).image_of_continuousOn
    (H.chart.contMDiffOn.continuousOn.mono ((H.core_subset_band b).trans (H.band_subset_source hb)))

end AnnularHandleData
end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem cylinderRadialForm_smooth (b : ℝ) (c : HandleCylinder) :
    ContDiffOn ℝ ∞ (chartOneForm (cylinderRadialForm b) c)
      (extChartAt 𝓘(ℝ,CylinderModel) c).target :=
  manifoldScalarDifferential_smooth ((intervalClock_smooth (-b) b).contMDiff.comp cylinder_fst_smooth) c

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
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

theorem density_smooth (H : AnnularHandleData E M) {b : ℝ} (hb : 0<b) (hbw : b<H.width) :
    SmoothTwoForm (H.density b) := by
  have hα := handlePushforwardOneForm_smooth H.chart (band_compact b) (H.band_subset_source hbw)
    (cylinderRadialForm_smooth b) (fun _ hx => cylinderRadialForm_zero hb hx)
  apply manifoldWedge_smooth
  · intro c
    exact (hα c).comp (f := fun y => ((0:ℝ),y))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)
  · intro c
    exact (H.dual_smooth c).comp (f := fun y => ((0:ℝ),y))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] in
theorem density_pullback (H : AnnularHandleData E M) (b : ℝ) {z : HandleCylinder}
    (hz : z∈H.chart.source) (v w : CylinderModel) :
    H.density b (H.chart z)
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart z v)
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart z w)=
      (deriv (intervalClock (-b) b) z.1*H.clock z.2)*cylinderAreaForm z v w := by
  have hα := handlePushforwardOneForm_pullback H.chart (cylinderRadialForm b) hz
  have hαv (u : CylinderModel) := congrArg (fun L : CylinderModel →L[ℝ] ℝ => L u) hα
  simp only [manifoldPullbackOneForm, manifoldMapDifferential,
    cylinderRadialForm_apply] at hαv
  let A : CylinderModel →L[ℝ] E := mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart z
  have hαv' (u : CylinderModel) :
      H.radial b (H.chart z) (A u) = deriv (intervalClock (-b) b) z.1 * u.1 := by
    simpa only [radial] using! hαv u
  have hβv (u : CylinderModel) :
      H.dual (H.chart z) (A u) = H.clock z.2 * circleAngular z.2 u.2 :=
    H.dual_pullback z hz u
  change manifoldWedge (H.radial b) H.dual (H.chart z) (A v) (A w) = _
  rw [manifoldWedge_apply, hαv' v, hαv' w, hβv v, hβv w, cylinderAreaForm_apply]
  ring

omit [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] in
theorem density_band_zero (H : AnnularHandleData E M) {b : ℝ} (hb : 0<b)
    {x : M} (hx : x∉H.chart '' band b) : H.density b x=0 := by
  have hz : H.radial b x=0 :=
    handlePushforwardOneForm_zero H.chart (fun _ hy => cylinderRadialForm_zero hb hy) hx
  ext v w
  simp [density,manifoldWedge_apply,hz]

omit [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] in
theorem density_core_zero (H : AnnularHandleData E M) {b : ℝ} (hb : 0<b) (hbw : b<H.width)
    {x : M} (hx : x∉H.chart '' H.core b) : H.density b x=0 := by
  by_cases hxb : x∈H.chart '' band b
  · obtain ⟨z,hz,rfl⟩ := hxb
    have hzs := H.band_subset_source hbw hz
    have hclk : H.clock z.2=0 := image_eq_zero_of_notMem_tsupport (fun ht => hx ⟨z,⟨hz.1,ht⟩,rfl⟩)
    let A := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) H.chart.symm (H.chart z)
    let B := mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart z
    have hBA : B.comp A=ContinuousLinearMap.id ℝ E := by
      have h := handle_mfderiv_symm_comp H.chart.symm (H.chart.map_source hzs)
      change (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart (H.chart.symm (H.chart z))).comp A=_ at h
      erw [H.chart.left_inv hzs] at h
      exact h
    have hi (v : E) : B (A v)=v := congrArg (fun D : E →L[ℝ] E => D v) hBA
    ext v w
    have hp := H.density_pullback b hzs (A v) (A w)
    change H.density b (H.chart z) (B (A v)) (B (A w))=_ at hp
    simpa only [hi,hclk,mul_zero,zero_mul,zero_apply] using hp
  · exact H.density_band_zero hb hxb

omit [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] in
theorem density_cover (H : AnnularHandleData E M) (b : ℝ) {q : Plane}
    (hq : cylinderCover q∈H.chart.source) (v w : Plane) :
    H.density b (H.chart (cylinderCover q))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (H.chart ∘ cylinderCover) q v)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (H.chart ∘ cylinderCover) q w)=
      (deriv (intervalClock (-b) b) q.1*H.clock (circleTurn q.2))*(v.1*w.2-v.2*w.1) := by
  rw [mfderiv_comp q (H.chart.mdifferentiableAt (by simp) hq)
    (cylinderCover_smooth.mdifferentiableAt (by simp))]
  change H.density b (H.chart (cylinderCover q))
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v))
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q w))=_
  erw [H.density_pullback b hq]
  erw [cylinderAreaForm_apply]
  erw [cylinderCover_derivative q v,cylinderCover_derivative q w]
  change (deriv (intervalClock (-b) b) q.1*H.clock (circleTurn q.2))*
    (v.1*circleAngular (circleTurn q.2) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn q.2 w.2)-
     circleAngular (circleTurn q.2) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn q.2 v.2)*w.1)=_
  erw [circleAngular_unit_pullback,circleAngular_unit_pullback]

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

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

theorem densityChart_contains (H : AnnularHandleData Plane M) {b : ℝ}
    (hb : b<H.width) : H.chart '' H.core b⊆H.densityChart.target := by
  rintro x ⟨z,hz,rfl⟩
  have ht : z.2∈positiveCircleCoordinate.target := by
    rw [positiveCircleCoordinate_target]
    exact H.clock_support hz.2
  obtain ⟨t,ht,heq⟩ := ht
  have hy : (z.1,t)∈H.densityChart.source := by
    rw [H.densityChart_source]
    exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,ht⟩
  have hi := H.densityChart.map_source hy
  have hev : H.densityChart (z.1,t)=H.chart z := congrArg H.chart (Prod.ext rfl heq)
  exact hev ▸ hi

end AnnularHandleData

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem partial_inverse_oneForm_smooth
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {β : ManifoldOneForm E M}
    (hβ : ∀ z∈e.source,ContDiffAt ℝ ∞ (chartOneForm β z) (extChartAt 𝓘(ℝ,E) z z))
    {x : N} (hx : x∈e.target) :
    ContDiffAt ℝ ∞
      (chartOneForm (manifoldPullbackOneForm (E := E) (F := F) (fun _ => β) e.symm 0) x)
      (extChartAt 𝓘(ℝ,F) x x) := by
  have hform := (hβ (e.symm x) (e.map_target hx)).comp
    ((0:ℝ),extChartAt 𝓘(ℝ,E) (e.symm x) (e.symm x)) contDiffAt_snd
  have hp := parameterManifoldPullbackOneForm_contDiffAt (α := fun _ : ℝ => β)
    hform (e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds hx))
  exact hp.comp (extChartAt 𝓘(ℝ,F) x x) (contDiffAt_const.prodMk contDiffAt_id)

theorem partial_inverse_oneForm_exterior
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {β : ManifoldOneForm E M} {Ω : ManifoldTwoForm F N}
    (hβ : ∀ z∈e.source,ContDiffAt ℝ ∞ (chartOneForm β z) (extChartAt 𝓘(ℝ,E) z z))
    (hcurv : ∀ z∈e.source,∀ v w,manifoldExteriorOneForm β z v w=Ω (e z)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e z v) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e z w))
    {x : N} (hx : x∈e.target) :
    manifoldExteriorOneForm
      (manifoldPullbackOneForm (E := E) (F := F) (fun _ => β) e.symm 0) x=Ω x := by
  rw [manifold_pullback_exterior_at (hβ (e.symm x) (e.map_target hx)) (e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds hx))]
  let A : F →L[ℝ] E := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e.symm x
  let B : E →L[ℝ] F := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e (e.symm x)
  have hAB : B.comp A=ContinuousLinearMap.id ℝ F := handle_mfderiv_symm_comp e.symm hx
  have hcancel (v : F) : B (A v)=v := congrArg (fun D : F →L[ℝ] F => D v) hAB
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change manifoldExteriorOneForm β (e.symm x) (A v) (A w)=Ω x v w
  have he := hcurv (e.symm x) (e.map_target hx) (A v) (A w)
  change manifoldExteriorOneForm β (e.symm x) (A v) (A w)=Ω (e (e.symm x)) (B (A v)) (B (A w)) at he
  rw [hcancel v,hcancel w] at he
  exact he.trans (congrArg (fun y => Ω y v w) (e.right_inv hx))

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularHandleCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem parameterEuclideanPullbackTwoForm_contDiffAt
    {α : P → ManifoldTwoForm E M} {g : F → M} {p : P × F}
    (hα : ContDiffAt ℝ ∞
      (fun q : P × E => chartTwoForm (α q.1) (g p.2) q.2)
      (p.1,extChartAt 𝓘(ℝ,E) (g p.2) (g p.2)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) :
    ContDiffAt ℝ ∞ (parameterEuclideanPullbackTwoForm α g) p := by
  let c := g p.2
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2 := hch.contDiffAt
  have hcoord : ContDiffAt ℝ ∞ (fun q : P × F => (q.1,extChartAt 𝓘(ℝ,E) c (g q.2))) p :=
    contDiffAt_fst.prodMk (hs.comp p contDiffAt_snd)
  have hform := hα.comp p hcoord
  have hder := (hs.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp p contDiffAt_snd
  have hsm := smooth_bilinear_flip ((smooth_bilinear_flip (hform.clm_comp hder)).clm_comp hder)
  apply hsm.congr_of_eventuallyEq
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
    continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
  exact euclideanPullbackTwoForm_chart (Ω := fun _ => α q.1) (p := (0,q.2))
    (hq.mdifferentiableAt (by simp)) hqc

variable {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartTwoForm_manifoldPullback_at {α : ℝ → ManifoldTwoForm E M} {e : N → M}
    {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target)
    (he : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) e ((extChartAt 𝓘(ℝ,F) b).symm p.2)) :
    chartTwoForm (manifoldPullbackTwoForm α e p.1) b p.2 =
      euclideanPullbackTwoForm α (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := (he.hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackTwoForm,hd,chartTwoForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v w
  rfl

omit [NormedSpace ℝ P] in

theorem parameterManifoldPullbackTwoForm_chart_germ
    (α : P → ManifoldTwoForm E M) {g : N → M} (p : P) {b : N}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g b) :
    (fun q : P × F => chartTwoForm (parameterManifoldPullbackTwoForm α g q.1) b q.2)
      =ᶠ[𝓝 (p,extChartAt 𝓘(ℝ,F) b b)]
    parameterEuclideanPullbackTwoForm α (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) := by
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hn₁ : {x | ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) 1 g x} ∈
      𝓝 ((extChartAt 𝓘(ℝ,F) b).symm (extChartAt 𝓘(ℝ,F) b b)) := by
    rw [he]; exact hn
  have hn' := (hi.continuousAt.comp (f := Prod.snd) (continuousAt_snd (p := (p,extChartAt 𝓘(ℝ,F) b b)))).preimage_mem_nhds hn₁
  filter_upwards [hn',continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)] with q hq hqt
  exact chartTwoForm_manifoldPullback_at (α := fun _ => α q.1) (p := (0,q.2)) hqt
    (hq.mdifferentiableAt (by simp))

theorem parameterManifoldPullbackTwoForm_contDiffAt
    {α : P → ManifoldTwoForm E M} {g : N → M} {p : P} {b : N}
    (hα : ContDiffAt ℝ ∞
      (fun q : P × E => chartTwoForm (α q.1) (g b) q.2)
      (p,extChartAt 𝓘(ℝ,E) (g b) (g b)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g b) :
    ContDiffAt ℝ ∞
      (fun q : P × F => chartTwoForm (parameterManifoldPullbackTwoForm α g q.1) b q.2)
      (p,extChartAt 𝓘(ℝ,F) b b) := by
  let y := extChartAt 𝓘(ℝ,F) b b
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy : y∈(extChartAt 𝓘(ℝ,F) b).target := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he : (extChartAt 𝓘(ℝ,F) b).symm y=b := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hg' : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g ((extChartAt 𝓘(ℝ,F) b).symm y) := by
    rw [he]; exact hg
  have hα' : ContDiffAt ℝ ∞
      (fun q : P × E => chartTwoForm (α q.1) ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y) q.2)
      (p,extChartAt 𝓘(ℝ,E) ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)
        ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)) := by
    simpa only [Function.comp_apply,he] using hα
  have hs := parameterEuclideanPullbackTwoForm_contDiffAt
    (α := α) (g := g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (p := (p,y)) hα' (hg'.comp y hi)
  exact hs.congr_of_eventuallyEq (parameterManifoldPullbackTwoForm_chart_germ α p hg)

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_AnnularSecondPositivity
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem cylinderAreaCoefficient_periodic (Λ : ManifoldTwoForm CylinderModel HandleCylinder)
    (s : ℝ) : Periodic (fun t => cylinderAreaCoefficient Λ (s,t)) 1 := by
  intro t
  have hq : (s,t+1)=(s,t)+(0,1) := by ext <;> simp
  change Λ (cylinderCover (s,t+1))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover (s,t+1) (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover (s,t+1) (0,1)) =
    Λ (cylinderCover (s,t))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover (s,t) (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover (s,t) (0,1))
  rw [hq,cylinderCover_period_one,cylinderCover_derivative_period_one]
  rfl

theorem cylinderAreaCoefficient_rep {Λ : ManifoldTwoForm CylinderModel HandleCylinder}
    (hsk : ∀ z v w,Λ z v w= -Λ z w v) (q : Plane) :
    Λ (cylinderCover q)=cylinderAreaCoefficient Λ q • cylinderAreaForm (cylinderCover q) := by
  let D : Plane →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q
  have hd (v : CylinderModel) : D (v.1,circleAngular (circleTurn q.2) v.2)=v :=
    cylinderCover_derivative_right_inverse q v
  have hs : ∀ v w,euclideanPullbackTwoForm (fun _ => Λ) cylinderCover (0,q) v w=
      -euclideanPullbackTwoForm (fun _ => Λ) cylinderCover (0,q) w v := by
    intro v w
    exact hsk _ _ _
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have hv := planar_skew_coefficient _ hs
    (v.1,circleAngular (circleTurn q.2) v.2) (w.1,circleAngular (circleTurn q.2) w.2)
  change Λ (cylinderCover q) (D _) (D _)=_ at hv
  rw [hd v,hd w] at hv
  simpa only [cylinderAreaCoefficient,planarArea_apply,cylinderAreaForm_apply,
    smul_apply,smul_eq_mul,cylinderCover] using hv

theorem exists_cylinder_area_primitive {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I) {Λ : ManifoldTwoForm CylinderModel HandleCylinder}
    (hΛ : ∀ z : HandleCylinder,z.1∈I → ContDiffAt ℝ ∞ (chartTwoForm Λ z)
      (extChartAt 𝓘(ℝ,CylinderModel) z z))
    (hsk : ∀ z v w,Λ z v w= -Λ z w v) :
    ∃ γ : ManifoldOneForm CylinderModel HandleCylinder,
      (∀ z : HandleCylinder,z.1∈I → ContDiffAt ℝ ∞ (chartOneForm γ z)
        (extChartAt 𝓘(ℝ,CylinderModel) z z)) ∧
      (∀ z : HandleCylinder,z.1∈I → manifoldExteriorOneForm γ z=Λ z) := by
  let κ : ℝ × Plane → ℝ := fun q => cylinderAreaCoefficient Λ q.2
  have hκ : ContDiffOn ℝ ∞ κ (univ ×ˢ (I ×ˢ univ)) := by
    intro q hq
    have hform := (hΛ (cylinderCover q.2) hq.2.1).comp
      (q.1,extChartAt 𝓘(ℝ,CylinderModel) (cylinderCover q.2) (cylinderCover q.2)) contDiffAt_snd
    have hs := parameterEuclideanPullbackTwoForm_contDiffAt (α := fun _ : ℝ => Λ)
      (p := q) hform cylinderCover_smooth.contMDiffAt
    exact ((hs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).contDiffWithinAt
  have hper : ∀ p∈(univ : Set ℝ),∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1 := by
    intro _ _ s _
    exact cylinderAreaCoefficient_periodic Λ s
  refine ⟨cylinderCurvaturePrimitive a κ 0,?_,?_⟩
  · intro z hz
    exact cylinderCurvaturePrimitive_smoothAt isOpen_univ hI hc ha hκ hper (mem_univ 0) hz
  · intro z hz
    let q : Plane := (z.1,shortCircleArgument z.2)
    have he : cylinderCover q=z := by
      apply Prod.ext
      · rfl
      · exact circleTurn_shortCircleArgument z.2
    rw [←he]
    exact (cylinderCurvaturePrimitive_exterior_covered isOpen_univ hI hc ha hκ hper
      (mem_univ 0) hz).trans (cylinderAreaCoefficient_rep hsk q).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_annular_area_primitive {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I)
    (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) HandleCylinder M ∞)
    (hsource : e.source=I ×ˢ univ)
    {Λ : ManifoldTwoForm E M} (hΛ : SmoothTwoForm Λ)
    (hsk : ∀ x v w,Λ x v w= -Λ x w v) :
    ∃ γ : ManifoldOneForm E M,
      (∀ x∈e.target,ContDiffAt ℝ ∞ (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x)) ∧
      (∀ x∈e.target,manifoldExteriorOneForm γ x=Λ x) := by
  let Ω : ManifoldTwoForm CylinderModel HandleCylinder :=
    manifoldPullbackTwoForm (E := E) (F := CylinderModel) (fun _ => Λ) e 0
  have hs (z : HandleCylinder) (hz : z.1∈I) : z∈e.source := by
    rw [hsource]; exact ⟨hz,mem_univ _⟩
  have hΩ (z : HandleCylinder) (hz : z.1∈I) :
      ContDiffAt ℝ ∞ (chartTwoForm Ω z) (extChartAt 𝓘(ℝ,CylinderModel) z z) := by
    have hd := e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hs z hz))
    have hform := ((hΛ (e z)).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) (e z)).mem_nhds
        ((extChartAt 𝓘(ℝ,E) (e z)).map_source (mem_extChartAt_source (e z))))).comp
      ((0:ℝ),extChartAt 𝓘(ℝ,E) (e z) (e z)) contDiffAt_snd
    have hp := parameterManifoldPullbackTwoForm_contDiffAt (α := fun _ : ℝ => Λ) hform hd
    exact hp.comp (extChartAt 𝓘(ℝ,CylinderModel) z z)
      (contDiffAt_const.prodMk contDiffAt_id)
  have hskΩ : ∀ z v w,Ω z v w= -Ω z w v := fun _ _ _ => hsk _ _ _
  obtain ⟨γc,hγc,hdγc⟩ := exists_cylinder_area_primitive hI hc ha hΩ hskΩ
  let γ : ManifoldOneForm E M :=
    manifoldPullbackOneForm (E := CylinderModel) (F := E) (fun _ => γc) e.symm 0
  refine ⟨γ,?_,?_⟩
  · intro x hx
    apply partial_inverse_oneForm_smooth e (x := x) ?_ hx
    intro z hz
    exact hγc z (by rw [hsource] at hz; exact hz.1)
  · intro x hx
    apply partial_inverse_oneForm_exterior e (x := x) ?_ ?_ hx
    · intro z hz
      exact hγc z (by rw [hsource] at hz; exact hz.1)
    · intro z hz v w
      have hd := hdγc z (by rw [hsource] at hz; exact hz.1)
      exact congrArg (fun A : CylinderModel →L[ℝ] CylinderModel →L[ℝ] ℝ => A v w) hd

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem clockPrimitive_smooth
    (H : AnnularHandleData E M) (b : ℝ)
    {x : M} (hx : x∈H.chart.target) :
    ContDiffAt ℝ ∞ (chartOneForm (H.clockPrimitive b) x)
      (extChartAt 𝓘(ℝ,E) x x) :=
  partial_inverse_oneForm_smooth H.chart
    (fun z _ => cylinderClockPrimitive_smoothAt (intervalClock_smooth (-b) b) H.clock_smooth z) hx

theorem clockPrimitive_exterior
    (H : AnnularHandleData E M) (b : ℝ)
    {x : M} (hx : x∈H.chart.target) :
    manifoldExteriorOneForm (H.clockPrimitive b) x=H.density b x := by
  apply partial_inverse_oneForm_exterior H.chart
    (fun z _ => cylinderClockPrimitive_smoothAt (intervalClock_smooth (-b) b) H.clock_smooth z) _ hx
  intro z hz v w
  rw [cylinderClockPrimitive_exterior (intervalClock_smooth (-b) b) H.clock_smooth]
  exact (H.density_pullback b hz v w).symm

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem clockPrimitive_eq
    (H : AnnularHandleData E M) (b : ℝ) {x : M} (hx : x∈H.chart.target) :
    H.clockPrimitive b x=
      intervalClock (-b) b (H.chart.symm x).1 • H.dual x := by
  let c := H.chart
  let z := c.symm x
  let A : E →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) c.symm x
  let B : CylinderModel →L[ℝ] E := mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) c z
  have hAB : B.comp A=ContinuousLinearMap.id ℝ E := handle_mfderiv_symm_comp c.symm hx
  have hc (v : E) : B (A v)=v := congrArg (fun D : E →L[ℝ] E => D v) hAB
  apply ContinuousLinearMap.ext
  intro v
  have hβ := H.dual_pullback z (c.map_target hx) (A v)
  change H.dual (c z) (B (A v))=H.clock z.2*circleAngular z.2 (A v).2 at hβ
  rw [hc v,show c z=x from c.right_inv hx] at hβ
  change (intervalClock (-b) b z.1*H.clock z.2)*cylinderAngular z (A v)=
    intervalClock (-b) b z.1*H.dual x v
  rw [cylinderAngular_apply,hβ]
  ring

end
section

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_normal_form
    (D : AnnularHandleData E M) (b q : ℝ)
    {Λ : ManifoldTwoForm E M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x v w,Λ x v w= -Λ x w v)
    {H : P → ℝ} (hH : ContDiff ℝ ∞ H) :
    ∃ (γ : ManifoldOneForm E M) (N : P → ManifoldOneForm E M),
      (∀ x∈D.chart.target,ContDiffAt ℝ ∞
        (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x)) ∧
      (∀ x∈D.chart.target,manifoldExteriorOneForm γ x=q • Λ x) ∧
      (∀ p,∀ x∈D.chart.target,ContDiffAt ℝ ∞
        (fun z : P × E => chartOneForm (N z.1) x z.2) (p,extChartAt 𝓘(ℝ,E) x x)) ∧
      (∀ p,∀ x∈D.chart.target,
        manifoldExteriorOneForm (N p) x=q • Λ x+H p • D.density b x) ∧
      (∀ p,∀ x∈D.chart.target,N p x=γ x+
        (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x) := by
  obtain ⟨γ₀,hγ₀,hdγ₀⟩ := exists_annular_area_primitive isOpen_Ioo (convex_Ioo (-D.width) D.width)
    (a := 0) ⟨by linarith [D.width_pos],D.width_pos⟩ D.chart D.source_eq hΛ hsΛ
  let γ : ManifoldOneForm E M := q • γ₀
  let C := D.clockPrimitive b
  let N : P → ManifoldOneForm E M := fun p => γ+H p • C
  have hγ (x : M) (hx : x∈D.chart.target) :
      ContDiffAt ℝ ∞ (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x) := by
    rw [show chartOneForm γ x=(fun y => q • chartOneForm γ₀ x y) from
      funext (chartOneForm_smul q γ₀ x)]
    exact (contDiffAt_const (c := q)).smul (hγ₀ x hx)
  have hdγ (x : M) (hx : x∈D.chart.target) :
      manifoldExteriorOneForm γ x=q • Λ x := by
    rw [manifoldExteriorOneForm_smul_at q (hγ₀ x hx),hdγ₀ x hx]
  have hC (x : M) (hx : x∈D.chart.target) :
      ContDiffAt ℝ ∞ (chartOneForm C x) (extChartAt 𝓘(ℝ,E) x x) :=
    D.clockPrimitive_smooth b hx
  refine ⟨γ,N,hγ,hdγ,?_,?_,?_⟩
  · intro p x hx
    have h1 := (hγ x hx).comp (p,extChartAt 𝓘(ℝ,E) x x) contDiffAt_snd
    have h2 := (hC x hx).comp (p,extChartAt 𝓘(ℝ,E) x x) contDiffAt_snd
    have h3 := h1.add ((hH.contDiffAt.comp _ contDiffAt_fst).smul h2)
    change ContDiffAt ℝ ∞ (fun z : P × E =>
      chartOneForm γ x z.2+H z.1 • chartOneForm C x z.2) _ at h3
    simpa only [N,chartOneForm_add,chartOneForm_smul] using h3
  · intro p x hx
    have hs : ContDiffAt ℝ ∞ (chartOneForm (H p • C) x) (extChartAt 𝓘(ℝ,E) x x) := by
      rw [show chartOneForm (H p • C) x=(fun y => H p • chartOneForm C x y) from
        funext (chartOneForm_smul (H p) C x)]
      exact (contDiffAt_const (c := H p)).smul (hC x hx)
    change manifoldExteriorOneForm (γ+H p • C) x=_
    rw [manifoldExteriorOneForm_add_at (hγ x hx) hs,hdγ x hx,
      manifoldExteriorOneForm_smul_at (H p) (hC x hx),
      D.clockPrimitive_exterior b hx]
  · intro p x hx
    change γ x+H p • C x=_
    rw [show C x=_ from D.clockPrimitive_eq b hx,smul_smul,mul_comm (H p)]

end

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfaceInteriorBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {I : Type*} {K L : Set M}

theorem restrictSurfacePartition_subordinate
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (hLK : L⊆K)
    {V : I → Set M} (hρ : ρ.IsSubordinate V) :
    (restrictSurfacePartition ρ hLK).IsSubordinate V := hρ

end

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  {K : Set M}

theorem exists_normalized_surface_primitive
    (D : AnnularHandleData Plane M) {b : ℝ} (hb : b<D.width)
    (heK : D.chart.target⊆interior K) (hβK : tsupport D.dual⊆interior K)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x v w,Λ x v w= -Λ x w v)
    {q : ℝ} {H : P → ℝ} (hH : ContDiff ℝ ∞ H)
    {κ Ξ : P → ManifoldTwoForm Plane M} {Γ₀ : P → ManifoldOneForm Plane M}
    (hΓ₀ : SmoothOneFormFamily Γ₀)
    (hdΓ₀ : ∀ p x,manifoldExteriorOneForm (Γ₀ p) x=κ p x)
    (hΞ : HasInteriorPrimitiveFamily (interior K) Ξ)
    (hformula : ∀ p,∀ x∈D.chart.target,
      κ p x+Ξ p x=q • Λ x+H p • D.density b x) :
    ∃ (Γ₁ : P → ManifoldOneForm Plane M) (γ : ManifoldOneForm Plane M) (L W : Set M),
      SmoothOneFormFamily Γ₁ ∧ IsCompact L ∧ L⊆interior K ∧ IsOpen W ∧
      D.chart '' band b⊆W ∧ W⊆D.chart.target ∧
      (∀ p x,x∉L→Γ₁ p x=Γ₀ p x) ∧
      (∀ p x,manifoldExteriorOneForm (Γ₁ p) x=κ p x+Ξ p x) ∧
      (∀ x∈D.chart.target,ContDiffAt ℝ ∞
        (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x)) ∧
      (∀ x∈D.chart.target,manifoldExteriorOneForm γ x=q • Λ x) ∧
      (∀ p,∀ x∈W,Γ₁ p x=γ x+
        (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x) := by
  obtain ⟨L₀,hL₀,hL₀K,α,hα,hαz⟩ := hΞ
  let Γ : P → ManifoldOneForm Plane M := Γ₀+α
  have hΓ : SmoothOneFormFamily Γ := by
    intro c
    simpa only [Γ,Pi.add_apply,chartOneForm_add] using (hΓ₀ c).add (hα.smooth c)
  have hdΓ (p : P) (x : M) : manifoldExteriorOneForm (Γ p) x=κ p x+Ξ p x := by
    have hx := (extChartAt 𝓘(ℝ,Plane) x).map_source (mem_extChartAt_source (I := 𝓘(ℝ,Plane)) x)
    change manifoldExteriorOneForm (Γ₀ p+α p) x=_
    rw [manifoldExteriorOneForm_add_at (hΓ₀.spatial_smooth p x hx)
      (hα.smooth.spatial_smooth p x hx),hdΓ₀ p x,hα.intrinsic p x]
  obtain ⟨γ,N,hγ,hdγ,hN,hdN,hNeq⟩ :=
    D.exists_normal_form b q hΛ hsΛ hH
  obtain ⟨Γ₁,L₁,W,hL₁,hL₁A,hW,hband,hWA,hΓ₁,hsub,_,hdΓ₁,hΓ₁N⟩ :=
    D.normalize_primitive_bp240 (P := P) isOpen_univ hb
      hΓ (fun p _ x hx => hN p x hx) (fun p _ x hx =>
        (hdΓ p x).trans ((hformula p x hx).trans (hdN p x hx).symm))
  let L := L₀∪tsupport (D.dual)∪L₁
  refine ⟨Γ₁,γ,L,W,hΓ₁,(hL₀.union D.dual_compact).union hL₁,
    union_subset (union_subset hL₀K hβK) (hL₁A.trans heK),hW,hband,hWA,?_,?_,hγ,hdγ,?_⟩
  · intro p x hx
    have h0 : α p x=0 := hαz p x (fun hk => hx (Or.inl (Or.inl hk)))
    have h1 : (Γ₁ p-Γ p) x=0 := by
      apply notMem_support.mp
      intro hs
      have hmem := hsub p hs
      exact hmem.elim (fun h => hx (Or.inl (Or.inr h))) (fun h => hx (Or.inr h))
    have heq : Γ₁ p x=Γ p x := sub_eq_zero.mp h1
    simpa only [Γ,Pi.add_apply,h0,add_zero] using heq
  · intro p x
    exact (hdΓ₁ p (mem_univ p) x).trans (hdΓ p x)
  · intro p x hx
    exact (hΓ₁N p (mem_univ p) x hx).trans (hNeq p x (hWA hx))

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_AnnularDensityMass
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open scoped BigOperators
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem densityChart_coefficient (H : AnnularHandleData Plane M) (b : ℝ) {y : Plane}
    (hy : y∈H.densityChart.source) :
    partialChartCoefficient H.densityChart (H.density b) y=
      deriv (intervalClock (-b) b) y.1*H.clock (circleTurn y.2) := by
  have hh := H.density_cover b hy.2 (1,0) (0,1)
  unfold partialChartCoefficient euclideanPullbackTwoForm
  have heq : (H.densityChart : Plane → M)=H.chart ∘ cylinderCover := rfl
  rw [heq]
  simpa only [mul_one, mul_zero, sub_zero] using! hh

omit [T2Space M] in
theorem density_nonnegative (H : AnnularHandleData Plane M) {b : ℝ} (hb : 0<b)
    (hbw : b<H.width) (hor : PositivePartialChart H.densityChart) (c : M) {y : Plane}
    (hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target) :
    0 ≤ chartTwoForm (H.density b) c y (1,0) (0,1) := by
  let d := H.densityChart
  let x := (extChartAt 𝓘(ℝ,Plane) c).symm y
  have hxc : x∈(extChartAt 𝓘(ℝ,Plane) c).source :=
    (extChartAt 𝓘(ℝ,Plane) c).map_target hy
  have hxy : extChartAt 𝓘(ℝ,Plane) c x=y :=
    (extChartAt 𝓘(ℝ,Plane) c).right_inv hy
  by_cases hx : x∈H.chart '' H.core b
  · have hxd : x∈d.target := H.densityChart_contains hbw hx
    let z := d.symm x
    have hzs : z∈d.source := d.map_target hxd
    have hzx : d z=x := d.right_inv hxd
    have hzc : d z∈(extChartAt 𝓘(ℝ,Plane) c).source := hzx.symm ▸ hxc
    have hdet := hor c z hzs hzc
    have hcoef : 0≤partialChartCoefficient d (H.density b) z := by
      rw [H.densityChart_coefficient b hzs]
      exact mul_nonneg (intervalClock_deriv_nonneg (by linarith) _) (H.clock_nonneg _)
    have hchange := partialChartCoefficient_change d (Ω := H.density b)
      (manifoldWedge_skew _ _) hzs hzc
    have hcy : extChartAt 𝓘(ℝ,Plane) c (d z)=y := (congrArg _ hzx).trans hxy
    rw [hchange,hcy] at hcoef
    exact nonneg_of_mul_nonneg_right hcoef hdet
  · have hz := H.density_core_zero hb hbw hx
    unfold chartTwoForm
    change 0≤((H.density b x).bilinearComp _ _) (1,0) (0,1)
    rw [hz]
    rfl

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem rectangle_integral (H : AnnularHandleData Plane M) {b : ℝ} (hb : 0<b) (hbw : b<H.width) :
    (∫ y in Ioo (-H.width) H.width ×ˢ Ioo (0:ℝ) 1,
      deriv (intervalClock (-b) b) y.1*H.clock (circleTurn y.2))=1 := by
  have hr : (∫ s in -H.width..H.width,deriv (intervalClock (-b) b) s)=1 := by
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun s _ => (intervalClock_smooth (-b) b).differentiable (by simp) s)
      ((intervalClock_deriv_smooth (-b) b).continuous.intervalIntegrable _ _)]
    rw [intervalClock_one (by linarith : -b<b) hbw.le,
      intervalClock_zero (by linarith : -b<b) (by linarith)]
    norm_num
  rw [Measure.volume_eq_prod,setIntegral_prod_mul
    (fun s => deriv (intervalClock (-b) b) s) (fun t => H.clock (circleTurn t)),
    ← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by linarith : -H.width≤H.width),
    hr,one_mul,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  exact H.clock_integral

theorem density_mass (H : AnnularHandleData Plane M) {b : ℝ} (hb : 0<b) (hbw : b<H.width)
    (hor : PositivePartialChart H.densityChart)
    {I : Type*} [Fintype I] (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M (H.chart '' H.core b))
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) :
    partitionFormMass B ρ (H.density b)=1 := by
  let d := H.densityChart
  let K := H.chart '' H.core b
  let R := Ioo (-H.width) H.width ×ˢ Ioo (0:ℝ) 1
  have hK : IsCompact K := H.image_core_compact hbw
  have hKe : K⊆d.target := H.densityChart_contains hbw
  have hsrc : d.source=R := H.densityChart_source
  have hsub : d.symm '' K⊆R := by
    rintro y ⟨x,hx,rfl⟩
    rw [← hsrc]
    exact d.map_target (hKe hx)
  have heq := partitionFormMass_eq_partialChart_integral d hor hK hKe B ρ hρ
    (H.density_smooth hb hbw) (manifoldWedge_skew _ _) (fun _ hx => H.density_core_zero hb hbw hx)
  rw [heq]
  have hlarge : (∫ y in R,partialChartCoefficient d (H.density b) y)=
      ∫ y in d.symm '' K,partialChartCoefficient d (H.density b) y := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isOpen_Ioo.prod isOpen_Ioo).measurableSet hsub
    intro y hy
    have hys : y∈d.source := hsrc.symm ▸ hy.1
    have hn : d y∉K := by
      intro hk
      exact hy.2 ⟨d y,hk,d.left_inv hys⟩
    have hz := H.density_core_zero hb hbw hn
    simp only [partialChartCoefficient,euclideanPullbackTwoForm,hz]
    rfl
  rw [← hlarge]
  calc
    _ = ∫ y in R,deriv (intervalClock (-b) b) y.1*H.clock (circleTurn y.2) := by
      apply setIntegral_congr_fun (isOpen_Ioo.prod isOpen_Ioo).measurableSet
      intro y hy
      exact H.densityChart_coefficient b (hsrc.symm ▸ hy)
    _ = 1 := H.rectangle_integral hb hbw

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]
  {I : Type*} [Fintype I] {K : Set M}

theorem exists_surface_step_two_bp240_oai
    (hK : IsCompact K) (hc : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
    (hor : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' frontier K)=0)
    (D : AnnularHandleData Plane M) {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (heK : closure D.chart.target⊆interior K) (hβK : tsupport D.dual⊆interior K)
    (heor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 < chartTwoForm Λ c y (1,0) (0,1))
    {c : P × M → ℝ} (hs : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ c)
    {Y : Set P} (hY : IsCompact Y) (hcp : ∀ p∈Y,∀ x∈K,0 < c (p,x))
    {Γ₀ : P → ManifoldOneForm Plane M} (hΓ₀ : SmoothOneFormFamily Γ₀)
    (hdΓ₀ : ∀ p x,manifoldExteriorOneForm (Γ₀ p) x=c (p,x) • Λ x)
    {A : P → ℝ} {ε : ℝ} (hε : 0<ε) (hA : ∀ p∈Y,2*ε<A p)
    (herr : ∀ p∈Y,|restrictedPartitionFormMass B ρ K (fun x => c (p,x) • Λ x)-A p|<ε) :
    ∃ (q : ℝ) (s : P × M → ℝ) (H : P → ℝ)
      (Γ₁ : P → ManifoldOneForm Plane M) (γ : ManifoldOneForm Plane M) (L W : Set M),
      0<q ∧ ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ s ∧ ContDiff ℝ ∞ H ∧
      (∀ p,H p=restrictedPartitionFormMass B ρ K (fun x => c (p,x) • Λ x)-
        restrictedPartitionFormMass B ρ K (fun x => s (p,x) • Λ x)) ∧
      (∀ p∈Y,0<H p ∧ |H p-A p|<2*ε) ∧
      SmoothOneFormFamily Γ₁ ∧ IsCompact L ∧ L⊆interior K ∧ IsOpen W ∧
      D.chart '' band b⊆W ∧ W⊆D.chart.target ∧
      (∀ p x,x∉L→Γ₁ p x=Γ₀ p x) ∧
      (∀ p x,x∈K→manifoldExteriorOneForm (Γ₁ p) x=
        s (p,x) • Λ x+H p • D.density b x) ∧
      (∀ p∈Y,∀ z y,y∈(extChartAt 𝓘(ℝ,Plane) z).target→
        (extChartAt 𝓘(ℝ,Plane) z).symm y∈K→
        0 < chartTwoForm (manifoldExteriorOneForm (Γ₁ p)) z y (1,0) (0,1)) ∧
      (∀ p x,x∈D.chart.target→s (p,x)=q) ∧
      (∀ x∈D.chart.target,ContDiffAt ℝ ∞
        (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x)) ∧
      (∀ x∈D.chart.target,manifoldExteriorOneForm γ x=q • Λ x) ∧
      (∀ p,∀ x∈W,Γ₁ p x=γ x+
        (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x) ∧
      (∀ p∈Y,∀ x∈K,0 < s (p,x)) ∧
      (∀ p∈Y,restrictedPartitionFormMass B ρ K (fun x => s (p,x) • Λ x)<ε) ∧
      (∃ U : Set M,IsOpen U ∧ frontier K⊆U ∧ ∀ p x,x∈U→s (p,x)=c (p,x)) := by
  let Z := closure D.chart.target
  have hdis : Disjoint (frontier K) Z := disjoint_interior_frontier.symm.mono_right heK
  have hAK : D.chart.target⊆interior K := subset_closure.trans heK
  let T := D.chart '' D.core b
  have hT : IsCompact T := D.image_core_compact hbw
  have hTK : T⊆interior K := by
    rintro _ ⟨z,hz,rfl⟩
    exact hAK (D.chart.map_source (D.band_subset_source hbw (D.core_subset_band b hz)))
  have hmass : partitionFormMass B ρ (D.density b)=1 :=
    D.density_mass hb hbw heor B
      (restrictSurfacePartition ρ (hTK.trans interior_subset))
      (restrictSurfacePartition_subordinate ρ _ hρ)
  obtain ⟨q,s,H,Ξ,hq,hs',hH,hΞ,hm,hbound,hform,hpos,hsZ,hprim,hsp,hsarea,hscollar⟩ :=
    exists_surface_area_redistribution_bp240 hK hc hne hor B ρ hρ hnull isClosed_closure hdis
      hΛ hsΛ hpΛ hs hY hcp
      (D.density_smooth hb hbw)
      (manifoldWedge_skew _ _)
      (fun z y hy => D.density_nonnegative hb hbw heor z hy)
      hT hTK (fun _ hx => D.density_core_zero hb hbw hx) hmass hε hA herr
  have hAZ : D.chart.target⊆Z := subset_closure
  have hNF (p : P) (x : M) (hx : x∈D.chart.target) :
      c (p,x) • Λ x+Ξ p x=q • Λ x+H p • D.density b x := by
    rw [hform p x (interior_subset (hAK hx)),hsZ p x (hAZ hx)]
  obtain ⟨Γ₁,γ,L,W,hΓ₁,hL,hLK,hW,hBW,hWA,haway,hdΓ₁,hγ,hdγ,hN⟩ :=
    D.exists_normalized_surface_primitive hbw hAK hβK
      hΛ hsΛ hH hΓ₀ hdΓ₀ hprim hNF
  refine ⟨q,s,H,Γ₁,γ,L,W,hq,hs',hH,hm,hbound,hΓ₁,hL,hLK,hW,hBW,hWA,haway,
    (fun p x hx => (hdΓ₁ p x).trans (hform p x hx)),?_,
    (fun p x hx => hsZ p x (hAZ hx)),hγ,hdγ,hN,hsp,hsarea,hscollar⟩
  intro p hp z y hy hk
  have heq : manifoldExteriorOneForm (Γ₁ p)=fun x => c (p,x) • Λ x+Ξ p x := funext (hdΓ₁ p)
  rw [heq]
  exact hpos p hp z y hy hk

end

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_step_two_bp240_oai.{u_1} := @OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_step_two_bp240_oai.{u_1}
