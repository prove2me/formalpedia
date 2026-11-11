-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.exists_actual_compact_normalized_dual_fixed_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:48.805997+00:00
-- url     : https://prove2.me/submissions/a3b0b54f-e1fe-4024-85ab-665acdaf2e53

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

theorem manifold_pullback_exterior_on {α : ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    {g : N → M} {U : Set N} (hU : IsOpen U)
    (hg : ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g U) {b : N} (hbU : b ∈ U) :
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
    exact hg.contMDiffAt (hU.mem_nhds hbU)
  have hc : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y :=
    hgy.comp y hi
  have hu : ∀ᶠ z in 𝓝 y, (extChartAt 𝓘(ℝ,F) b).symm z ∈ U :=
    hi.continuousAt.preimage_mem_nhds (hU.mem_nhds (he.symm ▸ hbU))
  have hh : chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =ᶠ[𝓝 y]
      fun z => euclideanPullbackOneForm (fun _ => α) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (0,z) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy,hu] with z hz hzU
    exact chartOneForm_manifoldPullback_at (α := fun _ => α) (b := b) (p := (0,z)) hz
      ((hg.contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt (by simp))
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

theorem extendManifoldOneForm_exterior_inside {U : Set M} (hU : IsOpen U)
    (α : ManifoldOneForm E M) {x : M} (hx : x ∈ U) :
    manifoldExteriorOneForm (extendManifoldOneForm U α) x=manifoldExteriorOneForm α x := by
  apply manifoldExteriorOneForm_congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact extendManifoldOneForm_inside hy

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

theorem manifoldScalarDifferential_closed {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f) (x : M) :
    manifoldExteriorOneForm (manifoldScalarDifferential (E := E) f) x=0 := by
  have hx : extChartAt 𝓘(ℝ,E) x x∈(extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x)
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hx
  have hs := (manifoldScalar_chart_smooth hf x).contDiffAt hn
  have he : chartOneForm (manifoldScalarDifferential f) x =ᶠ[𝓝 (extChartAt 𝓘(ℝ,E) x x)]
      fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ,E) x).symm) := by
    filter_upwards [hn] with z hz
    exact manifoldScalarDifferential_chart hf hz
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ (chartOneForm (manifoldScalarDifferential f) x)
      (extChartAt 𝓘(ℝ,E) x x) (chartDifferential x x u) (chartDifferential x x v)-
    fderiv ℝ (chartOneForm (manifoldScalarDifferential f) x)
      (extChartAt 𝓘(ℝ,E) x x) (chartDifferential x x v) (chartDifferential x x u)=0
  rw [he.fderiv_eq]
  exact sub_eq_zero.mpr ((hs.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)).eq _ _)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifoldScalarDifferential_support (f : M → ℝ) :
    support (manifoldScalarDifferential (E := E) f) ⊆ tsupport f := by
  intro x hx
  by_contra hn
  have he : f =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with y hy
    exact notMem_support.mp (fun hs => hy (subset_closure hs))
  apply hx
  exact he.mfderiv_eq.trans (by
    first
      | (rw [mfderiv_const,ContinuousLinearMap.comp_zero]; rfl)
      | (rw [mfderiv_const]; rfl)
      | simp [mfderiv_const])


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldExteriorAlgebra
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
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
theorem manifoldExteriorOneForm_sub {α β : ManifoldOneForm E M}
    (hα : ∀ c,ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target)
    (x : M) : manifoldExteriorOneForm (α-β) x=
      manifoldExteriorOneForm α x-manifoldExteriorOneForm β x := by
  have hx : extChartAt 𝓘(ℝ,E) x x∈(extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x)
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hx
  have he : chartOneForm (α-β) x=chartOneForm α x-chartOneForm β x :=
    funext (chartOneForm_sub α β x)
  simp only [manifoldExteriorOneForm,euclideanExteriorOneForm,he,
    fderiv_sub ((hα x).contDiffAt hn |>.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      ((hβ x).contDiffAt hn |>.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.bilinearComp_apply,sub_apply,
    ContinuousLinearMap.flip_apply]
  ring

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

theorem manifold_closed_exact_normalization {α β : ManifoldOneForm E M}
    (hα : ∀ c,ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target)
    (hclosed : ∀ x,manifoldExteriorOneForm β x=0)
    {F : M → ℝ} (hF : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ F) (a : ℝ) (x : M) :
    manifoldExteriorOneForm (α-a • β-manifoldScalarDifferential F) x=
      manifoldExteriorOneForm α x := by
  have hb : ∀ c,ContDiffOn ℝ ∞ (chartOneForm (a • β) c)
      (extChartAt 𝓘(ℝ,E) c).target := by
    intro c
    simpa only [show chartOneForm (a • β) c=fun y => a • chartOneForm β c y
      from funext (chartOneForm_smul a β c)] using (hβ c).const_smul a
  have hab : ∀ c,ContDiffOn ℝ ∞ (chartOneForm (α-a • β) c)
      (extChartAt 𝓘(ℝ,E) c).target := by
    intro c
    exact ((hα c).sub (hb c)).congr (fun y _ => chartOneForm_sub α (a • β) c y)
  rw [manifoldExteriorOneForm_sub hab (manifoldScalarDifferential_smooth hF),
    manifoldScalarDifferential_closed hF,manifoldExteriorOneForm_sub hα hb,
    manifoldExteriorOneForm_smul a hβ,hclosed]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_smooth_manifold_cutoff {K U : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ (∀ x, χ x ∈ Icc (0:ℝ) 1) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  obtain ⟨D,hD,hKD,hDU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχ⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ,E) hK.isClosed hKD
  have hs : tsupport (χ : M → ℝ) ⊆ D :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hχ0 x hn)) hD.isClosed
  exact ⟨χ,χ.contMDiff,HasCompactSupport.of_support_subset_isCompact hD
    ((subset_tsupport χ).trans hs),hs.trans hDU,hχ1,hχ⟩


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem scalar_product_tsupport_left (F ζ : M → ℝ) :
    tsupport (fun x => ζ x*F x) ⊆ tsupport ζ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply subset_closure
  intro hzero
  exact hx (by simp only [hzero,zero_mul])


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem manifoldFamily_local_potential_smoothOn {V : Set P} {A : Set M}
    (hV : IsOpen V) (hA : IsOpen A) {F : P × M → ℝ} {ζ : M → ℝ}
    (hF : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ A))
    (hζ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ ζ) (hs : tsupport ζ ⊆ A) :
    ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun q : P × M => ζ q.2*F q) (V ×ˢ univ) := by
  intro q hq
  by_cases hy : q.2∈A
  · exact ((hζ.comp contMDiff_snd).contMDiffAt.mul
      (hF.contMDiffAt ((hV.prod hA).mem_nhds ⟨hq.1,hy⟩))).contMDiffWithinAt
  · have ht : q.2∉tsupport ζ := fun ht => hy (hs ht)
    have he : (fun y : P × M => ζ y.2*F y) =ᶠ[𝓝 q] (fun _ => (0:ℝ)) := by
      have hn := (continuous_snd.continuousAt : ContinuousAt (Prod.snd : P × M → M) q)
      filter_upwards [hn (isClosed_closure.isOpen_compl.mem_nhds ht)] with y hy
      have hz : ζ y.2=0 := notMem_support.mp (fun hv => hy (subset_closure hv))
      simp only [hz,zero_mul]
    exact ((contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq he).contMDiffWithinAt

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_joint_global_local_potential {V : Set P} {K A : Set M}
    (hV : IsOpen V) (hK : IsCompact K) (hA : IsOpen A) (hKA : K ⊆ A)
    {F : P × M → ℝ}
    (hF : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ A)) :
    ∃ (G : P × M → ℝ) (L : Set M), IsCompact L ∧ L ⊆ A ∧
      ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ G (V ×ˢ univ) ∧
      (∀ p,tsupport (fun y => G (p,y)) ⊆ L) ∧
      (∀ᶠ y in 𝓝ˢ K,∀ p,G (p,y)=F (p,y)) ∧
      (∀ p,support (manifoldScalarDifferential (E := E) (fun y => G (p,y))) ⊆ L) ∧
      (∀ p ∈ V,∀ y,manifoldExteriorOneForm
        (manifoldScalarDifferential (E := E) (fun z => G (p,z))) y=0) ∧
      (∀ p,∀ y ∈ K,manifoldScalarDifferential (E := E) (fun z => G (p,z)) y=
        manifoldScalarDifferential (E := E) (fun z => F (p,z)) y) := by
  obtain ⟨ζ,hζ,hζc,hζA,hζ1,_⟩ := exists_smooth_manifold_cutoff (E := E) hK hA hKA
  let G : P × M → ℝ := fun q => ζ q.2*F q
  have hG := manifoldFamily_local_potential_smoothOn hV hA hF hζ hζA
  have hs : ∀ p,tsupport (fun y => G (p,y)) ⊆ tsupport ζ :=
    fun p => scalar_product_tsupport_left (fun y => F (p,y)) ζ
  have he : ∀ᶠ y in 𝓝ˢ K,∀ p,G (p,y)=F (p,y) := by
    filter_upwards [hζ1] with y hy p
    simp only [G,hy,one_mul]
  refine ⟨G,tsupport ζ,hζc,hζA,hG,hs,he,?_,?_,?_⟩
  · intro p
    exact (manifoldScalarDifferential_support (fun y => G (p,y))).trans (hs p)
  · intro p hp y
    have hfib : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun z => G (p,z)) := by
      intro z
      exact (hG.contMDiffAt (((hV.prod isOpen_univ)).mem_nhds ⟨hp,mem_univ z⟩)).comp z
        (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact manifoldScalarDifferential_closed hfib y
  · intro p y hy
    have he' : (fun z => G (p,z)) =ᶠ[𝓝 y] (fun z => F (p,z)) := by
      filter_upwards [he.filter_mono (nhds_le_nhdsSet hy)] with z hz
      exact hz p
    exact he'.mfderiv_eq


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldFamily_scalar_fiber_smooth {V : Set P} (hV : IsOpen V)
    {G : P × M → ℝ}
    (hG : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ G (V ×ˢ univ))
    {p : P} (hp : p∈V) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun z => G (p,z)) := by
  intro z
  exact (hG.contMDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hp,mem_univ z⟩)).comp z
    (contMDiff_const.prodMk contMDiff_id).contMDiffAt

theorem manifoldFamily_scalar_chart_smooth {V : Set P} (hV : IsOpen V)
    {G : P × M → ℝ}
    (hG : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ G (V ×ˢ univ))
    (c : M) : ContDiffOn ℝ ∞
      (fun q : P × E => G (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2))
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
  intro q hq
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hq.2)
  have hfst : ContMDiffAt 𝓘(ℝ,P × E) 𝓘(ℝ,P) ∞ (Prod.fst : P × E → P) q :=
    contDiff_fst.contMDiff.contMDiffAt
  have hsnd : ContMDiffAt 𝓘(ℝ,P × E) 𝓘(ℝ,E) ∞ (Prod.snd : P × E → E) q :=
    contDiff_snd.contMDiff.contMDiffAt
  have hinc := hfst.prodMk (hi.comp q hsnd)
  have hh := (hG.contMDiffAt ((hV.prod isOpen_univ).mem_nhds
    (show (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2)∈V ×ˢ univ from ⟨hq.1,mem_univ _⟩))).comp q hinc
  exact hh.contDiffAt.contDiffWithinAt

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem joint_scalar_fderiv_slice {F : P × E → ℝ} {q : P × E}
    (hF : DifferentiableAt ℝ F q) :
    fderiv ℝ (fun y => F (q.1,y)) q.2=
      (fderiv ℝ F q).comp ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)) := by
  have hi : HasFDerivAt (fun y : E => (q.1,y))
      ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)) q.2 :=
    (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
  exact (hF.hasFDerivAt.comp q.2 hi).fderiv

theorem manifoldFamilyScalarDifferential_smooth {V : Set P} (hV : IsOpen V)
    {G : P × M → ℝ}
    (hG : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ G (V ×ˢ univ))
    (c : M) : ContDiffOn ℝ ∞
      (fun q : P × E => chartOneForm
        (manifoldScalarDifferential (E := E) (fun z => G (q.1,z))) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
  let F : P × E → ℝ := fun q => G (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2)
  have hF : ContDiffOn ℝ ∞ F (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
    manifoldFamily_scalar_chart_smooth hV hG c
  intro q hq
  have hn := (hV.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hq
  have hdf : ContDiffAt ℝ ∞ (fun z => fderiv ℝ F z) q :=
    (hF.contDiffAt hn).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := hdf.clm_comp
    (contDiffAt_const (c := ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E))))
  apply (hd.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with z hz
  rw [manifoldScalarDifferential_chart (manifoldFamily_scalar_fiber_smooth hV hG hz.1) hz.2]
  exact joint_scalar_fderiv_slice ((hF.contDiffAt
    ((hV.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hz)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))




omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem normalizedManifoldPrimitive_chart
    (Γ : P → ManifoldOneForm E M) (β : ManifoldOneForm E M)
    (a : P → ℝ) (G : P × M → ℝ) (p : P) (c : M) (y : E) :
    chartOneForm (normalizedManifoldPrimitive Γ β a G p) c y=
      chartOneForm (Γ p) c y-a p • chartOneForm β c y-
        chartOneForm (manifoldScalarDifferential (fun z => G (p,z))) c y := by
  simp only [normalizedManifoldPrimitive,chartOneForm_sub,chartOneForm_smul]

theorem normalizedManifoldPrimitive_smooth {V : Set P} (hV : IsOpen V)
    {Γ : P → ManifoldOneForm E M} {β : ManifoldOneForm E M} {a : P → ℝ}
    {G : P × M → ℝ}
    (hΓ : ∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ q.1) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target)
    (ha : ContDiffOn ℝ ∞ a V)
    (hG : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ G (V ×ˢ univ))
    (c : M) : ContDiffOn ℝ ∞
      (fun q : P × E => chartOneForm (normalizedManifoldPrimitive Γ β a G q.1) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
  have hma : ContDiffOn ℝ ∞ (fun q : P × E => a q.1)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
    ha.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)
  have hmb : ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm β c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
    (hβ c).comp contDiff_snd.contDiffOn (fun _ hx => hx.2)
  exact (((hΓ c).sub (hma.smul hmb)).sub
    (manifoldFamilyScalarDifferential_smooth hV hG c)).congr
      (fun q _ => normalizedManifoldPrimitive_chart Γ β a G q.1 c q.2)

variable [FiniteDimensional ℝ E] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_normalized_manifold_primitive {V : Set P} {K A : Set M}
    (hV : IsOpen V) (hK : IsCompact K) (hA : IsOpen A) (hKA : K ⊆ A)
    {Γ N : P → ManifoldOneForm E M} {β : ManifoldOneForm E M}
    {a : P → ℝ} {F : P × M → ℝ}
    (hΓ : ∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ q.1) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target)
    (hβclosed : ∀ x,manifoldExteriorOneForm β x=0)
    (hβcompact : HasCompactSupport β) (ha : ContDiffOn ℝ ∞ a V)
    (hF : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ A))
    (hFd : ∀ p ∈ V,∀ x ∈ A,
      manifoldScalarDifferential (E := E) (fun y => F (p,y)) x=
        Γ p x-N p x-a p • β x) :
    ∃ (Γ₁ : P → ManifoldOneForm E M) (L : Set M), IsCompact L ∧ L ⊆ A ∧
      (∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ₁ q.1) c q.2)
        (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) ∧
      (∀ p,support (Γ₁ p-Γ p) ⊆ tsupport β ∪ L) ∧
      (∀ p,HasCompactSupport (Γ₁ p-Γ p)) ∧
      (∀ p ∈ V,∀ x,manifoldExteriorOneForm (Γ₁ p) x=manifoldExteriorOneForm (Γ p) x) ∧
      (∀ p ∈ V,∀ x ∈ K,Γ₁ p x=N p x) := by
  obtain ⟨G,L,hLc,hLA,hG,_,_,hGs,_,hGd⟩ :=
    exists_joint_global_local_potential hV hK hA hKA hF
  let Γ₁ := normalizedManifoldPrimitive Γ β a G
  have hs : ∀ p,support (Γ₁ p-Γ p) ⊆ tsupport β ∪ L := by
    intro p x hx
    by_contra hout
    have hβz : β x=0 := notMem_support.mp (fun hv => hout (Or.inl (subset_closure hv)))
    have hdz : manifoldScalarDifferential (E := E) (fun y => G (p,y)) x=0 :=
      notMem_support.mp (fun hv => hout (Or.inr (hGs p hv)))
    apply hx
    apply ContinuousLinearMap.ext
    intro v
    change Γ p x v-a p*β x v-manifoldScalarDifferential (E := E) (fun y => G (p,y)) x v-
      Γ p x v=0
    rw [hβz,hdz]
    simp
  refine ⟨Γ₁,L,hLc,hLA,normalizedManifoldPrimitive_smooth hV hΓ hβ ha hG,hs,
    (fun p => HasCompactSupport.of_support_subset_isCompact (hβcompact.union hLc) (hs p)),?_,?_⟩
  · intro p hp x
    have hΓp : ∀ c,ContDiffOn ℝ ∞ (chartOneForm (Γ p) c)
        (extChartAt 𝓘(ℝ,E) c).target := by
      intro c
      exact (hΓ c).comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
        (fun y hy => ⟨hp,hy⟩)
    exact manifold_closed_exact_normalization hΓp hβ hβclosed
      (manifoldFamily_scalar_fiber_smooth hV hG hp) (a p) x
  · intro p hp x hx
    apply ContinuousLinearMap.ext
    intro v
    change Γ p x v-a p*β x v-manifoldScalarDifferential (E := E) (fun y => G (p,y)) x v=N p x v
    rw [hGd p x hx,hFd p hp x (hKA hx)]
    simp only [sub_apply,smul_apply,smul_eq_mul]
    ring

theorem exists_normalized_manifold_primitive_neighborhood {V : Set P} {K A : Set M}
    (hV : IsOpen V) (hK : IsCompact K) (hA : IsOpen A) (hKA : K ⊆ A)
    {Γ N : P → ManifoldOneForm E M} {β : ManifoldOneForm E M}
    {a : P → ℝ} {F : P × M → ℝ}
    (hΓ : ∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ q.1) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target)
    (hβclosed : ∀ x,manifoldExteriorOneForm β x=0)
    (hβcompact : HasCompactSupport β) (ha : ContDiffOn ℝ ∞ a V)
    (hF : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ A))
    (hFd : ∀ p ∈ V,∀ x ∈ A,
      manifoldScalarDifferential (E := E) (fun y => F (p,y)) x=
        Γ p x-N p x-a p • β x) :
    ∃ (Γ₁ : P → ManifoldOneForm E M) (L W : Set M),
      IsCompact L ∧ L ⊆ A ∧ IsOpen W ∧ K ⊆ W ∧ W ⊆ A ∧
      (∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ₁ q.1) c q.2)
        (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) ∧
      (∀ p,support (Γ₁ p-Γ p) ⊆ tsupport β ∪ L) ∧
      (∀ p,HasCompactSupport (Γ₁ p-Γ p)) ∧
      (∀ p ∈ V,∀ x,manifoldExteriorOneForm (Γ₁ p) x=manifoldExteriorOneForm (Γ p) x) ∧
      (∀ p ∈ V,∀ x ∈ W,Γ₁ p x=N p x) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  obtain ⟨D,hD,hKD,hDA⟩ := exists_compact_between hK hA hKA
  obtain ⟨Γ₁,L,hL,hLA,hs,hsp,hcp,hd,he⟩ :=
    exists_normalized_manifold_primitive hV hD hA hDA hΓ hβ hβclosed hβcompact ha hF hFd
  exact ⟨Γ₁,L,interior D,hL,hLA,isOpen_interior,hKD,interior_subset.trans hDA,
    hs,hsp,hcp,hd,fun p hp x hx => he p hp x (interior_subset hx)⟩


end


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
theorem handlePushforwardOneForm_compact [T2Space N]
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {α : ManifoldOneForm E M} {K : Set M} (hK : IsCompact K) (hKs : K⊆e.source)
    (hz : ∀ x, x∉K → α x=0) : HasCompactSupport (handlePushforwardOneForm e α) := by
  apply HasCompactSupport.intro (hK.image_of_continuousOn
    (e.contMDiffOn.continuousOn.mono hKs))
  exact fun _ hy => handlePushforwardOneForm_zero e hz hy

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

theorem handlePushforwardOneForm_closed [T2Space N]
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {α : ManifoldOneForm E M} {K : Set M} (hK : IsCompact K) (hKs : K⊆e.source)
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (hz : ∀ x, x∉K → α x=0) (hd : ∀ x, manifoldExteriorOneForm α x=0) (y : N) :
    manifoldExteriorOneForm (handlePushforwardOneForm e α) y=0 := by
  by_cases hy : y∈e.target
  · rw [handlePushforwardOneForm,extendManifoldOneForm_exterior_inside e.open_target _ hy,
      manifold_pullback_exterior_on hα e.open_target e.symm.contMDiffOn hy]
    simp only [manifoldPullbackTwoForm,hd]
    rfl
  · have hn : y∉e '' K := by
      rintro ⟨x,hx,rfl⟩
      exact hy (e.map_source (hKs hx))
    have hKi := hK.image_of_continuousOn (e.contMDiffOn.continuousOn.mono hKs)
    have he : handlePushforwardOneForm e α =ᶠ[𝓝 y] 0 := by
      filter_upwards [hKi.isClosed.isOpen_compl.mem_nhds hn] with z hzK
      exact handlePushforwardOneForm_zero e hz hzK
    rw [manifoldExteriorOneForm_congr_of_eventuallyEq he,manifoldExteriorOneForm_zero]



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_AnnularChartHelpers
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

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [NormedAddCommGroup P] [NormedSpace ℝ P]
  [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem parameterManifoldPullbackOneForm_inverse_apply
    (e : PartialDiffeomorph 𝓘(ℝ,F) 𝓘(ℝ,E) N M ∞)
    (α : P → ManifoldOneForm E M) (p : P) {x : M} (hx : x∈e.target) (v : E) :
    parameterManifoldPullbackOneForm (E := E) (F := F) α e p (e.symm x)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e.symm x v)=α p x v := by
  have hd := handle_mfderiv_symm_comp e.symm hx
  change α p (e (e.symm x))
    ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e (e.symm x))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e.symm x v))=α p x v
  have he : α p (e (e.symm x))=α p x := congrArg (α p) (e.right_inv hx)
  rw [he]
  exact congrArg (α p x) (congrArg (fun D : E →L[ℝ] E => D v) hd)

end

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
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem annularPrimitive_smooth {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a ∈ I)
    {A B : P × Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (I ×ˢ univ)))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ))) :
    ContDiffOn ℝ ∞ (annularPrimitive a A B) (V ×ˢ (I ×ˢ univ)) := by
  have hAf : ContDiffOn ℝ ∞ (fun q : P × ℝ => A (q.1,(q.2,0))) (V ×ˢ I) :=
    hA.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)).contDiffOn
      (fun _ hq => ⟨hq.1,hq.2,mem_univ _⟩)
  have hAi := contDiffOn_parameter_segment_integral hV hI hc a ha hAf
  have hAs : ContDiffOn ℝ ∞ (fun q : P × Plane => ∫ s in a..q.2.1, A (q.1,(s,0)))
      (V ×ˢ (I ×ˢ univ)) :=
    hAi.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).contDiffOn
      (fun _ hq => ⟨hq.1,hq.2.1⟩)
  have hBf : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℝ => B (q.1.1,(q.1.2,q.2)))
      ((V ×ˢ I) ×ˢ univ) :=
    hB.comp ((contDiff_fst.comp contDiff_fst).prodMk
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn
      (fun _ hq => ⟨hq.1.1,hq.1.2,hq.2⟩)
  have hBi := contDiffOn_parameter_segment_integral (hV.prod hI) isOpen_univ convex_univ
    (0:ℝ) (mem_univ _) hBf
  have hBs : ContDiffOn ℝ ∞ (fun q : P × Plane => ∫ t in (0:ℝ)..q.2.2, B (q.1,(q.2.1,t)))
      (V ×ˢ (I ×ˢ univ)) :=
    hBi.comp ((contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).prodMk
      (contDiff_snd.comp contDiff_snd)).contDiffOn
      (fun _ hq => ⟨⟨hq.1,hq.2.1⟩,hq.2.2⟩)
  exact hAs.add hBs

theorem stripPrimitive_smooth {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ)) :
    ContDiffOn ℝ ∞ (stripPrimitive a A B) (I ×ˢ univ) := by
  have hA' : ContDiffOn ℝ ∞ (fun q : ℝ × Plane => A q.2) (univ ×ˢ (I ×ˢ univ)) :=
    hA.comp contDiff_snd.contDiffOn (fun _ hq => hq.2)
  have hB' : ContDiffOn ℝ ∞ (fun q : ℝ × Plane => B q.2) (univ ×ˢ (I ×ˢ univ)) :=
    hB.comp contDiff_snd.contDiffOn (fun _ hq => hq.2)
  exact (annularPrimitive_smooth isOpen_univ hI hc ha hA' hB').comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hq => ⟨mem_univ (0:ℝ),hq⟩)



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularMean
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
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

theorem annularMean_smooth {V : Set P} {I : Set ℝ} (hV : IsOpen V)
    {a : ℝ} (ha : a ∈ I) {B : P × Plane → ℝ}
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ))) :
    ContDiffOn ℝ ∞ (annularMean a B) V := by
  have hf : ContDiffOn ℝ ∞ (fun q : P × ℝ => B (q.1,(a,q.2))) (V ×ˢ univ) :=
    hB.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)).contDiffOn
      (fun _ hq => ⟨hq.1,ha,hq.2⟩)
  exact (contDiffOn_parameter_segment_integral hV isOpen_univ convex_univ
    (0:ℝ) (mem_univ _) hf).comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun _ hp => ⟨hp,mem_univ (1:ℝ)⟩)

theorem annularNormalized_smooth {V : Set P} {I : Set ℝ} (hV : IsOpen V)
    {a : ℝ} (ha : a ∈ I) {B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ))) (hβ : ContDiff ℝ ∞ β) :
    ContDiffOn ℝ ∞ (annularNormalized a B β) (V ×ˢ (I ×ˢ univ)) :=
  hB.sub (((annularMean_smooth hV ha hB).comp contDiff_fst.contDiffOn
    (fun _ hq => hq.1)).mul (hβ.comp (contDiff_snd.comp contDiff_snd)).contDiffOn)

omit [FiniteDimensional ℝ P] in

theorem annularNormalized_fderiv_radial {V : Set P} {I : Set ℝ}
    (hI : IsOpen I) {a : ℝ} {B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ))) (hβ : ContDiff ℝ ∞ β)
    {p : P} (hp : p ∈ V) {q : Plane} (hq : q.1 ∈ I) :
    fderiv ℝ (fun z => annularNormalized a B β (p,z)) q (1,0) =
      fderiv ℝ (fun z => B (p,z)) q (1,0) := by
  have hB' : ContDiffOn ℝ ∞ (fun z => B (p,z)) (I ×ˢ univ) :=
    hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩)
  have hdB := ((hB'.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨hq,mem_univ _⟩)).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hdβ := ((hβ.comp contDiff_snd).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) q).hasFDerivAt
  have hβ0 : fderiv ℝ (β ∘ (Prod.snd : Plane → ℝ)) q (1,0) = 0 := by
    rw [fderiv_comp q (hβ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) q.2) differentiableAt_snd]
    rw [(hasFDerivAt_snd (𝕜 := ℝ) (p := q)).fderiv]
    simp
  have hd := hdB.sub (hdβ.const_mul (annularMean a B p))
  change fderiv ℝ ((fun z => B (p,z)) - fun z => annularMean a B p * (β ∘ Prod.snd) z) q (1,0) = _
  rw [hd.fderiv]
  simp only [sub_apply,smul_apply,hβ0,smul_zero,sub_zero]

omit [FiniteDimensional ℝ P] in

theorem annularNormalized_zero_period {V : Set P} {I : Set ℝ}
    {a : ℝ} (ha : a ∈ I) {B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ))) (hβ : ContDiff ℝ ∞ β)
    (hβint : (∫ t in (0:ℝ)..1, β t) = 1) {p : P} (hp : p ∈ V) :
    (∫ t in (0:ℝ)..1, annularNormalized a B β (p,(a,t))) = 0 := by
  have hBt : Continuous (fun t : ℝ => B (p,(a,t))) := by
    apply continuousOn_univ.mp
    exact hB.continuousOn.comp (continuous_const.prodMk
      (continuous_const.prodMk continuous_id)).continuousOn
        (fun _ ht => ⟨hp,ha,ht⟩)
  simp only [annularNormalized]
  rw [intervalIntegral.integral_sub (hBt.intervalIntegrable 0 1)
    ((hβ.continuous.const_mul _).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul,hβint,mul_one]
  exact sub_self _

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem annularNormalized_periodic {V : Set P} {I : Set ℝ}
    {a : ℝ} {B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hpB : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => B (p,(s,t))) 1)
    (hpβ : Periodic β 1) {p : P} (hp : p ∈ V) {s : ℝ} (hs : s ∈ I) :
    Periodic (fun t => annularNormalized a B β (p,(s,t))) 1 := by
  intro t
  dsimp only [annularNormalized]
  have h := hpB p hp s hs t
  dsimp only at h
  rw [h,hpβ t]


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_interval_integral {f : ℝ × P → F} (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (x : P) : HasFDerivAt (fun p => ∫ s in a..b, f (s,p))
      (∫ s in a..b, fderiv ℝ (fun p => f (s,p)) x) x := by
  let D : ℝ × P → P →L[ℝ] F := fun q => (fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ ℝ P)
  have hD : Continuous D := (hf.fderiv_right (m := ∞) (by simp)).continuous.clm_comp continuous_const
  have hd (s : ℝ) (p : P) : HasFDerivAt (fun q => f (s,q)) (D (s,p)) p := by
    convert! ((hf.differentiable (by simp) (s,p)).hasFDerivAt.comp p
      ((hasFDerivAt_const s p).prodMk (hasFDerivAt_id p))) using 1
    all_goals try with_reducible_and_instances rfl
  obtain ⟨C,hC⟩ := (isCompact_uIcc.prod (isCompact_closedBall x (1:ℝ))).exists_bound_of_continuousOn hD.continuousOn
  have hi : HasFDerivAt (fun p => ∫ s in a..b, f (s,p)) (∫ s in a..b, D (s,x)) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (s := Metric.closedBall x 1) (bound := fun _ => C) (Metric.closedBall_mem_nhds x zero_lt_one)
    · exact Filter.Eventually.of_forall fun p =>
        (hf.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact (hf.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
    · exact (hD.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      intro p hp
      exact hC (s,p) ⟨uIoc_subset_uIcc hs,hp⟩
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun s p _ => hd s p
  convert! hi using 1
  all_goals try with_reducible_and_instances rfl
  apply intervalIntegral.integral_congr
  intro s _
  exact (hd s x).fderiv

theorem hasFDerivAt_interval_integral_local {f : ℝ × P → F} {U : Set (ℝ × P)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a b : ℝ) (x : P)
    (hseg : ∀ s ∈ uIcc a b, (s,x) ∈ U) :
    HasFDerivAt (fun p => ∫ s in a..b, f (s,p))
      (∫ s in a..b, fderiv ℝ (fun p => f (s,p)) x) x := by
  let K : Set (ℝ × P) := (fun s : ℝ => (s,x)) '' uIcc a b
  have hK : IsCompact K := isCompact_uIcc.image (continuous_id.prodMk continuous_const)
  obtain ⟨χ,_,_,_,_,_,hg,_,he⟩ := exists_smooth_compact_extension hK hU
    (by rintro _ ⟨s,hs,rfl⟩; exact hseg s hs) hf
  let g : ℝ × P → F := fun q => χ q • f q
  have hnear : ∀ᶠ p in 𝓝 x, ∀ s ∈ uIcc a b, g (s,p) = f (s,p) := by
    apply isCompact_uIcc.eventually_forall_of_forall_eventually
    intro s hs
    have hk : (s,x) ∈ K := ⟨s,hs,rfl⟩
    exact ((continuous_swap : Continuous (Prod.swap : P × ℝ → ℝ × P)).continuousAt (x := (x,s))).eventually
      (he.filter_mono (nhds_le_nhdsSet hk))
  have hD (s : ℝ) (hs : s ∈ uIcc a b) :
      fderiv ℝ (fun p => g (s,p)) x = fderiv ℝ (fun p => f (s,p)) x := by
    exact Filter.EventuallyEq.fderiv_eq (hnear.mono fun _ hp => hp s hs)
  have hi := hasFDerivAt_interval_integral hg a b x
  apply hi.congr_of_eventuallyEq ?_ |>.congr_fderiv ?_
  · filter_upwards [hnear] with p hp
    apply intervalIntegral.integral_congr
    intro s hs
    exact (hp s hs).symm
  · apply intervalIntegral.integral_congr
    exact hD

theorem hasDerivAt_interval_integral_local {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a b x : ℝ)
    (hseg : ∀ s ∈ uIcc a b, (s,x) ∈ U) :
    HasDerivAt (fun p => ∫ s in a..b, f (s,p))
      (∫ s in a..b, deriv (fun p => f (s,p)) x) x := by
  have hd := (hasFDerivAt_interval_integral_local hU hf a b x hseg).hasDerivAt
  have he (s : ℝ) : fderiv ℝ (fun p => f (s,p)) x =
      deriv (fun p => f (s,p)) x • (ContinuousLinearMap.id ℝ ℝ) := by
    ext
    simp only [← toSpanSingleton_deriv,ContinuousLinearMap.toSpanSingleton_apply,
      smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    ring
  simpa only [he,intervalIntegral.integral_smul_const,smul_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul,mul_one] using hd

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

section
open scoped ContDiff Topology
open Set Function MeasureTheory

theorem stripPrimitive_hasDerivAt_second {I : Set ℝ} {a : ℝ} {A B : Plane → ℝ}
    (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ)) {s : ℝ} (hs : s ∈ I) (t : ℝ) :
    HasDerivAt (fun u => stripPrimitive a A B (s,u)) (B (s,t)) t := by
  have hBt : ContDiff ℝ ∞ (fun u : ℝ => B (s,u)) := by
    apply contDiffOn_univ.mp
    exact hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => ⟨hs,mem_univ _⟩)
  have hd := intervalIntegral.integral_hasDerivAt_right (hBt.continuous.intervalIntegrable 0 t)
    hBt.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hBt.continuous.continuousAt
  exact hd.const_add (∫ x in a..s, A (x,0))

theorem stripPrimitive_hasDerivAt_first {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ))
    (hclosed : ∀ s ∈ I, ∀ t, fderiv ℝ A (s,t) (0,1) = fderiv ℝ B (s,t) (1,0))
    {s : ℝ} (hs : s ∈ I) (t : ℝ) :
    HasDerivAt (fun u => stripPrimitive a A B (u,t)) (A (s,t)) s := by
  have hA0 : ContinuousOn (fun u : ℝ => A (u,0)) I :=
    hA.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hu => ⟨hu,mem_univ _⟩)
  have hd₀ := hasDerivAt_primitive_on hI hc hA0 ha hs
  have hBf : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => B (q.2,q.1)) (univ ×ˢ I) :=
    hB.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hq => ⟨hq.2,hq.1⟩)
  have hd₁ := hasDerivAt_interval_integral_local (isOpen_univ.prod hI) hBf 0 t s
    (fun _ _ => ⟨mem_univ _,hs⟩)
  have hAt : ContDiff ℝ ∞ (fun u : ℝ => A (s,u)) := by
    apply contDiffOn_univ.mp
    exact hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => ⟨hs,mem_univ _⟩)
  have he (u : ℝ) : deriv (fun x => B (x,u)) s = deriv (fun x => A (s,x)) u := by
    have hdB := ((hB.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨hs,mem_univ u⟩)).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s u))
    have hdA := ((hA.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨hs,mem_univ u⟩)).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp_hasDerivAt u
        ((hasDerivAt_const u s).prodMk (hasDerivAt_id u))
    dsimp only [Function.comp_def,id_eq] at hdB hdA
    rw [hdB.deriv,hdA.deriv,hclosed s hs u]
  have hi : (∫ u in (0:ℝ)..t, deriv (fun x => B (x,u)) s) = A (s,t)-A (s,0) := by
    simp only [he]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun u _ => hAt.differentiable (by simp) u)
      ((hAt.continuous_deriv (by simp)).intervalIntegrable 0 t)
  have hd := hd₀.add hd₁
  rw [hi] at hd
  exact hd.congr_deriv (by ring)

theorem stripPrimitive_fderiv {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ))
    (hclosed : ∀ s ∈ I, ∀ t, fderiv ℝ A (s,t) (0,1) = fderiv ℝ B (s,t) (1,0))
    {q : Plane} (hq : q.1 ∈ I) (v : Plane) :
    fderiv ℝ (stripPrimitive a A B) q v = A q*v.1+B q*v.2 := by
  have hd : DifferentiableAt ℝ (stripPrimitive a A B) q :=
    ((stripPrimitive_smooth hI hc ha hA hB).contDiffAt
    ((hI.prod isOpen_univ).mem_nhds ⟨hq,mem_univ q.2⟩)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h₁ : fderiv ℝ (stripPrimitive a A B) q (1,0) = A q := by
    have hd' := hd.hasFDerivAt.comp_hasDerivAt q.1
        ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
    dsimp only [Function.comp_def,id_eq] at hd'
    exact hd'.unique (stripPrimitive_hasDerivAt_first hI hc ha hA hB hclosed hq q.2)
  have h₂ : fderiv ℝ (stripPrimitive a A B) q (0,1) = B q := by
    have hd' := hd.hasFDerivAt.comp_hasDerivAt q.2
        ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
    dsimp only [Function.comp_def,id_eq] at hd'
    exact hd'.unique (stripPrimitive_hasDerivAt_second (a := a) (A := A) hB hq q.2)
  have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  conv_lhs => rw [hv]
  simp only [map_add,map_smul,h₁,h₂,smul_eq_mul]
  ring




theorem strip_period_eq {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ))
    (hclosed : ∀ s ∈ I, ∀ t, fderiv ℝ A (s,t) (0,1) = fderiv ℝ B (s,t) (1,0))
    (hpA : ∀ s ∈ I, Periodic (fun t => A (s,t)) 1) {s : ℝ} (hs : s ∈ I) :
    (∫ t in (0:ℝ)..1, B (s,t)) = ∫ t in (0:ℝ)..1, B (a,t) := by
  let c : ℝ → ℝ := fun s => ∫ t in (0:ℝ)..1, B (s,t)
  have he : (fun s => stripPrimitive a A B (s,1)-stripPrimitive a A B (s,0)) = c := by
    funext s
    simp only [stripPrimitive,intervalIntegral.integral_same,add_zero,c,add_sub_cancel_left]
  have hd (s : ℝ) (hs : s ∈ I) : HasDerivAt c 0 s := by
    have h := (stripPrimitive_hasDerivAt_first hI hc ha hA hB hclosed hs 1).sub
      (stripPrimitive_hasDerivAt_first hI hc ha hA hB hclosed hs 0)
    change HasDerivAt (fun u => stripPrimitive a A B (u,1)-stripPrimitive a A B (u,0)) _ s at h
    rw [he] at h
    have hp := hpA s hs 0
    simp only [zero_add] at hp
    simpa only [hp,sub_self] using h
  exact hI.is_const_of_deriv_eq_zero hc.isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) hs ha

theorem stripPrimitive_periodic {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ))
    (hclosed : ∀ s ∈ I, ∀ t, fderiv ℝ A (s,t) (0,1) = fderiv ℝ B (s,t) (1,0))
    (hpA : ∀ s ∈ I, Periodic (fun t => A (s,t)) 1)
    (hpB : ∀ s ∈ I, Periodic (fun t => B (s,t)) 1)
    (hz : (∫ t in (0:ℝ)..1, B (a,t)) = 0) {s : ℝ} (hs : s ∈ I) :
    Periodic (fun t => stripPrimitive a A B (s,t)) 1 := by
  have hc0 := (strip_period_eq hI hc ha hA hB hclosed hpA hs).trans hz
  have hBt : Continuous (fun t : ℝ => B (s,t)) := by
    apply continuousOn_univ.mp
    exact hB.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => ⟨hs,mem_univ _⟩)
  intro t
  dsimp only [stripPrimitive]
  rw [(hpB s hs).intervalIntegral_add_eq_add 0 t (fun a b => hBt.intervalIntegrable a b)]
  simp only [zero_add,hc0,add_zero]


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem annular_normalization {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (I ×ˢ univ)))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ)))
    (hβ : ContDiff ℝ ∞ β) (hpβ : Periodic β 1)
    (hβint : (∫ t in (0:ℝ)..1, β t) = 1)
    (hpA : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => A (p,(s,t))) 1)
    (hpB : ∀ p ∈ V, ∀ s ∈ I, Periodic (fun t => B (p,(s,t))) 1)
    (hclosed : ∀ p ∈ V, ∀ s ∈ I, ∀ t,
      fderiv ℝ (fun z => A (p,z)) (s,t) (0,1) =
      fderiv ℝ (fun z => B (p,z)) (s,t) (1,0)) :
    ContDiffOn ℝ ∞ (normalizedAnnularPrimitive a A B β) (V ×ˢ (I ×ˢ univ)) ∧
      (∀ p ∈ V, ∀ s ∈ I,
        Periodic (fun t => normalizedAnnularPrimitive a A B β (p,(s,t))) 1) ∧
      (∀ p ∈ V, ∀ q : Plane, q.1 ∈ I → ∀ v : Plane,
        fderiv ℝ (fun z => normalizedAnnularPrimitive a A B β (p,z)) q v =
          A (p,q)*v.1+(B (p,q)-annularMean a B p*β q.2)*v.2) := by
  have hBn := annularNormalized_smooth hV ha hB hβ
  refine ⟨annularPrimitive_smooth hV hI hc ha hA hBn,?_,?_⟩
  · intro p hp s hs
    have hAp : ContDiffOn ℝ ∞ (fun z => A (p,z)) (I ×ˢ univ) :=
      hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩)
    have hBp : ContDiffOn ℝ ∞ (fun z => annularNormalized a B β (p,z)) (I ×ˢ univ) :=
      hBn.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩)
    apply stripPrimitive_periodic hI hc ha hAp hBp ?_ (hpA p hp) ?_ ?_ hs
    · intro u hu t
      rw [annularNormalized_fderiv_radial hI hB hβ hp hu]
      exact hclosed p hp u hu t
    · intro u hu
      exact annularNormalized_periodic hpB hpβ hp hu
    · exact annularNormalized_zero_period ha hB hβ hβint hp
  · intro p hp q hq v
    have hAp : ContDiffOn ℝ ∞ (fun z => A (p,z)) (I ×ˢ univ) :=
      hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩)
    have hBp : ContDiffOn ℝ ∞ (fun z => annularNormalized a B β (p,z)) (I ×ˢ univ) :=
      hBn.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩)
    exact stripPrimitive_fderiv hI hc ha hAp hBp
      (fun u hu t => by
        rw [annularNormalized_fderiv_radial hI hB hβ hp hu]
        exact hclosed p hp u hu t) hq v


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
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
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


end


open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_CylinderAnnularNormalization
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderComplexMap_norm _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
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
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem annularCylinderScalar_differential_cover {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) {F : P × Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => F (p,(s,t))) 1)
    {p : P} (hp : p∈V) {q : Plane} (hq : q.1∈I) (v : Plane) :
    manifoldScalarDifferential (E := CylinderModel) (annularCylinderScalar F p) (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v)=
      fderiv ℝ (fun z => F (p,z)) q v := by
  have hs := annularCylinderScalar_smoothAt hV hI hF hper hp (z := cylinderCover q) hq
  have hd := mfderiv_comp q (hs.mdifferentiableAt (by simp))
    (cylinderCover_smooth.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  have he : (annularCylinderScalar F p ∘ cylinderCover) =ᶠ[𝓝 q] (fun z => F (p,z)) := by
    filter_upwards [(hI.prod isOpen_univ).mem_nhds (show q∈I ×ˢ univ from ⟨hq,mem_univ _⟩)] with z hz
    exact annularScalarDescent_turn (hper p hp z.1 hz.1) z.2
  rw [he.fderiv_eq] at hd
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L v) hd.symm

variable [FiniteDimensional ℝ P]

theorem normalized_annular_scalar_intrinsic {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I) {A B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (I ×ˢ univ)))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ)))
    (hβ : ContDiff ℝ ∞ β) (hpβ : Periodic β 1)
    (hβint : (∫ t in (0:ℝ)..1,β t)=1)
    (hpA : ∀ p∈V,∀ s∈I,Periodic (fun t => A (p,(s,t))) 1)
    (hpB : ∀ p∈V,∀ s∈I,Periodic (fun t => B (p,(s,t))) 1)
    (hclosed : ∀ p∈V,∀ s∈I,∀ t,
      fderiv ℝ (fun z => A (p,z)) (s,t) (0,1)=
      fderiv ℝ (fun z => B (p,z)) (s,t) (1,0)) :
    ContMDiffOn ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
      (annularScalarDescent (normalizedAnnularPrimitive a A B β)) ((V ×ˢ I) ×ˢ univ) ∧
    (∀ p∈V,∀ z : HandleCylinder,z.1∈I → ∀ v : CylinderModel,
      manifoldScalarDifferential (E := CylinderModel) (annularCylinderScalar (normalizedAnnularPrimitive a A B β) p) z v=
        annularCylinderScalar A p z*v.1+
          (annularCylinderScalar B p z-annularMean a B p*circlePeriodicDescent β z.2)*
            circleAngular z.2 v.2) := by
  obtain ⟨hF,hFp,hFd⟩ := annular_normalization hV hI hc ha hA hB hβ hpβ hβint hpA hpB hclosed
  refine ⟨annularScalarDescent_smoothOn hV hI hF hFp,?_⟩
  intro p hp z hz v
  let q : Plane := (z.1,shortCircleArgument z.2)
  have hq : cylinderCover q=z := by
    apply Prod.ext
    · rfl
    · exact circleTurn_shortCircleArgument z.2
  let u : Plane := (v.1,circleAngular (circleTurn q.2) v.2)
  have hd := annularCylinderScalar_differential_cover hV hI hF hFp hp (q := q) hz u
  have hL : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q u=v :=
    cylinderCover_derivative_right_inverse q v
  have hval : manifoldScalarDifferential (E := CylinderModel)
      (annularCylinderScalar (normalizedAnnularPrimitive a A B β) p) (cylinderCover q) v=
      A (p,q)*u.1+(B (p,q)-annularMean a B p*β q.2)*u.2 := by
    calc
      _ = manifoldScalarDifferential (E := CylinderModel)
          (annularCylinderScalar (normalizedAnnularPrimitive a A B β) p) (cylinderCover q)
          (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q u) := congrArg _ hL.symm
      _ = _ := hd.trans (hFd p hp q hz u)
  have hAv : annularCylinderScalar A p (cylinderCover q)=A (p,q) :=
    annularScalarDescent_turn (hpA p hp q.1 hz) q.2
  have hBv : annularCylinderScalar B p (cylinderCover q)=B (p,q) :=
    annularScalarDescent_turn (hpB p hp q.1 hz) q.2
  have hβv := circlePeriodicDescent_turn hpβ q.2
  rw [← hq,hAv,hBv]
  change _=A (p,q)*v.1+(B (p,q)-annularMean a B p*circlePeriodicDescent β (circleTurn q.2))*
    circleAngular (circleTurn q.2) v.2
  rw [hβv]
  exact hval


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem closed_cylinder_cover_equation {I : Set ℝ} (hI : IsOpen I)
    {α : ManifoldOneForm CylinderModel HandleCylinder} {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ))
    (hα : ∀ q : Plane,q.1∈I → ContDiffAt ℝ ∞
      (chartOneForm α (cylinderCover q))
      (extChartAt 𝓘(ℝ,CylinderModel) (cylinderCover q) (cylinderCover q)))
    (hclosed : ∀ z : HandleCylinder,z.1∈I → manifoldExteriorOneForm α z=0)
    (hrep : ∀ q : Plane,q.1∈I →
      euclideanPullbackOneForm (fun _ => α) cylinderCover (0,q)=planarCovector (A q) (B q))
    {q : Plane} (hq : q.1∈I) :
    fderiv ℝ A q (0,1)=fderiv ℝ B q (1,0) := by
  have hn := (hI.prod isOpen_univ).mem_nhds (show q∈I ×ˢ univ from ⟨hq,mem_univ _⟩)
  have he : (fun y => euclideanPullbackOneForm (fun _ => α) cylinderCover (0,y))
      =ᶠ[𝓝 q] (fun y => planarCovector (A y) (B y)) := by
    filter_upwards [hn] with y hy
    exact hrep y hy.1
  have hd := euclidean_manifold_pullback_exterior_at
    (g := cylinderCover) cylinderCover_smooth.contMDiffAt (hα q hq)
  rw [hclosed (cylinderCover q) hq] at hd
  have hz : euclideanExteriorOneForm (fun y => planarCovector (A y) (B y)) q=0 := by
    have hder : fderiv ℝ (fun y => euclideanPullbackOneForm (fun _ => α) cylinderCover (0,y)) q=
        fderiv ℝ (fun y => planarCovector (A y) (B y)) q := he.fderiv_eq
    unfold euclideanExteriorOneForm at hd ⊢
    rw [hder] at hd
    exact hd
  rw [planarCovector_exterior_at (hA.contDiffAt hn) (hB.contDiffAt hn)] at hz
  have hv := congrArg (fun Ω : Plane →L[ℝ] Plane →L[ℝ] ℝ => Ω (1,0) (0,1)) hz
  simp only [smul_apply,smul_eq_mul,planarArea_apply,mul_one,mul_zero,
    sub_zero,zero_apply] at hv
  linarith

variable [FiniteDimensional ℝ P]

theorem closed_cylinder_normalized_potential {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {α : P → ManifoldOneForm CylinderModel HandleCylinder}
    {A B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (I ×ˢ univ)))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ)))
    (hβ : ContDiff ℝ ∞ β) (hpβ : Periodic β 1)
    (hβint : (∫ t in (0:ℝ)..1,β t)=1)
    (hpA : ∀ p∈V,∀ s∈I,Periodic (fun t => A (p,(s,t))) 1)
    (hpB : ∀ p∈V,∀ s∈I,Periodic (fun t => B (p,(s,t))) 1)
    (hα : ∀ p∈V,∀ q : Plane,q.1∈I → ContDiffAt ℝ ∞
      (chartOneForm (α p) (cylinderCover q))
      (extChartAt 𝓘(ℝ,CylinderModel) (cylinderCover q) (cylinderCover q)))
    (hclosed : ∀ p∈V,∀ z : HandleCylinder,z.1∈I → manifoldExteriorOneForm (α p) z=0)
    (hrep : ∀ p∈V,∀ q : Plane,q.1∈I →
      euclideanPullbackOneForm (fun _ => α p) cylinderCover (0,q)=
        planarCovector (A (p,q)) (B (p,q))) :
    ContMDiffOn ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
      (annularScalarDescent (normalizedAnnularPrimitive a A B β)) ((V ×ˢ I) ×ˢ univ) ∧
    (∀ p∈V,∀ z : HandleCylinder,z.1∈I → ∀ v : CylinderModel,
      manifoldScalarDifferential (E := CylinderModel)
        (annularCylinderScalar (normalizedAnnularPrimitive a A B β) p) z v=
          α p z v-annularMean a B p*circlePeriodicDescent β z.2*circleAngular z.2 v.2) := by
  have hc' : ∀ p∈V,∀ s∈I,∀ t,
      fderiv ℝ (fun z => A (p,z)) (s,t) (0,1)=
      fderiv ℝ (fun z => B (p,z)) (s,t) (1,0) := by
    intro p hp s hs t
    exact closed_cylinder_cover_equation hI
      (hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩))
      (hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩))
      (hα p hp) (hclosed p hp) (hrep p hp) hs
  obtain ⟨hs,hd⟩ := normalized_annular_scalar_intrinsic hV hI hc ha hA hB
    hβ hpβ hβint hpA hpB hc'
  refine ⟨hs,?_⟩
  intro p hp z hz v
  rw [hd p hp z hz v]
  let q : Plane := (z.1,shortCircleArgument z.2)
  have hq : cylinderCover q=z := by
    apply Prod.ext
    · rfl
    · exact circleTurn_shortCircleArgument z.2
  let u : Plane := (v.1,circleAngular (circleTurn q.2) v.2)
  have hL : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q u=v :=
    cylinderCover_derivative_right_inverse q v
  have hr := congrArg (fun L : Plane →L[ℝ] ℝ => L u) (hrep p hp q hz)
  change α p (cylinderCover q)
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q u)=_
    at hr
  rw [hL] at hr
  have hAv : annularCylinderScalar A p (cylinderCover q)=A (p,q) :=
    annularScalarDescent_turn (hpA p hp q.1 hz) q.2
  have hBv : annularCylinderScalar B p (cylinderCover q)=B (p,q) :=
    annularScalarDescent_turn (hpB p hp q.1 hz) q.2
  rw [← hq,hAv,hBv,hr]
  simp only [planarCovector_apply,u,cylinderCover]
  ring


end

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

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem cylinderForm_rep (α : P → ManifoldOneForm CylinderModel HandleCylinder)
    (p : P) (q : Plane) :
    euclideanPullbackOneForm (fun _ => α p) cylinderCover (0,q)=
      planarCovector (cylinderFormA α (p,q)) (cylinderFormB α (p,q)) := by
  let L := parameterEuclideanPullbackOneForm α cylinderCover (p,q)
  change L=planarCovector (L (1,0)) (L (0,1))
  apply ContinuousLinearMap.ext
  intro v
  have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
  rw [show L v=L (v.1 • (1,0)+v.2 • (0,1)) from congrArg L hv]
  simp only [map_add,map_smul,smul_eq_mul,planarCovector_apply]
  ring

theorem cylinderForm_coefficients_smooth {V : Set P} {I : Set ℝ}
    {α : P → ManifoldOneForm CylinderModel HandleCylinder}
    (hα : ∀ p∈V,∀ z : HandleCylinder,z.1∈I → ContDiffAt ℝ ∞
      (fun q : P × CylinderModel => chartOneForm (α q.1) z q.2)
      (p,extChartAt 𝓘(ℝ,CylinderModel) z z)) :
    ContDiffOn ℝ ∞ (cylinderFormA α) (V ×ˢ (I ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (cylinderFormB α) (V ×ˢ (I ×ˢ univ)) := by
  have hs : ∀ q∈V ×ˢ (I ×ˢ (univ : Set ℝ)),
      ContDiffAt ℝ ∞ (parameterEuclideanPullbackOneForm α cylinderCover) q := by
    intro q hq
    exact parameterEuclideanPullbackOneForm_contDiffAt
      (hα q.1 hq.1 (cylinderCover q.2) hq.2.1) cylinderCover_smooth.contMDiffAt
  exact ⟨fun q hq => ((hs q hq).clm_apply contDiffAt_const).contDiffWithinAt,
    fun q hq => ((hs q hq).clm_apply contDiffAt_const).contDiffWithinAt⟩

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem cylinderForm_coefficients_periodic
    (α : P → ManifoldOneForm CylinderModel HandleCylinder) (p : P) (s : ℝ) :
    Periodic (fun t => cylinderFormA α (p,(s,t))) 1 ∧
      Periodic (fun t => cylinderFormB α (p,(s,t))) 1 := by
  have he (t : ℝ) : parameterEuclideanPullbackOneForm α cylinderCover (p,(s,t+1))=
      parameterEuclideanPullbackOneForm α cylinderCover (p,(s,t)) := by
    have hq : (s,t+1)=(s,t)+(0,1) := by ext <;> simp
    unfold parameterEuclideanPullbackOneForm
    rw [hq,cylinderCover_period_one,cylinderCover_derivative_period_one]
  exact ⟨fun t => congrArg (fun L : Plane →L[ℝ] ℝ => L (1,0)) (he t),
    fun t => congrArg (fun L : Plane →L[ℝ] ℝ => L (0,1)) (he t)⟩


end


open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_QuadricCylinderChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable (m : ℕ)

theorem transverseCylinderWidth_pos : 0<transverseCylinderWidth m :=
  (exists_transverseCylinderWidth m).choose_spec.1

theorem transverseCylinderWidth_subset :
    Icc (-transverseCylinderWidth m) (transverseCylinderWidth m) ×ˢ (univ : Set Circle)⊆
      (transverseCylinder m).source := (exists_transverseCylinderWidth m).choose_spec.2

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport
open scoped Topology
open Set Function

theorem complexClosedAnnulus_isCompact (ε : ℝ) : IsCompact (complexClosedAnnulus ε) := by
  apply (isCompact_closedBall (0:ℂ) (1+ε)).of_isClosed_subset
  · exact isClosed_le continuous_const continuous_norm |>.inter
      (isClosed_le continuous_norm continuous_const)
  · intro z hz
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2

end PackingSufficiencySupport

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem planeRadiusSq_norm (x : RadialPlane) :
    planeRadiusSq x=‖Complex.equivRealProdCLM.symm x‖^2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [planeRadiusSq,Complex.normSq_apply,pow_two]

theorem planeRadialStep_smooth (ε : ℝ) : ContDiff ℝ ∞ (planeRadialStep ε) := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_fst.pow 2).add (contDiff_snd.pow 2)).sub contDiff_const |>.div_const _)

theorem planeClosedAnnulus_compact (ε : ℝ) : IsCompact (planeClosedAnnulus ε) := by
  have he : planeClosedAnnulus ε=Complex.equivRealProdCLM '' complexClosedAnnulus ε := by
    ext x
    constructor
    · intro hx
      exact ⟨Complex.equivRealProdCLM.symm x,hx,Complex.equivRealProdCLM.apply_symm_apply x⟩
    · rintro ⟨z,hz,rfl⟩
      simpa only [planeClosedAnnulus,mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hz
  rw [he]
  exact (complexClosedAnnulus_isCompact ε).image Complex.equivRealProdCLM.continuous

theorem planeRadialStep_zero {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {x : RadialPlane}
    (hx : ‖Complex.equivRealProdCLM.symm x‖≤1-ε) : planeRadialStep ε x=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hd : 0<(1+ε)^2-(1-ε)^2 := by nlinarith
  apply div_nonpos_of_nonpos_of_nonneg _ hd.le
  rw [planeRadiusSq_norm]
  nlinarith [norm_nonneg (Complex.equivRealProdCLM.symm x)]

theorem planeRadialStep_one {ε : ℝ} (hε : 0<ε) {x : RadialPlane}
    (hx : 1+ε≤‖Complex.equivRealProdCLM.symm x‖) : planeRadialStep ε x=1 := by
  apply Real.smoothTransition.one_of_one_le
  have hd : 0<(1+ε)^2-(1-ε)^2 := by nlinarith
  rw [le_div_iff₀ hd]
  rw [planeRadiusSq_norm]
  nlinarith

theorem planeRadialDifferential_zero {ε : ℝ} (hε : 0<ε) (hε1 : ε<1)
    (x : RadialPlane) (hx : x∉planeClosedAnnulus ε) :
    manifoldScalarDifferential (E := RadialPlane) (planeRadialStep ε) x=0 := by
  have hn := continuous_norm.comp Complex.equivRealProdCLM.symm.continuous
  change ¬(1-ε≤‖Complex.equivRealProdCLM.symm x‖ ∧
    ‖Complex.equivRealProdCLM.symm x‖≤1+ε) at hx
  by_cases hl : ‖Complex.equivRealProdCLM.symm x‖<1-ε
  · have he : planeRadialStep ε =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [(isOpen_lt hn continuous_const).mem_nhds hl] with y hy
      exact planeRadialStep_zero hε hε1 hy.le
    exact he.mfderiv_eq.trans (by
      simp only [mfderiv_const,ContinuousLinearMap.comp_zero]
      rfl)
  · have hu : 1+ε<‖Complex.equivRealProdCLM.symm x‖ :=
      lt_of_not_ge (fun h => hx ⟨le_of_not_gt hl,h⟩)
    have he : planeRadialStep ε =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
      filter_upwards [(isOpen_lt continuous_const hn).mem_nhds hu] with y hy
      exact planeRadialStep_one hε hy.le
    exact he.mfderiv_eq.trans (by
      simp only [mfderiv_const,ContinuousLinearMap.comp_zero]
      rfl)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable (m : ℕ)

theorem annulusWidth_pos : 0<annulusWidth m := (exists_annulusWidth m).choose_spec.1

theorem annulusWidth_lt : annulusWidth m<1/2 := (exists_annulusWidth m).choose_spec.2.1

theorem annulusWidth_subset : planeClosedAnnulus (annulusWidth m)⊆(annulusDiffeomorph m).source :=
  (exists_annulusWidth m).choose_spec.2.2

theorem compactDualForm_smooth : SmoothOneFormFamily (fun _ : ℝ => compactDualForm m) := by
  apply handlePushforwardOneForm_smooth (annulusDiffeomorph m)
    (planeClosedAnnulus_compact (annulusWidth m)) (annulusWidth_subset m)
  · exact manifoldScalarDifferential_smooth (planeRadialStep_smooth _).contMDiff
  · exact planeRadialDifferential_zero (annulusWidth_pos m)
      (lt_trans (annulusWidth_lt m) (by norm_num))

theorem compactDualForm_compact : HasCompactSupport (compactDualForm m) := by
  exact handlePushforwardOneForm_compact (annulusDiffeomorph m)
    (planeClosedAnnulus_compact (annulusWidth m)) (annulusWidth_subset m)
    (planeRadialDifferential_zero (annulusWidth_pos m)
      (lt_trans (annulusWidth_lt m) (by norm_num)))

theorem compactDualForm_closed (x : Surface m) : manifoldExteriorOneForm (compactDualForm m) x=0 := by
  apply handlePushforwardOneForm_closed (annulusDiffeomorph m)
    (planeClosedAnnulus_compact (annulusWidth m)) (annulusWidth_subset m)
  · exact manifoldScalarDifferential_smooth (planeRadialStep_smooth _).contMDiff
  · exact planeRadialDifferential_zero (annulusWidth_pos m)
      (lt_trans (annulusWidth_lt m) (by norm_num))
  · exact manifoldScalarDifferential_closed (planeRadialStep_smooth _).contMDiff

theorem transverseCycle_periodic : Function.Periodic (transverseCycle m) (2*Real.pi) := by
  intro θ
  apply Subtype.ext
  simp only [transverseCycle,transversePoint,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem transversePoint_smooth : ContDiff ℝ ∞ (transversePoint m) := by
  apply ContDiff.prodMk
  · exact Complex.ofRealCLM.contDiff.comp Real.contDiff_cos
  · apply contDiff_pi.mpr
    intro j
    by_cases hj : j=0
    · simp only [ite_eq_left hj]
      exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp Real.contDiff_sin)
    · simp only [ite_eq_right hj]
      apply contDiff_const.mul
      apply Complex.ofRealCLM.contDiff.comp
      have hp : ∀ θ : ℝ,0<(j.val : ℝ)+1-Real.cos θ^2 := by
        intro θ
        have hjp : 0<j.val := Fin.pos_iff_ne_zero.mpr hj
        have hr : 0<(j.val : ℝ) := by exact_mod_cast hjp
        nlinarith [Real.cos_sq_le_one θ]
      exact (contDiff_const.sub (Real.contDiff_cos.pow 2)).sqrt (fun θ => (hp θ).ne')

theorem transverseCycle_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,RealModel) ∞ (transverseCycle m) := by
  intro θ
  rw [← contMDiffWithinAt_univ]
  exact real_contMDiffWithinAt_of_ambient (parameters m) (transversePoint_smooth m).contDiffAt.contDiffWithinAt

theorem transverseCycle_coordinate (θ : ℝ) :
    annulusCoordinate m (transverseCycle m θ).val=
      Complex.I*((Real.sin θ+Real.sqrt (1+Real.sin θ^2) : ℝ) : ℂ) := by
  change (transversePoint m θ).2 0+(transversePoint m θ).2 1=_
  rw [transversePoint_zero,transversePoint_one,Complex.ofReal_add,mul_add]

theorem transverseCycle_branch_iff (θ : ℝ) :
    transverseCycle m θ∈annulusBranch m ↔ 0<Real.cos θ := by
  constructor
  · intro h
    exact h.2.1
  · intro h
    have hb : baseSquare (annulusCoordinate m (transverseCycle m θ).val)=(Real.cos θ : ℂ)^2 :=
      baseSquare_coordinate m (transversePoint_mem m θ)
    refine ⟨⟨annulusCoordinate_ne_zero m (transversePoint_mem m θ),?_,?_⟩,h,?_⟩
    · rw [hb,← Complex.ofReal_pow,Complex.ofReal_re]
      positivity
    · intro j hj
      rw [hb]
      simp only [parameters,Complex.sub_re,Complex.add_re,Complex.natCast_re,
        Complex.one_re,← Complex.ofReal_pow,Complex.ofReal_re]
      have hjp : (1:ℝ)<j.val := by exact_mod_cast hj
      nlinarith [Real.cos_sq_le_one θ]
    · intro j hj
      have hj0 : j≠0 := by intro he; subst j; simp at hj
      change 0<(if j=0 then Complex.I*(Real.sin θ : ℂ)
        else Complex.I*(Real.sqrt ((j.val : ℝ)+1-Real.cos θ^2) : ℂ)).im
      simp only [ite_eq_right hj0,Complex.mul_im,Complex.I_re,Complex.I_im,
        zero_mul,one_mul,zero_add,Complex.ofReal_re]
      apply Real.sqrt_pos.mpr
      have hjp : (1:ℝ)<j.val := by exact_mod_cast hj
      nlinarith [Real.cos_sq_le_one θ]

theorem transverseRadius_pos (θ : ℝ) : 0<transverseRadius θ := by
  have hp : 0<1+Real.sin θ^2 := by positivity
  have hs := Real.sq_sqrt hp.le
  have hn := Real.sqrt_pos.mpr hp
  unfold transverseRadius
  nlinarith

theorem transverseCycle_coord_norm (θ : ℝ) :
    ‖annulusCoordinate m (transverseCycle m θ).val‖=transverseRadius θ := by
  rw [transverseCycle_coordinate,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
    Real.norm_eq_abs]
  exact abs_of_pos (transverseRadius_pos θ)

theorem transverseRadius_lower : transverseRadius (-(Real.pi/2))<1/2 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : 0≤Real.sqrt 2 := Real.sqrt_nonneg 2
  norm_num [transverseRadius,Real.sin_neg,Real.sin_pi_div_two]
  nlinarith

theorem transverseRadius_upper : 3/2<transverseRadius (Real.pi/2) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : 0≤Real.sqrt 2 := Real.sqrt_nonneg 2
  norm_num [transverseRadius,Real.sin_pi_div_two]
  nlinarith

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem curveOneForm_smooth {α : ManifoldOneForm E M} {q : ℝ → M}
    (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (hq : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ q) : ContDiff ℝ ∞ (curveOneForm α q) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hs := (euclideanPullbackOneForm_contDiffAt (α := fun _ => α) (g := q) (p := (0,t)) hα (hq t)).comp t
    (contDiffAt_const.prodMk contDiffAt_id)
  exact hs.clm_apply contDiffAt_const

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
theorem curveOneForm_pushforward_scalar
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f)
    {q : ℝ → N} (hq : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,F) ∞ q)
    {t : ℝ} (ht : q t∈e.target) :
    curveOneForm (handlePushforwardOneForm e (manifoldScalarDifferential (E := E) f)) q t=
      deriv (f ∘ e.symm ∘ q) t := by
  have hi := e.symm.mdifferentiableAt (by simp) ht
  have hq' := hq.mdifferentiableAt (x := t) (by simp)
  have hd₁ := mfderiv_comp t hi hq'
  have hd₂ := mfderiv_comp t (hf.mdifferentiableAt (by simp)) (hi.comp t hq')
  rw [mfderiv_eq_fderiv] at hd₂
  rw [hd₁] at hd₂
  change (extendManifoldOneForm (E := F) e.target
    (manifoldPullbackOneForm (E := E) (F := F) (fun _ => manifoldScalarDifferential (E := E) f) e.symm 0) (q t))
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,F) q t 1)=_
  rw [extendManifoldOneForm_inside ht]
  exact (congrArg (fun D : ℝ →L[ℝ] ℝ => D 1) hd₂).symm

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

variable (m : ℕ)

theorem transverseRealCoordinate_smooth : ContDiff ℝ ∞ (transverseRealCoordinate m) :=
  Complex.equivRealProdCLM.contDiff.comp
    (((annulusCoordinate m).restrictScalars ℝ).contDiff.comp (transversePoint_smooth m))

theorem transverseStep_smooth : ContDiff ℝ ∞ (transverseStep m) :=
  (planeRadialStep_smooth _).comp (transverseRealCoordinate_smooth m)

theorem dualAlongCycle_smooth : ContDiff ℝ ∞ (dualAlongCycle m) :=
  curveOneForm_smooth (compactDualForm_smooth m) (transverseCycle_smooth m)

theorem dualAlongCycle_zero {θ : ℝ} (hθ : Real.cos θ≤0) : dualAlongCycle m θ=0 := by
  have ht : transverseCycle m θ∉(annulusDiffeomorph m).target := by
    rw [annulusDiffeomorph_target,transverseCycle_branch_iff]
    exact not_lt.mpr hθ
  change (extendManifoldOneForm (annulusDiffeomorph m).target _ (transverseCycle m θ)) _=0
  rw [extendManifoldOneForm_outside ht]
  rfl

theorem dualAlongCycle_deriv {θ : ℝ} (hθ : 0<Real.cos θ) :
    dualAlongCycle m θ=deriv (transverseStep m) θ := by
  have ht : transverseCycle m θ∈(annulusDiffeomorph m).target := by
    rw [annulusDiffeomorph_target,transverseCycle_branch_iff]
    exact hθ
  exact curveOneForm_pushforward_scalar (annulusDiffeomorph m)
    (planeRadialStep_smooth _).contMDiff (transverseCycle_smooth m) ht

theorem transverseStep_lower : transverseStep m (-(Real.pi/2))=0 := by
  apply planeRadialStep_zero (annulusWidth_pos m) (lt_trans (annulusWidth_lt m) (by norm_num))
  change ‖Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM _)‖≤_
  rw [ContinuousLinearEquiv.symm_apply_apply,transverseCycle_coord_norm]
  linarith [transverseRadius_lower,annulusWidth_lt m]

theorem transverseStep_upper : transverseStep m (Real.pi/2)=1 := by
  apply planeRadialStep_one (annulusWidth_pos m)
  change _≤‖Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM _)‖
  rw [ContinuousLinearEquiv.symm_apply_apply,transverseCycle_coord_norm]
  linarith [transverseRadius_upper,annulusWidth_lt m]

theorem dualAlongCycle_integral_first :
    ∫ θ in -(Real.pi/2)..Real.pi/2,dualAlongCycle m θ=1 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤Real.pi/2)
    (transverseStep_smooth m).continuous.continuousOn
    (fun θ hθ => ?_)
    ((dualAlongCycle_smooth m).continuous.intervalIntegrable _ _)
  · simpa only [transverseStep_lower,transverseStep_upper,sub_zero] using he
  · rw [dualAlongCycle_deriv m (Real.cos_pos_of_mem_Ioo hθ)]
    exact ((transverseStep_smooth m).differentiable (by simp) θ).hasDerivAt

theorem dualAlongCycle_integral_second :
    ∫ θ in Real.pi/2..Real.pi+Real.pi/2,dualAlongCycle m θ=0 := by
  calc
    _ = ∫ θ in Real.pi/2..Real.pi+Real.pi/2,(0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le (by linarith [Real.pi_pos] : Real.pi/2≤Real.pi+Real.pi/2)] at hθ
      exact dualAlongCycle_zero m (Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 hθ.2)
    _ = 0 := by simp

theorem compactDualForm_period :
    ∫ θ in -(Real.pi/2)..Real.pi+Real.pi/2,
      curveOneForm (compactDualForm m) (transverseCycle m) θ=1 := by
  have hi := (dualAlongCycle_smooth m).continuous
  change ∫ θ in -(Real.pi/2)..Real.pi+Real.pi/2,dualAlongCycle m θ=1
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.pi/2) (hi.intervalIntegrable _ _) (hi.intervalIntegrable _ _),
    dualAlongCycle_integral_first,dualAlongCycle_integral_second,add_zero]

end PackingSufficiencySupport.DiagonalQuadrics.Explicit
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_QuadricNormalizedCycle
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem curveOneForm_affine {α : ManifoldOneForm E M} {q : ℝ → M}
    (hq : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ q) (a b t : ℝ) :
    curveOneForm α (fun s => q (a*s+b)) t=a*curveOneForm α q (a*t+b) := by
  let h : ℝ → ℝ := fun s => a*s+b
  have hd : HasDerivAt h a t := by
    simpa only [h,id_eq,mul_one] using ((hasDerivAt_id t).const_mul a).add_const b
  have he := mfderiv_comp t (hq.mdifferentiableAt (by simp))
    (hasMFDerivAt_iff_hasFDerivAt.mpr hd.hasFDerivAt).mdifferentiableAt
  have he' := congrArg (fun D : ℝ →L[ℝ] E => D 1) he
  have hh : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) h t 1=a := by
    have hh := congrArg (fun D : ℝ →L[ℝ] ℝ => D 1)
      (mfderiv_eq_fderiv (f := h) (x := t))
    have hh' : fderiv ℝ h t 1=a := by
      rw [hd.hasFDerivAt.fderiv]
      simp
    exact hh.trans hh'
  change mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (q ∘ h) t 1=
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) q (h t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) h t 1) at he'
  rw [hh] at he'
  change α (q (h t)) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (q ∘ h) t 1)=_
  rw [he']
  let L : ℝ →L[ℝ] ℝ := (α (q (h t))).comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) q (h t))
  change L a = a * L 1
  simpa only [smul_eq_mul, mul_one] using L.map_smul a (1:ℝ)

theorem curveOneForm_periodic {α : ManifoldOneForm E M} {q : ℝ → M}
    (hq : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ q) {T : ℝ} (hp : Periodic q T) :
    Periodic (curveOneForm α q) T := by
  have he : (fun s => q (1*s+T))=q := by ext s; simp only [one_mul,hp s]
  intro t
  have hd := curveOneForm_affine (α := α) hq 1 T t
  rw [he,one_mul,one_mul] at hd
  exact hd.symm

theorem curveOneForm_period_integral {α : ManifoldOneForm E M} {q : ℝ → M}
    (hq : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ q) {T : ℝ} (hp : Periodic q T) (b c : ℝ) :
    (∫ t in b..b+T,curveOneForm α q t)=(∫ t in c..c+T,curveOneForm α q t) := by
  exact (curveOneForm_periodic hq hp).intervalIntegral_add_eq _ _

end

theorem cylinderFormB_curve (α : ℝ → ManifoldOneForm CylinderModel HandleCylinder)
    (p a t : ℝ) : cylinderFormB α (p,(a,t))=
      curveOneForm (α p) (fun s => (a,circleTurn s)) t := by
  let j : ℝ → Plane := fun s => (a,s)
  have hj : HasFDerivAt j (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
    (hasFDerivAt_const a t).prodMk (hasFDerivAt_id t)
  have hg := ((cylinderCover_smooth.mdifferentiableAt (by simp)).hasMFDerivAt.comp t
    (hasMFDerivAt_iff_hasFDerivAt.mpr hj)).mfderiv
  change α p (a,circleTurn t)
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover (a,t) (0,1))=
    α p (a,circleTurn t)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CylinderModel) (cylinderCover ∘ j) t 1)
  rw [hg]
  rfl

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem curveOneForm_parameter_pullback (α : ℝ → ManifoldOneForm E M)
    {g : N → M} {q : ℝ → N} {t p : ℝ}
    (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g (q t))
    (hq : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,F) q t) :
    curveOneForm (parameterManifoldPullbackOneForm (E := E) (F := F) α g p) q t=
      curveOneForm (α p) (g ∘ q) t := by
  have hd := mfderiv_comp t hg hq
  change α p (g (q t)) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g (q t)
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,F) q t 1))=
    α p (g (q t)) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (g ∘ q) t 1)
  rw [hd]
  rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

variable (m : ℕ)

theorem transverseCycle_Acoordinate (θ : ℝ) :
    transverseCoordinate m (transverseCycle m θ).val=(Circle.exp θ : ℂ) := by
  change (Real.cos θ : ℂ)+Complex.I*(Real.sin θ : ℂ)=_
  rw [Circle.coe_exp,Complex.exp_mul_I]
  rw [← Complex.ofReal_cos,← Complex.ofReal_sin,mul_comm Complex.I]

theorem transverseCycle_transverseBranch (θ : ℝ) :
    transverseCycle m θ∈transverseBranch m := by
  refine ⟨?_,?_⟩
  · rw [transverseCycle_Acoordinate]
    exact unitCircle_subset_transverseDomain m (Circle.norm_coe _)
  · intro j hj
    change 0<(if j=0 then Complex.I*(Real.sin θ : ℂ)
      else Complex.I*(Real.sqrt ((j.val : ℝ)+1-Real.cos θ^2) : ℂ)).im
    simp only [ite_eq_right hj,Complex.mul_im,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,zero_add,Complex.ofReal_re]
    apply Real.sqrt_pos.mpr
    have hjp : 0<(j.val : ℝ) := by exact_mod_cast Fin.pos_iff_ne_zero.mpr hj
    nlinarith [Real.cos_sq_le_one θ]

theorem transverseCylinder_core_cycle (t : ℝ) :
    transverseCylinder m (0,circleTurn t)=transverseCycle m (2*Real.pi*t) := by
  have he := (transverseAnnulusChart m).left_inv (transverseCycle_transverseBranch m (2*Real.pi*t))
  change transverseAnnulusInverse m (transverseCoordinate m (transverseCycle m (2*Real.pi*t)).val)=_ at he
  rw [transverseCycle_Acoordinate] at he
  simpa only [transverseCylinder_apply,cylinderComplexMap,Real.exp_zero,
    Complex.ofReal_one,one_mul,circleTurn] using he

theorem cylinderDualForm_B (p t : ℝ) :
    cylinderFormB (cylinderDualForm m) (p,(0,t))=
      curveOneForm (compactDualForm m) (fun s => transverseCylinder m (0,circleTurn s)) t := by
  rw [cylinderFormB_curve]
  exact curveOneForm_parameter_pullback (fun _ : ℝ => compactDualForm m)
    ((transverseCylinder m).mdifferentiableAt (by simp) (transverseCylinder_core m _))
    ((cylinderCover_smooth.comp ((contDiff_const.prodMk contDiff_id).contMDiff)).mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

theorem cylinderDualForm_period (p : ℝ) : cylinderFormPeriod 0 (cylinderDualForm m) p=1 := by
  unfold cylinderFormPeriod annularMean
  simp_rw [cylinderDualForm_B]
  have he : (fun s => transverseCylinder m (0,circleTurn s))=
      (fun s => transverseCycle m (2*Real.pi*s+0)) := by
    funext s
    rw [add_zero]
    exact transverseCylinder_core_cycle m s
  rw [he]
  simp_rw [curveOneForm_affine (transverseCycle_smooth m),add_zero]
  rw [intervalIntegral.integral_const_mul]
  change (2*Real.pi) • (∫ t in (0:ℝ)..1,
    curveOneForm (compactDualForm m) (transverseCycle m) (2*Real.pi*t))=1
  rw [intervalIntegral.smul_integral_comp_mul_left]
  simp only [mul_zero,mul_one]
  have hp := curveOneForm_period_integral (α := compactDualForm m)
    (transverseCycle_smooth m) (transverseCycle_periodic m) 0 (-(Real.pi/2))
  rw [zero_add,show -(Real.pi/2)+2*Real.pi=Real.pi+Real.pi/2 by ring] at hp
  rw [hp]
  exact compactDualForm_period m

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem annularCylinderScalar_joint_smoothOn {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) {F : P × Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => F (p,(s,t))) 1) :
    ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel)) 𝓘(ℝ,ℝ) ∞
      (fun q : P × HandleCylinder => annularCylinderScalar F q.1 q.2)
      (V ×ˢ (I ×ˢ univ)) := by
  have hfst : ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞
      (Prod.fst : HandleCylinder → ℝ) := by
    rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
      modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hparam : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel)) 𝓘(ℝ,P) ∞
      (Prod.fst : P × HandleCylinder → P) := contMDiff_fst
  have hbase : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel)) 𝓘(ℝ,CylinderModel) ∞
      (Prod.snd : P × HandleCylinder → HandleCylinder) := contMDiff_snd
  have hpair : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel)) 𝓘(ℝ,P × ℝ) ∞
      (fun q : P × HandleCylinder => (q.1,q.2.1)) := by
    exact (contMDiff_prod_module_iff _).2 ⟨hparam,hfst.comp hbase⟩
  have hmap : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel))
      ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) ∞
      (fun q : P × HandleCylinder => ((q.1,q.2.1),q.2.2)) :=
    hpair.prodMk (cylinder_snd_smooth.comp hbase)
  exact (annularScalarDescent_smoothOn hV hI hF hper).comp hmap.contMDiffOn
    (fun _ hq => ⟨⟨hq.1,hq.2.1⟩,hq.2.2⟩)

end
section

variable {P : Type} {E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace G N]

theorem manifoldScalarDifferential_comp_at {f : N → ℝ} {e : M → N} {x : M}
    (hf : ContMDiffAt 𝓘(ℝ,G) 𝓘(ℝ,ℝ) ∞ f (e x))
    (he : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ e x) :
    manifoldScalarDifferential (E := E) (f ∘ e) x=
      (manifoldScalarDifferential (E := G) f (e x)).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) e x) :=
  mfderiv_comp x (hf.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))

theorem annularCylinderScalar_family_pullback_smoothOn {V : Set P} {I : Set ℝ} {U : Set M}
    (hV : IsOpen V) (hI : IsOpen I) {F : P × Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => F (p,(s,t))) 1)
    {e : M → HandleCylinder} (he : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) ∞ e U)
    (hmem : ∀ x∈U,(e x).1∈I) :
    ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun q : P × M => annularCylinderScalar F q.1 (e q.2)) (V ×ˢ U) := by
  have hg : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E))
      ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel)) ∞
      (fun q : P × M => (q.1,e q.2)) (V ×ˢ U) :=
    contMDiffOn_fst.prodMk (he.comp contMDiffOn_snd (fun _ hq => hq.2))
  exact (annularCylinderScalar_joint_smoothOn hV hI hF hper).comp hg
    (fun q hq => ⟨hq.1,hmem q.2 hq.2,mem_univ _⟩)

end

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

theorem exists_closed_annular_coordinate_potential {V : Set P} {I : Set ℝ} {U : Set M}
    (hV : IsOpen V) (hI : IsOpen I) (hU : IsOpen U) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I)
    {α : P → ManifoldOneForm CylinderModel HandleCylinder}
    {A B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (I ×ˢ univ)))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ)))
    (hβ : ContDiff ℝ ∞ β) (hpβ : Periodic β 1)
    (hβint : (∫ t in (0:ℝ)..1,β t)=1)
    (hpA : ∀ p∈V,∀ s∈I,Periodic (fun t => A (p,(s,t))) 1)
    (hpB : ∀ p∈V,∀ s∈I,Periodic (fun t => B (p,(s,t))) 1)
    (hα : ∀ p∈V,∀ q : Plane,q.1∈I → ContDiffAt ℝ ∞
      (chartOneForm (α p) (cylinderCover q))
      (extChartAt 𝓘(ℝ,CylinderModel) (cylinderCover q) (cylinderCover q)))
    (hclosed : ∀ p∈V,∀ z : HandleCylinder,z.1∈I → manifoldExteriorOneForm (α p) z=0)
    (hrep : ∀ p∈V,∀ q : Plane,q.1∈I →
      euclideanPullbackOneForm (fun _ => α p) cylinderCover (0,q)=
        planarCovector (A (p,q)) (B (p,q)))
    {e : M → HandleCylinder} (he : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) ∞ e U)
    (hmem : ∀ x∈U,(e x).1∈I) :
    ∃ F : P × M → ℝ,
      ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ U) ∧
      ∀ p∈V,∀ x∈U,∀ v : E,
        manifoldScalarDifferential (E := E) (fun y => F (p,y)) x v=
          α p (e x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e x v)-
            annularMean a B p*circlePeriodicDescent β (e x).2*
              circleAngular (e x).2 (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e x v).2 := by
  have hcurl : ∀ p∈V,∀ s∈I,∀ t,
      fderiv ℝ (fun z => A (p,z)) (s,t) (0,1)=
      fderiv ℝ (fun z => B (p,z)) (s,t) (1,0) := by
    intro p hp s hs t
    exact closed_cylinder_cover_equation hI
      (hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩))
      (hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩))
      (hα p hp) (hclosed p hp) (hrep p hp) hs
  obtain ⟨hF,hper,_⟩ := annular_normalization hV hI hc ha hA hB hβ hpβ hβint hpA hpB hcurl
  obtain ⟨_,hFd⟩ := closed_cylinder_normalized_potential hV hI hc ha hA hB
    hβ hpβ hβint hpA hpB hα hclosed hrep
  refine ⟨fun q => annularCylinderScalar (normalizedAnnularPrimitive a A B β) q.1 (e q.2),
    annularCylinderScalar_family_pullback_smoothOn hV hI hF hper he hmem,?_⟩
  intro p hp x hx v
  have hd := manifoldScalarDifferential_comp_at
    (annularCylinderScalar_smoothAt hV hI hF hper hp (hmem x hx))
    (he.contMDiffAt (hU.mem_nhds hx))
  change (manifoldScalarDifferential (E := E)
    (annularCylinderScalar (normalizedAnnularPrimitive a A B β) p ∘ e) x) v=_
  rw [hd]
  exact hFd p hp (e x) (hmem x hx) _

theorem exists_intrinsic_annular_coordinate_potential
    {V : Set P} {I : Set ℝ} {U : Set M}
    (hV : IsOpen V) (hI : IsOpen I) (hU : IsOpen U) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I)
    {α : P → ManifoldOneForm CylinderModel HandleCylinder}
    (hα : ∀ p∈V,∀ z : HandleCylinder,z.1∈I → ContDiffAt ℝ ∞
      (fun q : P × CylinderModel => chartOneForm (α q.1) z q.2)
      (p,extChartAt 𝓘(ℝ,CylinderModel) z z))
    (hclosed : ∀ p∈V,∀ z : HandleCylinder,z.1∈I → manifoldExteriorOneForm (α p) z=0)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfint : (∫ t in (0:ℝ)..1,f (circleTurn t))=1)
    {e : M → HandleCylinder} (he : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) ∞ e U)
    (hmem : ∀ x∈U,(e x).1∈I) :
    ∃ F : P × M → ℝ,
      ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ U) ∧
      ∀ p∈V,∀ x∈U,∀ v : E,
        manifoldScalarDifferential (E := E) (fun y => F (p,y)) x v=
          α p (e x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e x v)-
            cylinderFormPeriod a α p*f (e x).2*
              circleAngular (e x).2 (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e x v).2 := by
  have hβ : ContDiff ℝ ∞ (f ∘ circleTurn) := (hf.comp circleTurn_smooth).contDiff
  have hpβ : Periodic (f ∘ circleTurn) 1 := fun t => congrArg f (circleTurn_period_one t)
  have hα' : ∀ p∈V,∀ q : Plane,q.1∈I → ContDiffAt ℝ ∞
      (chartOneForm (α p) (cylinderCover q))
      (extChartAt 𝓘(ℝ,CylinderModel) (cylinderCover q) (cylinderCover q)) := by
    intro p hp q hq
    exact (hα p hp (cylinderCover q) hq).comp _ (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨F,hF,hd⟩ := exists_closed_annular_coordinate_potential hV hI hU hc ha
    (cylinderForm_coefficients_smooth hα).1 (cylinderForm_coefficients_smooth hα).2
    hβ hpβ hfint
    (fun p _ s _ => (cylinderForm_coefficients_periodic α p s).1)
    (fun p _ s _ => (cylinderForm_coefficients_periodic α p s).2)
    hα' hclosed (fun p _ q _ => cylinderForm_rep α p q) he hmem
  refine ⟨F,hF,?_⟩
  intro p hp x hx v
  simpa only [cylinderFormPeriod,circlePeriodicDescent,Function.comp_apply,
    circleTurn_shortCircleArgument] using hd p hp x hx v

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularChartNormalization
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_compact_annular_dual_normalization
    (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) HandleCylinder M ∞)
    {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I) (he : e.source=I ×ˢ univ)
    {a : ℝ} (ha : a∈I) {K : Set M} (hK : IsCompact K) (hKA : K⊆e.target)
    {β : ManifoldOneForm E M} (hβ : SmoothOneFormFamily (fun _ : ℝ => β))
    (hclosed : ∀ x,manifoldExteriorOneForm β x=0) (hcompact : HasCompactSupport β)
    (hperiod : cylinderFormPeriod a (parameterManifoldPullbackOneForm (fun _ : ℝ => β) e) 0=1)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfint : (∫ t in (0:ℝ)..1,f (circleTurn t))=1) :
    ∃ (β' : ManifoldOneForm E M) (L W : Set M),
      IsCompact L ∧ L⊆e.target ∧ IsOpen W ∧ K⊆W ∧ W⊆e.target ∧
      SmoothOneFormFamily (fun _ : ℝ => β') ∧ HasCompactSupport β' ∧
      (∀ x,manifoldExteriorOneForm β' x=0) ∧
      support (β'-β)⊆L ∧
      ∀ z∈e.source,e z∈W → ∀ v : CylinderModel,
        β' (e z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) e z v)=
          f z.2*circleAngular z.2 v.2 := by
  let α := parameterManifoldPullbackOneForm (E := E) (F := CylinderModel) (fun _ : ℝ => β) e
  have hβat (p : ℝ) (x : M) : ContDiffAt ℝ ∞
      (fun q : ℝ × E => chartOneForm β x q.2) (p,extChartAt 𝓘(ℝ,E) x x) :=
    (hβ x).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x)).mem_nhds
      ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x)⟩)
  have hsrc (z : HandleCylinder) (hz : z.1∈I) : z∈e.source := by
    rw [he]; exact ⟨hz,mem_univ _⟩
  have hα (p : ℝ) (_hp : p∈(univ : Set ℝ)) (z : HandleCylinder) (hz : z.1∈I) : ContDiffAt ℝ ∞
      (fun q : ℝ × CylinderModel => chartOneForm (α q.1) z q.2)
      (p,extChartAt 𝓘(ℝ,CylinderModel) z z) :=
    parameterManifoldPullbackOneForm_contDiffAt (hβat p (e z))
      (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hsrc z hz)))
  have hαclosed (p : ℝ) (_hp : p∈(univ : Set ℝ)) (z : HandleCylinder) (hz : z.1∈I) :
      manifoldExteriorOneForm (α p) z=0 := by
    change manifoldExteriorOneForm (manifoldPullbackOneForm (E := E) (F := CylinderModel) (fun _ => β) e 0) z=0
    rw [manifold_pullback_exterior_at (α := β) (g := e) (b := z)
      ((hβat p (e z)).comp _ (contDiffAt_const.prodMk contDiffAt_id))
      (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hsrc z hz)))]
    dsimp only [manifoldPullbackTwoForm]
    rw [hclosed]
    rfl
  have hmem (x : M) (hx : x∈e.target) : (e.symm x).1∈I := by
    have hm := e.map_target hx
    rw [he] at hm
    exact hm.1
  obtain ⟨F,hF,hFd⟩ := exists_intrinsic_annular_coordinate_potential isOpen_univ hI
    e.open_target hc ha hα hαclosed hf hfint e.symm.contMDiffOn hmem
  let N : ℝ → ManifoldOneForm E M := fun _ => manifoldPullbackOneForm
    (fun _ => cylinderClockPrimitive (fun _ => 1) f) e.symm 0
  have hFd' : ∀ p∈(univ : Set ℝ),∀ x∈e.target,
      manifoldScalarDifferential (E := E) (fun y => F (p,y)) x=
        β x-N p x-(0:ℝ) • (0 : ManifoldOneForm E M) x := by
    intro p hp x hx
    apply ContinuousLinearMap.ext
    intro v
    rw [hFd p hp x hx v]
    have hd := parameterManifoldPullbackOneForm_inverse_apply e (fun _ : ℝ => β) p hx v
    change α p (e.symm x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e.symm x v)=_ at hd
    rw [hd]
    have hp' : cylinderFormPeriod a α p=1 := hperiod
    rw [hp',one_mul]
    simp only [N, sub_apply, zero_smul, sub_zero, manifoldPullbackOneForm,
      cylinderClockPrimitive, weightedCylinderAngular, one_mul, manifoldMapDifferential]
    change β x v - _ = β x v - f (e.symm x).2 *
      cylinderAngular (e.symm x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e.symm x v)
    erw [cylinderAngular_apply]
  have hz : ∀ c,ContDiffOn ℝ ∞ (chartOneForm (0 : ManifoldOneForm E M) c)
      (extChartAt 𝓘(ℝ,E) c).target := by
    intro c
    simpa only [show chartOneForm (0 : ManifoldOneForm E M) c=(fun _ => 0) from
      funext (chartOneForm_zero c)] using (contDiffOn_const : ContDiffOn ℝ ∞
        (fun _ : E => (0 : E →L[ℝ] ℝ)) (extChartAt 𝓘(ℝ,E) c).target)
  obtain ⟨Γ,L,W,hL,hLA,hW,hKW,hWA,hΓ,hsp,hcp,hd,hn⟩ :=
    exists_normalized_manifold_primitive_neighborhood (E := E) (M := M)
      (Γ := fun _ : ℝ => β) (N := N) (β := 0) (a := fun _ => 0) isOpen_univ hK e.open_target hKA
      hβ hz (fun x => manifoldExteriorOneForm_zero x) (HasCompactSupport.zero)
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ => (0:ℝ)) univ) hF hFd'
  refine ⟨Γ 0,L,W,hL,hLA,hW,hKW,hWA,?_,?_,?_,?_,?_⟩
  · intro c
    exact (hΓ c).comp (contDiff_const.prodMk contDiff_snd).contDiffOn (fun q hq => ⟨mem_univ _,hq.2⟩)
  · have hp := (hcp 0).add hcompact
    simpa only [sub_add_cancel] using hp
  · intro x
    rw [hd 0 (mem_univ _) x,hclosed]
  · simpa only [tsupport_zero,empty_union] using hsp 0
  · intro z hz' hw v
    rw [hn 0 (mem_univ _) (e z) hw]
    have hi := parameterManifoldPullbackOneForm_inverse_apply e.symm
      (fun _ : ℝ => cylinderClockPrimitive (fun _ => 1) f) 0 hz' v
    change (N 0 (e z)) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) e z v)=_
    rw [show N 0 (e z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) e z v)=
      cylinderClockPrimitive (fun _ => 1) f z v from hi]
    simp only [cylinderClockPrimitive,weightedCylinderAngular,smul_apply,smul_eq_mul,
      one_mul,cylinderAngular_apply]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

variable (m : ℕ)

theorem restrictedTransverseCylinder_source {a : ℝ}
    (ha : a≤transverseCylinderWidth m) :
    (restrictedTransverseCylinder m a).source=Ioo (-a) a ×ˢ univ := by
  apply inter_eq_right.mpr
  intro z hz
  exact transverseCylinderWidth_subset m ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,hz.2⟩

theorem exists_actual_compact_normalized_dual_fixed_bp240_oai
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfi : (∫ t in (0:ℝ)..1,f (circleTurn t))=1) :
    ∃ (a : ℝ) (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel)
      HandleCylinder (Surface m) ∞) (β : ManifoldOneForm RealModel (Surface m)),
      a=transverseCylinderWidth m/2 ∧
      e=restrictedTransverseCylinder m (transverseCylinderWidth m/2) ∧
      0<a ∧ e.source=Ioo (-a) a ×ˢ univ ∧ IsCompact (closure e.target) ∧
      SmoothOneFormFamily (fun _ : ℝ => β) ∧ HasCompactSupport β ∧
      (∀ x,manifoldExteriorOneForm β x=0) ∧
      ∀ z∈e.source,∀ v : CylinderModel,
        β (e z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) e z v)=
          f z.2*circleAngular z.2 v.2 := by
  let a := transverseCylinderWidth m
  have ha : 0<a := transverseCylinderWidth_pos m
  let e := restrictedTransverseCylinder m a
  have he : e.source=Ioo (-a) a ×ˢ univ := restrictedTransverseCylinder_source m le_rfl
  let K := e '' (Icc (-a/2) (a/2) ×ˢ (univ : Set Circle))
  have hsub : Icc (-a/2) (a/2) ×ˢ (univ : Set Circle)⊆e.source := by
    intro z hz
    rw [he]
    exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,hz.2⟩
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_univ).image_of_continuousOn
    (e.contMDiffOn.continuousOn.mono hsub)
  have hKA : K⊆e.target := image_subset_iff.mpr (fun z hz => e.map_source (hsub hz))
  have hp : cylinderFormPeriod 0
      (parameterManifoldPullbackOneForm (fun _ : ℝ => compactDualForm m) e) 0=1 :=
    cylinderDualForm_period m 0
  obtain ⟨β,L,W,_,_,_,hKW,_,hβ,hcp,hcl,_,hn⟩ := exists_compact_annular_dual_normalization
    e isOpen_Ioo (convex_Ioo (-a) a) he (show (0:ℝ)∈Ioo (-a) a by constructor <;> linarith)
    hK hKA (compactDualForm_smooth m) (compactDualForm_closed m) (compactDualForm_compact m) hp hf hfi
  let d := restrictedTransverseCylinder m (a/2)
  have hd : d.source=Ioo (-(a/2)) (a/2) ×ˢ univ :=
    restrictedTransverseCylinder_source m (by dsimp [a] <;> linarith [transverseCylinderWidth_pos m])
  have hdK : d.target⊆K := by
    intro x hx
    obtain ⟨z,hz,hzx⟩ := d.toPartialEquiv.surjOn hx
    rw [hd] at hz
    exact ⟨z,⟨⟨by linarith [hz.1.1],hz.1.2.le⟩,hz.2⟩,hzx⟩
  refine ⟨a/2,d,β,rfl,rfl,half_pos ha,hd,hK.of_isClosed_subset isClosed_closure
    (closure_minimal hdK hK.isClosed),hβ,hcp,hcl,?_⟩
  intro z hz v
  have hzK : z∈Icc (-a/2) (a/2) ×ˢ (univ : Set Circle) := by
    rw [hd] at hz
    exact ⟨⟨by linarith [hz.1.1],hz.1.2.le⟩,hz.2⟩
  exact hn z (hsub hzK) (hKW ⟨z,hzK,rfl⟩) v

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.exists_actual_compact_normalized_dual_fixed_bp240_oai := @OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.exists_actual_compact_normalized_dual_fixed_bp240_oai
