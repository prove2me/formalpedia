-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_annular_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:11.955577+00:00
-- url     : https://prove2.me/submissions/9ae72164-f39b-4995-af79-28fdddd4baff

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

section
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bilinearComp_isInvertible {A : E →L[ℝ] E →L[ℝ] ℝ} {C : E →L[ℝ] E}
    (hA : A.IsInvertible) (hC : C.IsInvertible) : (A.bilinearComp C C).IsInvertible := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨c,rfl⟩ := hC
  refine ⟨(c.trans a).trans (c.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)),?_⟩
  ext u v
  rfl


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



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

theorem euclideanExteriorOneForm_add {α β : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    euclideanExteriorOneForm (α+β) x =
      euclideanExteriorOneForm α x + euclideanExteriorOneForm β x := by
  rw [euclideanExteriorOneForm,fderiv_add hα hβ]
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,add_apply]
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
-- module Solutions.OAIQ240_BP.BallPacking_Layers_PlanarRotation
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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
-- module Solutions.OAIQ240_BP.BallPacking_Layers_SmoothFormTransport
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_spatial_fderiv {F : ℝ × E → E} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x v : E) :
    fderiv ℝ (fun y => F (t,y)) x v = fderiv ℝ F (t,x) (0,v) := by
  have hd := (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (t,x)).hasFDerivAt.comp x
    ((hasFDerivAt_const (c := t) x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  exact congrArg (fun A : E →L[ℝ] E => A v) hd.fderiv

theorem joint_time_fderiv {F X : ℝ × E → E} (hF : ContDiff ℝ ∞ F)
    (hflow : ∀ t x, HasDerivAt (fun s => F (s,x)) (X (t,F (t,x))) t) (p : ℝ × E) :
    fderiv ℝ F p (1,0) = X (p.1,F p) := by
  have hd := (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.unique (hflow p.1 p.2)


end

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_flow_fderiv {F X : ℝ × E → E} (hF : ContDiff ℝ ∞ F)
    (hflow : ∀ t x, HasDerivAt (fun s => F (s,x)) (X (t,F (t,x))) t)
    (t τ : ℝ) (x v : E) :
    fderiv ℝ F (t,x) (τ,v) = τ • X (t,F (t,x)) +
      fderiv ℝ (fun y => F (t,y)) x v := by
  rw [show (τ,v) = τ • ((1,0) : ℝ × E) + (0,v) by ext <;> simp,
    map_add,map_smul,joint_time_fderiv hF hflow,joint_spatial_fderiv hF]


end

open scoped ContDiff Topology
open Set Function



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
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
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

theorem firstBaseCoefficient_fderiv {a : ℝ × E → ℝ}
    (ha : ContDiff ℝ ∞ a) (p v : Plane × E) :
    fderiv ℝ (firstBaseCoefficient a) p v = fderiv ℝ a (p.1.1,p.2) (v.1.1,v.2) := by
  have hh := ((ha.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (p.1.1,p.2)).hasFDerivAt.comp p
    (((hasFDerivAt_fst (𝕜 := ℝ) (p := p.1)).comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))).fderiv
  exact congrArg (fun L : (Plane × E) →L[ℝ] ℝ => L v) hh

theorem firstBase_horizontalCoupling (Ω : E →L[ℝ] E →L[ℝ] ℝ)
    {a : ℝ × E → ℝ} (ha : ContDiff ℝ ∞ a) (p v w : Plane × E) :
    horizontalCoupling Ω (firstBaseCoefficient a) 0 p v w = Ω v.2 w.2 +
      fderiv ℝ a (p.1.1,p.2) (0,v.2) *w.1.1 -
      v.1.1*fderiv ℝ a (p.1.1,p.2) (0,w.2) := by
  have h0 : DifferentiableAt ℝ (0 : Plane × E → ℝ) p := differentiableAt_const 0
  rw [horizontalCoupling_eq ((firstBaseCoefficient_smooth ha).differentiable (by simp) p) h0]
  simp only [twoCovectorForm_apply,firstBaseCoefficient_fderiv ha,fderiv_zero,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]
  change Ω v.2 w.2 + (0-fderiv ℝ a (p.1.1,p.2) 0)*(v.1.1*w.1.2-v.1.2*w.1.1)+
      0*w.1.2-v.1.2*0+fderiv ℝ a (p.1.1,p.2) (0,v.2)*w.1.1-
      v.1.1*fderiv ℝ a (p.1.1,p.2) (0,w.2) = _
  simp

theorem horizontalCoupling_oneCovector_isInvertible [FiniteDimensional ℝ E]
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} (hΩ : Ω.IsInvertible)
    {A B : Plane × E → ℝ} {p : Plane × E}
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hvertical : (fderiv ℝ A p).comp (ContinuousLinearMap.inr ℝ Plane E)=0)
    (hpositive : 0<fderiv ℝ B p ((1,0),0)-fderiv ℝ A p ((0,1),0)) :
    (horizontalCoupling Ω A B p).IsInvertible := by
  rw [horizontalCoupling_eq hA hB,hvertical]
  have he (c : ℝ) (η : E →L[ℝ] ℝ) : twoCovectorForm Ω c 0 η=oneCovectorForm Ω c η := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [twoCovectorForm_apply,oneCovectorForm_apply,zero_apply,zero_mul,mul_zero,add_zero,sub_zero]
  rw [he]
  exact oneCovectorForm_isInvertible hΩ (ne_of_gt hpositive) _

theorem baseCoefficient_fderiv {a : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (p v : Plane × E) :
    fderiv ℝ (baseCoefficient a) p v=fderiv ℝ a p.1 v.1 := by
  exact congrArg (fun L : (Plane × E) →L[ℝ] ℝ => L v)
    (((ha.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p.1).hasFDerivAt.comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).fderiv)

theorem baseCoefficient_vertical {a : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (p : Plane × E) :
    (fderiv ℝ (baseCoefficient a) p).comp (ContinuousLinearMap.inr ℝ Plane E)=0 := by
  apply ContinuousLinearMap.ext
  intro z
  change fderiv ℝ (baseCoefficient a) p (0,z)=0
  rw [baseCoefficient_fderiv ha]
  exact map_zero _

theorem weightedSecondCoefficient_fderiv {b w : Plane → ℝ} {G : ℝ × E → ℝ}
    (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w) (hG : ContDiff ℝ ∞ G) (p v : Plane × E) :
    fderiv ℝ (weightedSecondCoefficient b w G) p v =
      fderiv ℝ b p.1 v.1+fderiv ℝ w p.1 v.1*G (p.1.1,p.2)+
        w p.1*fderiv ℝ G (p.1.1,p.2) (v.1.1,v.2) := by
  have hbD := (baseCoefficient_smooth (E := E) hb).differentiable (by simp) p
  have hwD := (baseCoefficient_smooth (E := E) hw).differentiable (by simp) p
  have hgD := (firstBaseCoefficient_smooth hG).differentiable (by simp) p
  change fderiv ℝ (baseCoefficient b+baseCoefficient w*firstBaseCoefficient G) p v = _
  rw [fderiv_add hbD (hwD.mul hgD),fderiv_mul hwD hgD]
  simp only [add_apply,smul_apply,smul_eq_mul,baseCoefficient_fderiv hb,baseCoefficient_fderiv hw,
    firstBaseCoefficient_fderiv hG,baseCoefficient,firstBaseCoefficient]
  ring

theorem weighted_horizontalCoupling_isInvertible [FiniteDimensional ℝ E]
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} (hΩ : Ω.IsInvertible)
    {a b w : Plane → ℝ} {G : ℝ × E → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w)
    (hG : ContDiff ℝ ∞ G) (p : Plane × E)
    (hbase : 0<fderiv ℝ b p.1 (1,0)-fderiv ℝ a p.1 (0,1))
    (hwzero : fderiv ℝ w p.1 (1,0)=0) (hwpos : 0≤w p.1)
    (hGpos : 0≤fderiv ℝ G (p.1.1,p.2) (1,0)) :
    (horizontalCoupling Ω (baseCoefficient a) (weightedSecondCoefficient b w G) p).IsInvertible := by
  apply horizontalCoupling_oneCovector_isInvertible hΩ
    ((baseCoefficient_smooth ha).differentiable (by simp) p)
    ((weightedSecondCoefficient_smooth hb hw hG).differentiable (by simp) p)
    (baseCoefficient_vertical ha p)
  rw [weightedSecondCoefficient_fderiv hb hw hG,baseCoefficient_fderiv ha]
  dsimp only
  rw [hwzero,zero_mul,add_zero]
  linarith [mul_nonneg hwpos hGpos]

end

theorem intervalClock_monotone {a b : ℝ} (hab : a < b) : Monotone (intervalClock a b) := by
  intro x y hxy
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_nonneg.mpr hab.le))

theorem intervalClock_deriv_nonneg {a b : ℝ} (hab : a < b) (s : ℝ) :
    0 ≤ deriv (intervalClock a b) s := (intervalClock_monotone hab).deriv_nonneg

theorem intervalClock_zero {a b s : ℝ} (hab : a < b) (hs : s ≤ a) : intervalClock a b s=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sub_nonneg.mpr hab.le))

theorem intervalClock_one {a b s : ℝ} (hab : a < b) (hs : b ≤ s) : intervalClock a b s=1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).2 (by linarith))

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


open scoped ContDiff Manifold Topology
open Set Function Manifold



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

theorem first_partial_eq_deriv {F : ℝ × E → ℝ} {p : ℝ × E}
    (hF : DifferentiableAt ℝ F p) :
    fderiv ℝ F p (1,0)=deriv (fun s => F (s,p.2)) p.1 := by
  exact (hF.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv.symm

theorem surfaceFirstLayer_firstDerivative {S : ℝ → ℝ} {H : E → ℝ} {ψ : E → E}
    (hS : ContDiff ℝ ∞ S) (hH : ContDiff ℝ ∞ H) (hψ : ContDiff ℝ ∞ ψ) (p : ℝ × E) :
    fderiv ℝ (surfaceFirstLayer S H ψ) p (1,0)=deriv S p.1*H (ψ p.2) := by
  rw [first_partial_eq_deriv ((surfaceFirstLayer_smooth hS hH hψ).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)]
  simpa only [surfaceFirstLayer] using ((hS.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p.1).hasDerivAt.mul_const (H (ψ p.2))).deriv

theorem surfaceFinalLayer_firstDerivative {J R : E → ℝ} {h : ι → E → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} (hJ : ContDiff ℝ ∞ J) (hR : ContDiff ℝ ∞ R)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) (p : ℝ × E) :
    fderiv ℝ (surfaceFinalLayer J h R ρ ρ₀) p (1,0)=
      (∑ i, deriv (ρ i) p.1*h i p.2)+deriv ρ₀ p.1*R p.2 := by
  rw [first_partial_eq_deriv ((surfaceFinalLayer_smooth hJ hR hh hρ hρ₀).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)]
  have hd := ((hasDerivAt_const p.1 (J p.2)).add
    (HasDerivAt.sum (u := Finset.univ) (fun i _ => (hρ i |>.differentiable (by simp) p.1).hasDerivAt.mul_const (h i p.2)))).add
    ((hρ₀.differentiable (by simp) p.1).hasDerivAt.mul_const (R p.2))
  have he : (((fun _ : ℝ => J p.2) + ∑ i, fun s => ρ i s*h i p.2) +
      fun s => ρ₀ s*R p.2) = fun s => surfaceFinalLayer J h R ρ ρ₀ (s,p.2) := by
    funext s
    simp [surfaceFinalLayer]
  rw [he] at hd
  simpa only [zero_add] using hd.deriv

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
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.surfaceFirstCorrectionCoefficient_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.surfaceSecondExtraCoefficient_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.surfaceSuspensionCoefficient_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem homeomorph_pointwise_fderiv_isInvertible (f : E ≃ₜ E) {x : E}
    (hf : DifferentiableAt ℝ f x) (hi : DifferentiableAt ℝ f.symm (f x)) :
    (fderiv ℝ f x).IsInvertible := by
  have hleft : (fderiv ℝ f.symm (f x)).comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ E := by
    rw [←fderiv_comp x hi hf]
    simp only [show (f.symm : E → E) ∘ f = id by funext y; exact f.symm_apply_apply y]
    exact fderiv_id
  have hright : (fderiv ℝ f x).comp (fderiv ℝ f.symm (f x)) = ContinuousLinearMap.id ℝ E := by
    have hh := fderiv_comp (f x) (show DifferentiableAt ℝ f (f.symm (f x)) by simpa using hf) hi
    simp only [f.symm_apply_apply] at hh
    rw [←hh]
    simp only [show (f : E → E) ∘ f.symm = id by funext y; exact f.apply_symm_apply y]
    exact fderiv_id
  refine ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℝ f x) (fderiv ℝ f.symm (f x)) ?_ ?_,rfl⟩
  · intro v
    exact congrArg (fun L : E →L[ℝ] E => L v) hleft
  · intro v
    exact congrArg (fun L : E →L[ℝ] E => L v) hright


end

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : E →L[ℝ] E →L[ℝ] ℝ}

theorem hamiltonianBaseShear_fderiv (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (p v : Plane × E) :
    fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p v =
      (v.1,(deriv θ p.1.1*v.1.1) • hamiltonianField Ω Φ.hamiltonian
        (θ p.1.1,Φ.map (θ p.1.1) p.2) + fderiv ℝ (Φ.map (θ p.1.1)) p.2 v.2) := by
  have hθd := (hθ.differentiable (by simp) p.1.1).hasDerivAt
  have htime := hθd.hasFDerivAt.comp p
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := p.1)).comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p)))
  have hinner := htime.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hf := ((Φ.smooth.differentiable (by simp) (θ p.1.1,p.2)).hasFDerivAt.comp p hinner)
  have hh := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk hf
  change HasFDerivAt (hamiltonianBaseShear Φ θ hθ) _ p at hh
  rw [hh.fderiv]
  change (v.1,fderiv ℝ (fun q : ℝ × E => Φ.map q.1 q.2) (θ p.1.1,p.2)
    (v.1.1*deriv θ p.1.1,v.2)) = _
  rw [joint_flow_fderiv Φ.smooth Φ.flow,mul_comm v.1.1]

theorem hamiltonianBaseShear_fderiv_isInvertible (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : Plane × E) :
    (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p).IsInvertible :=
  homeomorph_pointwise_fderiv_isInvertible _
    ((hamiltonianBaseShear_smooth Φ hθ).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)
    ((hamiltonianBaseShear_inverse_smooth Φ hθ).differentiable (by simp) _)

theorem baseShearPrimitiveCoefficient_vertical (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (s : ℝ) (u v : E) :
    fderiv ℝ (baseShearPrimitiveCoefficient Φ θ) (s,u) (0,v) =
      deriv θ s * spatialDifferential Φ.hamiltonian (θ s,Φ.map (θ s) u)
        (fderiv ℝ (Φ.map (θ s)) u v) := by
  have hchain := (((baseShearPrimitiveCoefficient_smooth Φ hθ).differentiable (by simp) (s,u)).hasFDerivAt.comp u
    ((hasFDerivAt_const (𝕜 := ℝ) s u).prodMk (hasFDerivAt_id (𝕜 := ℝ) u))).fderiv
  have hdH := ((Φ.hamiltonian_smooth.differentiable (by simp) (θ s,Φ.map (θ s) u)).hasFDerivAt.comp u
    ((hasFDerivAt_const (𝕜 := ℝ) (θ s) u).prodMk ((Φ.map_smooth (θ s)).differentiable (by simp) u).hasFDerivAt)).const_mul (deriv θ s)
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) (hchain.symm.trans hdH.fderiv)
  simpa [baseShearPrimitiveCoefficient,spatialDifferential,mul_comm] using he



theorem hamiltonianBaseShear_suspension (hΩ : Ω.IsInvertible)
    (hskew : ∀ v w, Ω v w = -Ω w v) (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : Plane × E) :
    (Ω.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E)).bilinearComp
      (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p) (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p) =
    horizontalCoupling Ω (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ)) 0 p := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [firstBase_horizontalCoupling Ω (baseShearPrimitiveCoefficient_smooth Φ hθ),
    baseShearPrimitiveCoefficient_vertical Φ hθ,baseShearPrimitiveCoefficient_vertical Φ hθ]
  simp only [ContinuousLinearMap.bilinearComp_apply]
  change Ω (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p v).2
    (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p w).2 = _
  rw [hamiltonianBaseShear_fderiv Φ hθ,hamiltonianBaseShear_fderiv Φ hθ]
  dsimp only
  let X := hamiltonianField Ω Φ.hamiltonian (θ p.1.1,Φ.map (θ p.1.1) p.2)
  have hXX : Ω X X=0 := by have hh := hskew X X; linarith
  have hX (z : E) : Ω X z = -spatialDifferential Φ.hamiltonian
      (θ p.1.1,Φ.map (θ p.1.1) p.2) z := hamiltonianField_contraction hΩ _ _ z
  have hright (z : E) : Ω z X = spatialDifferential Φ.hamiltonian
      (θ p.1.1,Φ.map (θ p.1.1) p.2) z := by rw [hskew,hX,neg_neg]
  change Ω ((deriv θ p.1.1*v.1.1) • X+fderiv ℝ (Φ.map (θ p.1.1)) p.2 v.2)
      ((deriv θ p.1.1*w.1.1) • X+fderiv ℝ (Φ.map (θ p.1.1)) p.2 w.2) = _
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul,hXX,hX,hright,
    Φ.symplectic]
  ring



theorem baseShear_pullback_horizontal_general (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (A B : Plane × E → ℝ) :
    staticPullbackOneForm (horizontalOneForm A B) (hamiltonianBaseShear Φ θ hθ) =
      horizontalOneForm (A ∘ hamiltonianBaseShear Φ θ hθ) (B ∘ hamiltonianBaseShear Φ θ hθ) := by
  funext p
  apply ContinuousLinearMap.ext
  intro v
  simp only [staticPullbackOneForm,ContinuousLinearMap.comp_apply,horizontalOneForm_apply,
    hamiltonianBaseShear_fderiv]
  rfl

theorem baseShear_coupling_pullback_general (hΩ : Ω.IsInvertible)
    (hskew : ∀ v w, Ω v w = -Ω w v) (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {A B : Plane × E → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (p : Plane × E) :
    (horizontalCoupling Ω A B (hamiltonianBaseShear Φ θ hθ p)).bilinearComp
      (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p) (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p) =
      horizontalCoupling Ω
        (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ) + A ∘ hamiltonianBaseShear Φ θ hθ)
        (B ∘ hamiltonianBaseShear Φ θ hθ) p := by
  have hnat := staticPullbackOneForm_exterior
    ((horizontalOneForm_smooth hA hB).contDiffAt (x := hamiltonianBaseShear Φ θ hθ p))
    ((hamiltonianBaseShear_smooth Φ hθ).contDiffAt (x := p))
  rw [baseShear_pullback_horizontal_general Φ hθ A B] at hnat
  have hsplit : horizontalOneForm
      (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ) + A ∘ hamiltonianBaseShear Φ θ hθ)
      (B ∘ hamiltonianBaseShear Φ θ hθ) =
      horizontalOneForm (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ)) 0 +
        horizontalOneForm (A ∘ hamiltonianBaseShear Φ θ hθ) (B ∘ hamiltonianBaseShear Φ θ hθ) := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    simp [horizontalOneForm_apply,add_mul,add_assoc]
  have hsum : euclideanExteriorOneForm
      (horizontalOneForm
        (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ) + A ∘ hamiltonianBaseShear Φ θ hθ)
        (B ∘ hamiltonianBaseShear Φ θ hθ)) p =
      euclideanExteriorOneForm (horizontalOneForm (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ)) 0) p +
        euclideanExteriorOneForm (horizontalOneForm (A ∘ hamiltonianBaseShear Φ θ hθ)
          (B ∘ hamiltonianBaseShear Φ θ hθ)) p := by
    rw [hsplit]
    exact euclideanExteriorOneForm_add
      ((horizontalOneForm_smooth (firstBaseCoefficient_smooth (baseShearPrimitiveCoefficient_smooth Φ hθ))
        (contDiff_const (c := (0 : ℝ)))).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)
      ((horizontalOneForm_smooth (hA.comp (hamiltonianBaseShear_smooth Φ hθ))
        (hB.comp (hamiltonianBaseShear_smooth Φ hθ))).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)
  have hsusp := hamiltonianBaseShear_suspension hΩ hskew Φ hθ p
  have hadd (F G : (Plane × E) →L[ℝ] (Plane × E) →L[ℝ] ℝ)
      (L : (Plane × E) →L[ℝ] (Plane × E)) :
      (F+G).bilinearComp L L=F.bilinearComp L L+G.bilinearComp L L := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [horizontalCoupling,hadd,←hnat,hsusp]
  simp only [horizontalCoupling,hsum]
  exact add_assoc _ _ _

theorem baseShear_weighted_isInvertible [FiniteDimensional ℝ E]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w, Ω v w = -Ω w v)
    (Φ : CompactHamiltonianIsotopy Ω) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {a b w : Plane → ℝ} {G : ℝ × E → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w)
    (hG : ContDiff ℝ ∞ G) (p : Plane × E)
    (hbase : 0<fderiv ℝ b p.1 (1,0)-fderiv ℝ a p.1 (0,1))
    (hwzero : fderiv ℝ w p.1 (1,0)=0) (hwpos : 0≤w p.1)
    (hGpos : 0≤fderiv ℝ G (p.1.1,Φ.map (θ p.1.1) p.2) (1,0)) :
    (horizontalCoupling Ω
      (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ) +
        baseCoefficient a ∘ hamiltonianBaseShear Φ θ hθ)
      (weightedSecondCoefficient b w G ∘ hamiltonianBaseShear Φ θ hθ) p).IsInvertible := by
  rw [←baseShear_coupling_pullback_general hΩ hskew Φ hθ (baseCoefficient_smooth ha)
    (weightedSecondCoefficient_smooth hb hw hG)]
  exact bilinearComp_isInvertible
    (weighted_horizontalCoupling_isInvertible hΩ ha hb hw hG
      (hamiltonianBaseShear Φ θ hθ p) hbase hwzero hwpos hGpos)
    (hamiltonianBaseShear_fderiv_isInvertible Φ hθ p)


end

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
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_SurfacePathPositivity
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.surfaceFirstCorrectionCoefficient_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.surfaceSecondExtraCoefficient_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.surfaceSuspensionCoefficient_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : E →L[ℝ] E →L[ℝ] ℝ}

variable {ι : Type*} [Fintype ι]

theorem surfaceInterpolatedLayer_firstDerivative {S : ℝ → ℝ} {K H : E → ℝ}
    {h : ι → E → ℝ} {ψ : E → E} {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hψ : ContDiff ℝ ∞ ψ)
    (hρ : ∀ i, ContDiff ℝ ∞ (ρ i)) (hρ₀ : ContDiff ℝ ∞ ρ₀) (τ : ℝ) (p : ℝ × E) :
    fderiv ℝ (surfaceInterpolatedLayer S K H h ψ ρ ρ₀ τ) p (1,0) =
      (1-τ)*(deriv S p.1*H (ψ p.2)) +
        τ*((∑ i, deriv (ρ i) p.1*h i p.2)+deriv ρ₀ p.1*surfaceRemainder K H h ψ p.2) := by
  have hF := (surfaceFirstLayer_smooth hS hH hψ).differentiable (by simp) p
  have hG := (surfaceFinalLayer_smooth (hK.sub hH) (surfaceRemainder_smooth hK hH hh hψ) hh hρ hρ₀).differentiable (by simp) p
  have hd := (hF.hasFDerivAt.const_mul (1-τ)).add (hG.hasFDerivAt.const_mul τ)
  change HasFDerivAt (surfaceInterpolatedLayer S K H h ψ ρ ρ₀ τ) _ p at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,
    surfaceFirstLayer_firstDerivative hS hH hψ,
    surfaceFinalLayer_firstDerivative (hK.sub hH) (surfaceRemainder_smooth hK hH hh hψ) hh hρ hρ₀]

theorem surfaceInterpolatedLayer_firstDerivative_nonneg {S : ℝ → ℝ} {K H : E → ℝ}
    {h : ι → E → ℝ} {ψ : E → E} {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hψ : ContDiff ℝ ∞ ψ)
    (hρ : ∀ i, ContDiff ℝ ∞ (ρ i)) (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) (p : ℝ × E)
    (hSpos : 0 ≤ deriv S p.1) (hHpos : 0 ≤ H (ψ p.2))
    (hclock : ∀ i, 0 ≤ deriv (ρ i) p.1) (hclock₀ : 0 ≤ deriv ρ₀ p.1)
    (hcap : ∀ i, 0 ≤ h i p.2) (hres : 0 ≤ surfaceRemainder K H h ψ p.2) :
    0 ≤ fderiv ℝ (surfaceInterpolatedLayer S K H h ψ ρ ρ₀ τ) p (1,0) := by
  rw [surfaceInterpolatedLayer_firstDerivative hS hK hH hh hψ hρ hρ₀]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hτ.2) (mul_nonneg hSpos hHpos))
    (mul_nonneg hτ.1 (add_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hclock i) (hcap i)))
      (mul_nonneg hclock₀ hres)))


theorem surfaceSecondPrimitive_coupling (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S) (K H : E → ℝ) (h : ι → E → ℝ)
    (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ) (a b w : Plane → ℝ) (τ : ℝ) :
    (fun x => surfaceSecondPrimitive Φ S K H h ρ ρ₀ a b w (τ,x)) =
      horizontalOneForm
        (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ S) +
          baseCoefficient a ∘ hamiltonianBaseShear Φ S hS)
        (weightedSecondCoefficient b w (surfaceInterpolatedLayer S K H h (Φ.map 1).symm ρ ρ₀ τ) ∘
          hamiltonianBaseShear Φ S hS) := by
  funext p
  apply ContinuousLinearMap.ext
  intro v
  simp only [surfaceSecondPrimitive,horizontalOneForm_apply,Pi.add_apply,Function.comp_apply,
    firstBaseCoefficient,baseShearPrimitiveCoefficient,baseCoefficient,weightedSecondCoefficient,
    hamiltonianBaseShear]
  dsimp
  ring

theorem surfaceSecondPath_isInvertible [FiniteDimensional ℝ E]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w, Ω v w = -Ω w v)
    (Φ : CompactHamiltonianIsotopy Ω) {S : ℝ → ℝ} {K H : E → ℝ} {h : ι → E → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} {a b w : Plane → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w)
    (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) (p : Plane × E)
    (hbase : 0<fderiv ℝ b p.1 (1,0)-fderiv ℝ a p.1 (0,1))
    (hwzero : fderiv ℝ w p.1 (1,0)=0) (hwpos : 0 ≤ w p.1)
    (hSpos : 0 ≤ deriv S p.1.1)
    (hHpos : 0 ≤ H ((Φ.map 1).symm (Φ.map (S p.1.1) p.2)))
    (hclock : ∀ i, 0 ≤ deriv (ρ i) p.1.1) (hclock₀ : 0 ≤ deriv ρ₀ p.1.1)
    (hcap : ∀ i, 0 ≤ h i (Φ.map (S p.1.1) p.2))
    (hres : 0 ≤ surfaceRemainder K H h (Φ.map 1).symm (Φ.map (S p.1.1) p.2)) :
    (Ω.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E) +
      euclideanExteriorOneForm (fun x => surfaceSecondPrimitive Φ S K H h ρ ρ₀ a b w (τ,x)) p).IsInvertible := by
  rw [surfaceSecondPrimitive_coupling Φ hS]
  apply baseShear_weighted_isInvertible hΩ hskew Φ hS ha hb hw
    (surfaceInterpolatedLayer_smooth hS hK hH hh (Φ.map_inverse_smooth 1) hρ hρ₀ τ) p hbase hwzero hwpos
  exact surfaceInterpolatedLayer_firstDerivative_nonneg hS hK hH hh (Φ.map_inverse_smooth 1)
    hρ hρ₀ τ hτ _ hSpos hHpos hclock hclock₀ hcap hres

end

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem chartOneForm_coefficient (f : M → ℝ) (α : ManifoldOneForm E M)
    (c : M) (y : E) : chartOneForm (fun x => f x • α x) c y=
      f ((extChartAt 𝓘(ℝ,E) c).symm y) • chartOneForm α c y := by
  ext v
  rfl

theorem annular_coefficient_smooth_on {U : Set M} (hU : IsOpen U)
    {s : M → ℝ} (hs : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s U)
    {A : P × ℝ → ℝ} (hA : ContDiff ℝ ∞ A) {α : ManifoldOneForm E M}
    (hα : ∀ c,ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (c : M) : ContDiffOn ℝ ∞
      (fun q : P × E => chartOneForm (fun x => A (q.1,s x) • α x) c q.2)
      (univ ×ˢ ((extChartAt 𝓘(ℝ,E) c).target ∩ (extChartAt 𝓘(ℝ,E) c).symm ⁻¹' U)) := by
  intro q hq
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hq.2.1)
  have hsc : ContDiffAt ℝ ∞ (fun y => s ((extChartAt 𝓘(ℝ,E) c).symm y)) q.2 :=
    ((hs.contMDiffAt (hU.mem_nhds hq.2.2)).comp q.2 hi).contDiffAt
  have hc := hA.contDiffAt.comp q (contDiffAt_fst.prodMk (hsc.comp q contDiffAt_snd))
  have ha := ((hα c).contDiffAt ((isOpen_extChartAt_target c).mem_nhds hq.2.1)).comp q contDiffAt_snd
  have hh := hc.smul ha
  change ContDiffAt ℝ ∞ (fun z : P × E =>
    A (z.1,s ((extChartAt 𝓘(ℝ,E) c).symm z.2)) • chartOneForm α c z.2) q at hh
  simpa only [chartOneForm_coefficient] using hh.contDiffWithinAt

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem annular_inverse_fst_smooth
    (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) HandleCylinder M ∞) :
    ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun x => (e.symm x).1) e.target := by
  intro x hx
  have hf : ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ (fun z : HandleCylinder => z.1) := by
    rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
      modelWithCornersSelf_prod]
    exact contMDiff_fst
  exact (hf.contMDiffAt.comp x (e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds hx))).contMDiffWithinAt

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem image_band_subset_target (D : AnnularHandleData E M) {b : ℝ} (hb : b<D.width) :
    D.chart '' band b⊆D.chart.target := by
  rintro x ⟨z,hz,rfl⟩
  exact D.chart.map_source (D.band_subset_source hb hz)

theorem off_band_inverse (D : AnnularHandleData E M) (b : ℝ) {x : M}
    (hx : x∈D.chart.target) (hn : x∉D.chart '' band b) : (D.chart.symm x).1∉Icc (-b) b := by
  intro hs
  exact hn ⟨D.chart.symm x,⟨hs,mem_univ _⟩,D.chart.right_inv hx⟩

theorem radial_zero (D : AnnularHandleData E M) {b : ℝ} (hb : 0<b)
    {x : M} (hx : x∉D.chart '' band b) : D.radial b x=0 :=
  handlePushforwardOneForm_zero D.chart (fun _ hy => cylinderRadialForm_zero hb hy) hx

theorem radial_pullback (D : AnnularHandleData E M) (b : ℝ) {z : HandleCylinder}
    (hz : z∈D.chart.source) (v : CylinderModel) :
    D.radial b (D.chart z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) D.chart z v)=
      deriv (intervalClock (-b) b) z.1*v.1 := by
  have h := handlePushforwardOneForm_pullback D.chart (cylinderRadialForm b) hz
  have hh := congrArg (fun A : CylinderModel →L[ℝ] ℝ => A v) h
  change D.radial b (D.chart z)
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) D.chart z v)=cylinderRadialForm b z v at hh
  exact hh.trans (cylinderRadialForm_apply b z v)

variable [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
theorem radial_smooth (D : AnnularHandleData E M) {b : ℝ} (hb : 0<b) (hbw : b<D.width) :
    SmoothOneFormFamily (fun _ : ℝ => D.radial b) :=
  handlePushforwardOneForm_smooth D.chart (band_compact b) (D.band_subset_source hbw)
    (cylinderRadialForm_smooth b) (fun _ hx => cylinderRadialForm_zero hb hx)

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_SurfaceSuspensionCoefficients
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
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

theorem globalSurfaceFirstPrimitive_smooth [T2Space M]
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (Φ : CompactHamiltonianIsotopy Ω) {H : V → ℝ} (hH : ContDiff ℝ ∞ H)
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (globalSurfaceFirstPrimitive D b Φ H Γ) := by
  have hr := D.radial_smooth hb hbw
  have hβ := D.dual_smooth
  have hα := extendManifoldOneForm_smooth D.chart.open_target
    (D.image_band_compact hbw).isClosed
    (D.image_band_subset_target hbw)
    (α := handleFirstCorrection D b Φ H)
    (fun c => by
      have h1 := annular_coefficient_smooth_on D.chart.open_target
        (annular_inverse_fst_smooth D.chart)
        (surfaceSuspensionCoefficient_smooth Φ (intervalClock_smooth (-b) b))
        (α := D.radial b) (fun c => (hr c).comp
          (f := fun y => ((0:ℝ),y)) (contDiffOn_const.prodMk contDiffOn_id)
          (fun _ hy => ⟨mem_univ _,hy⟩)) c
      have h2 := annular_coefficient_smooth_on D.chart.open_target
        (annular_inverse_fst_smooth D.chart)
        (surfaceFirstCorrectionCoefficient_smooth Φ (intervalClock_smooth (-b) b) hH)
        (α := D.dual) (fun c => (hβ c).comp
          (f := fun y => ((0:ℝ),y)) (contDiffOn_const.prodMk contDiffOn_id)
          (fun _ hy => ⟨mem_univ _,hy⟩)) c
      simpa only [handleFirstCorrection,chartOneForm,ContinuousLinearMap.add_comp] using h1.add h2)
    (fun p x hx hn => handleFirstCorrection_off_band D hb Φ H p hx hn)
  intro c
  have hmap : ContDiffOn ℝ ∞ (fun q : (ℝ × V) × E => (q.1.2,q.2))
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
    ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
  have hbg := (hΓ c).comp hmap (fun _ hq => ⟨mem_univ _,hq.2⟩)
  simpa only [globalSurfaceFirstPrimitive,chartOneForm_add,Function.comp_apply] using hbg.add (hα c)

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {ι : Type*} [Fintype ι]

theorem surfaceSecondCorrectionCoefficient_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} {K H : V → ℝ} {h : ι → V → ℝ} {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i,ContDiff ℝ ∞ (h i)) (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) :
    ContDiff ℝ ∞ (surfaceSecondCorrectionCoefficient Φ S K H h ρ ρ₀) := by
  have hp : ContDiff ℝ ∞ (fun p : (ℝ × V) × ℝ => (p.2,Φ.map (S p.2) p.1.2)) :=
    contDiff_snd.prodMk (Φ.smooth.comp ((hS.comp contDiff_snd).prodMk
      (contDiff_snd.comp contDiff_fst)))
  have h1 := (surfaceFirstLayer_smooth hS hH (Φ.map_inverse_smooth 1)).comp hp
  have h2 := (surfaceFinalLayer_smooth (hK.sub hH)
    (surfaceRemainder_smooth hK hH hh (Φ.map_inverse_smooth 1)) hh hρ hρ₀).comp hp
  exact ((((contDiff_const.sub (contDiff_fst.comp contDiff_fst)).mul h1).add
    ((contDiff_fst.comp contDiff_fst).mul h2)).sub
    ((hS.comp contDiff_snd).mul (hH.comp (contDiff_snd.comp contDiff_fst)))).sub
    ((contDiff_fst.comp contDiff_fst).mul ((hK.sub hH).comp (contDiff_snd.comp contDiff_fst)))

theorem surfaceSecondExtraCoefficient_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} {K H : V → ℝ} {h : ι → V → ℝ} {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i,ContDiff ℝ ∞ (h i)) (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) :
    ContDiff ℝ ∞ (surfaceSecondExtraCoefficient Φ S K H h ρ ρ₀) :=
  (surfaceSecondCorrectionCoefficient_smooth Φ hS hK hH hh hρ hρ₀).sub
    ((surfaceFirstCorrectionCoefficient_smooth Φ hS hH).comp
      ((contDiff_const.prodMk (contDiff_snd.comp contDiff_fst)).prodMk contDiff_snd))

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

variable [IsManifold 𝓘(ℝ,E) ∞ M]
theorem globalSurfaceSecondPrimitive_smooth [T2Space M]
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (Φ : CompactHamiltonianIsotopy Ω) {K H : V → ℝ} (hK : ContDiff ℝ ∞ K)
    (hH : ContDiff ℝ ∞ H) {h : ι → V → ℝ} (hh : ∀ i,ContDiff ℝ ∞ (h i))
    {ρ : ι → ℝ → ℝ} (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (hlo : ∀ s, s ≤ -b → (∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s, b ≤ s → (∀ i,ρ i s=1) ∧ ρ₀ s=1)
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ) := by
  have hβ := D.dual_smooth
  have hα := extendManifoldOneForm_smooth D.chart.open_target
    (D.image_band_compact hbw).isClosed
    (D.image_band_subset_target hbw)
    (α := handleSecondExtra D b Φ K H h ρ ρ₀)
    (fun c => annular_coefficient_smooth_on D.chart.open_target
      (annular_inverse_fst_smooth D.chart)
      (surfaceSecondExtraCoefficient_smooth Φ (intervalClock_smooth (-b) b) hK hH hh hρ hρ₀)
      (α := D.dual) (fun c => (hβ c).comp
        (f := fun y => ((0:ℝ),y)) (contDiffOn_const.prodMk contDiffOn_id)
        (fun _ hy => ⟨mem_univ _,hy⟩)) c)
    (fun p x hx hn => handleSecondExtra_off_band D hb Φ K H h ρ ρ₀ hlo hhi p hx hn)
  have hfirst := (globalSurfaceFirstPrimitive_smooth D hb hbw Φ hH hΓ).comp
    (f := fun p : ℝ × V => (1,p.2)) (contDiff_const.prodMk (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × V → V)))
  have hj := (hβ.comp (f := fun _ : ℝ × V => (0:ℝ)) contDiff_const).smul
    (contDiff_fst.mul ((hK.sub hH).comp contDiff_snd))
  exact (hfirst.add hj).add hα

end
section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

theorem globalSurfaceSecondPrimitive_normal {ι : Type*} [Fintype ι]
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) (p : ℝ × V)
    {x : M} (hx : x∈D.chart.target)
    (hN : Γ p.2 x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p.2) • D.dual x) :
    globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ p x=
      γ x+surfaceSuspensionCoefficient Φ (intervalClock (-b) b)
        ((1,p.2),(D.chart.symm x).1) • D.radial b x+
      surfaceInterpolatedLayer (intervalClock (-b) b) K H h (Φ.map 1).symm ρ ρ₀ p.1
        ((D.chart.symm x).1,
          Φ.map (intervalClock (-b) b (D.chart.symm x).1) p.2) •
        D.dual x := by
  simp only [globalSurfaceSecondPrimitive,globalSurfaceFirstPrimitive,Pi.add_apply,Pi.smul_apply,
    extendManifoldOneForm_inside hx,hN,handleFirstCorrection,handleSecondExtra,
    surfaceSecondExtraCoefficient,surfaceSecondCorrectionCoefficient,
    surfaceFirstCorrectionCoefficient,one_mul]
  ext v
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

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

 theorem dual_cover
    (D : AnnularHandleData E M)
    {q : Plane}
    (hq : cylinderCover q∈D.chart.source) (v : Plane) :
    D.dual (D.handleAnnularCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q v)=D.clock (circleTurn q.2)*v.2 := by
  rw [D.handleAnnularCover_derivative hq]
  change D.dual (D.chart (cylinderCover q))
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) D.chart (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v))=_
  erw [D.dual_pullback _ hq,cylinderCover_derivative]
  exact congrArg (D.clock (circleTurn q.2)*·) (circleAngular_unit_pullback q.2 v.2)

 theorem radial_cover
    (D : AnnularHandleData E M)
    (b : ℝ) {q : Plane} (hq : cylinderCover q∈D.chart.source)
    (v : Plane) :
    D.radial b (D.handleAnnularCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q v)=
      deriv (intervalClock (-b) b) q.1*v.1 := by
  rw [D.handleAnnularCover_derivative hq]
  change D.radial b (D.chart (cylinderCover q))
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) D.chart (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v))=_
  erw [D.radial_pullback b hq,cylinderCover_derivative]
  rfl

 theorem handleAnnularCover_inverse
    (D : AnnularHandleData E M)
    {q : Plane} (hq : cylinderCover q∈D.chart.source) :
    D.chart.symm (D.handleAnnularCover q)=cylinderCover q :=
  D.chart.left_inv hq

end

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

theorem annularCover_form_rep
    (D : AnnularHandleData E M)
    (γ : ManifoldOneForm E M) (q v : Plane) :
    γ (D.handleAnnularCover q) (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q v)=
      D.annularCoverA γ q*v.1+D.annularCoverB γ q*v.2 := by
  let L := euclideanPullbackOneForm (fun _ => γ) (D.handleAnnularCover) (0,q)
  change L v=L (1,0)*v.1+L (0,1)*v.2
  have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
  rw [show L v=L (v.1 • (1,0)+v.2 • (0,1)) from congrArg L hv]
  simp only [map_add,map_smul,smul_eq_mul]
  ring

theorem globalSurfaceSecondPrimitive_cover {ι : Type*} [Fintype ι]
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M)
    (τ : ℝ) (p : Plane × V) (hp : cylinderCover p.1∈D.chart.source)
    (hN : Γ p.2 (D.handleAnnularCover p.1)=γ (D.handleAnnularCover p.1)+
      (intervalClock (-b) b p.1.1*H p.2) • D.dual (D.handleAnnularCover p.1)) :
    euclideanPullbackOneForm
      (fun _ => productHorizontalLift (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (τ,v)))
      (flatProductMap (D.handleAnnularCover)) (0,p)=
      surfaceSecondPrimitive Φ (intervalClock (-b) b) K H h ρ ρ₀
        (D.annularCoverA γ) (D.annularCoverB γ) (fun q => D.clock (circleTurn q.2)) (τ,p) := by
  have hn := globalSurfaceSecondPrimitive_normal D b Φ K H h ρ ρ₀ Γ γ (τ,p.2) (x := D.handleAnnularCover p.1)
    (D.chart.map_source hp)
  have hi := D.handleAnnularCover_inverse hp
  have hN' : Γ p.2 (D.handleAnnularCover p.1)=γ (D.handleAnnularCover p.1)+
      (intervalClock (-b) b (D.chart.symm (D.handleAnnularCover p.1)).1*H p.2) •
        D.dual (D.handleAnnularCover p.1) := by
    simpa only [hi,cylinderCover] using hN
  have he := hn hN'
  let A : Plane →L[ℝ] E := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) D.handleAnnularCover p.1
  have hd (u : Plane) : D.dual (D.handleAnnularCover p.1) (A u) =
      D.clock (circleTurn p.1.2) * u.2 := D.dual_cover hp u
  have hr (u : Plane) : D.radial b (D.handleAnnularCover p.1) (A u) =
      deriv (intervalClock (-b) b) p.1.1 * u.1 := D.radial_cover b hp u
  have hg (u : Plane) : γ (D.handleAnnularCover p.1) (A u) =
      D.annularCoverA γ p.1 * u.1 + D.annularCoverB γ p.1 * u.2 :=
    D.annularCover_form_rep γ p.1 u
  apply ContinuousLinearMap.ext
  intro v
  rw [productHorizontalLift_pullback_apply _ (D.handleAnnularCover_smoothAt hp)]
  change (globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (τ,p.2) (D.handleAnnularCover p.1))
    (A v.1)=_
  erw [he]
  simp only [add_apply,smul_apply,smul_eq_mul,hi,cylinderCover,
    hd, hr, hg,
    surfaceSuspensionCoefficient,surfaceSecondPrimitive,horizontalOneForm_apply,one_mul]
  ring

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
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

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem annularCoverDomain_open
    (D : AnnularHandleData E M) :
    IsOpen (D.annularCoverDomain) :=
  D.chart.open_source.preimage cylinderCover_smooth.continuous

theorem annularCover_pullback_smoothAt
    (D : AnnularHandleData E M)
    {γ : ManifoldOneForm E M} {q : Plane} (hq : q∈D.annularCoverDomain)
    (hγ : ContDiffAt ℝ ∞ (chartOneForm γ (D.handleAnnularCover q))
      (extChartAt 𝓘(ℝ,E) (D.handleAnnularCover q) (D.handleAnnularCover q))) :
    ContDiffAt ℝ ∞ (fun y => euclideanPullbackOneForm (fun _ => γ) (D.handleAnnularCover) (0,y)) q := by
  have hf := hγ.comp ((0:ℝ),extChartAt 𝓘(ℝ,E) (D.handleAnnularCover q)
    (D.handleAnnularCover q)) contDiffAt_snd
  have hs := parameterEuclideanPullbackOneForm_contDiffAt (α := fun _ : ℝ => γ)
    (p := (0,q)) hf (D.handleAnnularCover_smoothAt hq)
  exact hs.comp q (contDiffAt_const.prodMk contDiffAt_id)

theorem annularCover_coefficients_smooth
    (D : AnnularHandleData E M)
    {γ : ManifoldOneForm E M}
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x)) :
    ContDiffOn ℝ ∞ (D.annularCoverA γ) (D.annularCoverDomain) ∧
    ContDiffOn ℝ ∞ (D.annularCoverB γ) (D.annularCoverDomain) := by
  constructor <;> intro q hq
  · exact ((D.annularCover_pullback_smoothAt hq
      (hγ _ (D.chart.map_source hq))).clm_apply contDiffAt_const).contDiffWithinAt
  · exact ((D.annularCover_pullback_smoothAt hq
      (hγ _ (D.chart.map_source hq))).clm_apply contDiffAt_const).contDiffWithinAt

theorem annularCover_curl
    (D : AnnularHandleData E M)
    {γ : ManifoldOneForm E M} {q : Plane} (hq : q∈D.annularCoverDomain)
    (hγ : ContDiffAt ℝ ∞ (chartOneForm γ (D.handleAnnularCover q))
      (extChartAt 𝓘(ℝ,E) (D.handleAnnularCover q) (D.handleAnnularCover q))) :
    fderiv ℝ (D.annularCoverB γ) q (1,0)-fderiv ℝ (D.annularCoverA γ) q (0,1)=
      manifoldExteriorOneForm γ (D.handleAnnularCover q)
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q (1,0))
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q (0,1)) := by
  have hs := D.annularCover_pullback_smoothAt hq hγ
  have he : (fun y => euclideanPullbackOneForm (fun _ => γ) (D.handleAnnularCover) (0,y))=
      (fun y => planarCovector (D.annularCoverA γ y) (D.annularCoverB γ y)) := by
    funext y
    apply ContinuousLinearMap.ext
    intro v
    exact D.annularCover_form_rep γ y v
  have hd := euclidean_manifold_pullback_exterior_at (D.handleAnnularCover_smoothAt hq) hγ
  have hA : ContDiffAt ℝ ∞ (D.annularCoverA γ) q := hs.clm_apply contDiffAt_const
  have hB : ContDiffAt ℝ ∞ (D.annularCoverB γ) q := hs.clm_apply contDiffAt_const
  rw [he,planarCovector_exterior_at hA hB] at hd
  have hv := congrArg (fun Ω : Plane →L[ℝ] Plane →L[ℝ] ℝ => Ω (1,0) (0,1)) hd
  simp only [smul_apply,smul_eq_mul,planarArea_apply,mul_one,mul_zero,sub_zero,
    manifoldMapDifferential] at hv
  exact hv

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_AnnularInverseDomain
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul
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

 theorem exists_smooth_base_germs {U : Set Plane} (hU : IsOpen U)
    {a b : Plane → ℝ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    {x : Plane} (hx : x∈U) :
    ∃ a' b' : Plane → ℝ, ContDiff ℝ ∞ a' ∧ ContDiff ℝ ∞ b' ∧
      a' =ᶠ[𝓝 x] a ∧ b' =ᶠ[𝓝 x] b := by
  obtain ⟨r,hr,hrU,he⟩ := exists_smooth_local_identity (hU.mem_nhds hx)
  refine ⟨a ∘ r,b ∘ r,ha.comp_contDiff hr hrU,hb.comp_contDiff hr hrU,?_,?_⟩
  · filter_upwards [he] with y hy
    exact congrArg a hy
  · filter_upwards [he] with y hy
    exact congrArg b hy

 theorem euclideanExteriorOneForm_congr_germ {α β : E → E →L[ℝ] ℝ} {x : E}
    (h : α =ᶠ[𝓝 x] β) : euclideanExteriorOneForm α x=euclideanExteriorOneForm β x := by
  simp only [euclideanExteriorOneForm,h.fderiv_eq]

 theorem surfaceSecondPath_isInvertible_local [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w, Ω v w = -Ω w v)
    (Φ : CompactHamiltonianIsotopy Ω) {S : ℝ → ℝ} {K H : E → ℝ} {h : ι → E → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} {a b w : Plane → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) {U : Set Plane} (hU : IsOpen U)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) (hw : ContDiff ℝ ∞ w)
    (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) (p : Plane × E) (hp : p.1∈U)
    (hbase : 0<fderiv ℝ b p.1 (1,0)-fderiv ℝ a p.1 (0,1))
    (hwzero : fderiv ℝ w p.1 (1,0)=0) (hwpos : 0 ≤ w p.1)
    (hSpos : 0 ≤ deriv S p.1.1)
    (hHpos : 0 ≤ H ((Φ.map 1).symm (Φ.map (S p.1.1) p.2)))
    (hclock : ∀ i, 0 ≤ deriv (ρ i) p.1.1) (hclock₀ : 0 ≤ deriv ρ₀ p.1.1)
    (hcap : ∀ i, 0 ≤ h i (Φ.map (S p.1.1) p.2))
    (hres : 0 ≤ surfaceRemainder K H h (Φ.map 1).symm (Φ.map (S p.1.1) p.2)) :
    (Ω.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E) +
      euclideanExteriorOneForm (fun x => surfaceSecondPrimitive Φ S K H h ρ ρ₀ a b w (τ,x)) p).IsInvertible := by
  obtain ⟨a',b',ha',hb',hea,heb⟩ := exists_smooth_base_germs hU ha hb hp
  have hbase' : 0<fderiv ℝ b' p.1 (1,0)-fderiv ℝ a' p.1 (0,1) := by
    rwa [hea.fderiv_eq,heb.fderiv_eq]
  have hi := surfaceSecondPath_isInvertible hΩ hskew Φ hS hK hH hh hρ hρ₀ ha' hb' hw τ hτ p
    hbase' hwzero hwpos hSpos hHpos hclock hclock₀ hcap hres
  have he : (fun x => surfaceSecondPrimitive Φ S K H h ρ ρ₀ a' b' w (τ,x)) =ᶠ[𝓝 p]
      (fun x => surfaceSecondPrimitive Φ S K H h ρ ρ₀ a b w (τ,x)) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds hea,
      continuousAt_fst.preimage_mem_nhds heb] with y hya hyb
    change a' y.1=a y.1 at hya
    change b' y.1=b y.1 at hyb
    apply ContinuousLinearMap.ext
    intro v
    simp only [surfaceSecondPrimitive,horizontalOneForm_apply,hya,hyb]
  rwa [euclideanExteriorOneForm_congr_germ he] at hi

end

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

 theorem circleWeight_radial_deriv {f : Circle → ℝ}
    (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f) (q : Plane) :
    fderiv ℝ (fun y : Plane => f (circleTurn y.2)) q (1,0)=0 := by
  have ht := ((hf.comp circleTurn_smooth).contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) q.2).hasFDerivAt
  have hd := (ht.comp q (hasFDerivAt_snd (𝕜 := ℝ) (p := q))).fderiv
  change (fderiv ℝ ((f ∘ circleTurn) ∘ Prod.snd) q) (1,0)=0
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',map_zero]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_AnnularPathGerms
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

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
 theorem annular_normalForm_cover
    (D : AnnularHandleData E M)
    (b : ℝ) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) {W : Set M}
    (hN : ∀ v x,x∈W→Γ v x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H v) • D.dual x)
    (v : V) {q : Plane} (hq : q∈D.annularCoverDomain) (hx : D.handleAnnularCover q∈W) :
    Γ v (D.handleAnnularCover q)=γ (D.handleAnnularCover q)+
      (intervalClock (-b) b q.1*H v) • D.dual (D.handleAnnularCover q) := by
  simpa only [D.handleAnnularCover_inverse hq,cylinderCover] using hN v _ hx

 theorem globalSurfaceSecondPrimitive_cover_germ {ι : Type*} [Fintype ι]
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) {W : Set M}
    (hW : IsOpen W)
    (hN : ∀ v x,x∈W→Γ v x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H v) • D.dual x)
    (τ : ℝ) {p : Plane × V} (hp : p.1∈D.annularCoverDomain)
    (hx : D.handleAnnularCover p.1∈W) :
    (fun y => euclideanPullbackOneForm
      (fun _ => productHorizontalLift (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (τ,v)))
      (flatProductMap (D.handleAnnularCover)) (0,y)) =ᶠ[𝓝 p]
    (fun y => surfaceSecondPrimitive Φ (intervalClock (-b) b) K H h ρ ρ₀
      (D.annularCoverA γ) (D.annularCoverB γ) (fun q => D.clock (circleTurn q.2)) (τ,y)) := by
  have hs := (D.annularCoverDomain_open).mem_nhds hp
  have hw := (D.handleAnnularCover_smoothAt hp).continuousAt.preimage_mem_nhds (hW.mem_nhds hx)
  filter_upwards [continuousAt_fst.preimage_mem_nhds hs,
    continuousAt_fst.preimage_mem_nhds hw] with y hy hyW
  exact globalSurfaceSecondPrimitive_cover D b Φ K H h ρ ρ₀ Γ γ τ y hy
    (annular_normalForm_cover D b H Γ γ hN y.2 hy hyW)

end

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_AnnularSecondPositivity
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

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

theorem globalSurfaceSecondPath_isInvertible_annular_bp240_oai {ι : Type*} [Fintype ι]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w,Ω v w= -Ω w v)
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (Φ : CompactHamiltonianIsotopy Ω) {K H : V → ℝ}
    (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    {h : ι → V → ℝ} (hh : ∀ i,ContDiff ℝ ∞ (h i))
    {ρ : ι → ℝ → ℝ} (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (hlo : ∀ s,s ≤ -b →(∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s,b ≤ s →(∀ i,ρ i s=1) ∧ ρ₀ s=1)
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {γ : ManifoldOneForm E M}
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x))
    {W : Set M} (hW : IsOpen W)
    (hN : ∀ v x,x∈W→Γ v x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H v) • D.dual x)
    (τ : ℝ) (hτ : τ∈Icc (0:ℝ) 1) (p : Plane × V) (hp : p.1∈D.annularCoverDomain)
    (hx : D.handleAnnularCover p.1∈W)
    (hbase : 0 < manifoldExteriorOneForm γ (D.handleAnnularCover p.1)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) p.1 (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) p.1 (0,1)))
    (hfp : 0≤D.clock (circleTurn p.1.2))
    (hHp : 0≤H ((Φ.map 1).symm (Φ.map (intervalClock (-b) b p.1.1) p.2)))
    (hclock : ∀ i,0≤deriv (ρ i) p.1.1) (hclock₀ : 0≤deriv ρ₀ p.1.1)
    (hcap : ∀ i,0≤h i (Φ.map (intervalClock (-b) b p.1.1) p.2))
    (hres : 0 ≤ surfaceRemainder K H h (Φ.map 1).symm
      (Φ.map (intervalClock (-b) b p.1.1) p.2)) :
    (globalHorizontalCoupling Ω
      (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (τ,v))
      (D.handleAnnularCover p.1,p.2)).IsInvertible := by
  have hpath := (globalSurfaceSecondPrimitive_smooth D hb hbw Φ hK hH hh hρ hρ₀ hlo hhi hΓ).comp
    (f := fun v : V => (τ,v)) (contDiff_const.prodMk contDiff_id)
  have hc := D.annularCover_coefficients_smooth hγ
  have hcurl : 0<fderiv ℝ (D.annularCoverB γ) p.1 (1,0)-
      fderiv ℝ (D.annularCoverA γ) p.1 (0,1) := by
    rw [D.annularCover_curl hp (hγ _ (D.chart.map_source hp))]
    exact hbase
  have hloc := surfaceSecondPath_isInvertible_local hΩ hskew Φ
    (intervalClock_smooth (-b) b) hK hH hh hρ hρ₀ (D.annularCoverDomain_open) hc.1 hc.2
    (((D.clock_smooth.comp circleTurn_smooth).contDiff).comp contDiff_snd) τ hτ p hp hcurl
    (circleWeight_radial_deriv D.clock_smooth p.1) hfp (intervalClock_deriv_nonneg (by linarith) _) hHp hclock hclock₀ hcap hres
  have hgerm := globalSurfaceSecondPrimitive_cover_germ D b Φ K H h ρ ρ₀ Γ γ hW hN τ hp hx
  have hd := euclideanExteriorOneForm_congr_germ hgerm
  apply globalHorizontalCoupling_isInvertible_coordinates hpath
    (D.handleAnnularCover_smoothAt hp) (D.handleAnnularCoverLinearEquiv hp) (by rfl)
  exact hd.symm ▸ hloc

end

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_annular_bp240_oai.{u_1, u_2, u_3, u_4} := @OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_annular_bp240_oai.{u_1, u_2, u_3, u_4}
