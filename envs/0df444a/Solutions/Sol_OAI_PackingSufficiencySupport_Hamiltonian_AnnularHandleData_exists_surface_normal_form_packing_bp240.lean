-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_normal_form_packing_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:03.885578+00:00
-- url     : https://prove2.me/submissions/5c63ed1c-b9e2-4017-8a07-c2ce2351e6d9

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_exists_global_surface_final_packing_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceFirstPath_moser_endpoint_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceSecondPath_isInvertible_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_horizontal_moser_endpoint_bp240

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

theorem chartOneForm_reconstruct_target {α : ManifoldOneForm E M} {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    (chartOneForm α c y).comp (chartDifferential c ((extChartAt 𝓘(ℝ,E) c).symm y)) =
      α ((extChartAt 𝓘(ℝ,E) c).symm y) := by
  have hC : (chartDifferential (E := E) c ((extChartAt 𝓘(ℝ,E) c).symm y)).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) ((extChartAt 𝓘(ℝ,E) c).map_target hy) using 1
    all_goals try with_reducible_and_instances rfl
  ext v
  exact congrArg (α ((extChartAt 𝓘(ℝ,E) c).symm y)) (hC.inverse_apply_self v)


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

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_NonautonomousManifoldFlow
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

namespace PreservesTwoFormOn
variable {e f : M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ M}
  {Ω₀ Ω₁ Ω₂ : ManifoldTwoForm E M} {D : Set M}

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem symm (he : PreservesTwoFormOn e Ω₀ Ω₁ D) (hD : e '' D = D) :
    PreservesTwoFormOn e.symm Ω₁ Ω₀ D := by
  intro y hy v w
  have hx : e.symm y ∈ D := by
    obtain ⟨x,hx,hxy⟩ := hD.symm ▸ hy
    simpa only [←hxy,e.symm_apply_apply] using hx
  have hd := mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) (e.symm y))
    (e.symm.contMDiff.mdifferentiable (by simp) y)
  have heq : (e : M → M) ∘ e.symm = id := by funext z; exact e.apply_symm_apply z
  rw [heq,mfderiv_id] at hd
  have hv := congrArg (fun L : E →L[ℝ] E => L v) hd.symm
  have hw := congrArg (fun L : E →L[ℝ] E => L w) hd.symm
  have h := he (e.symm y) hx (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm y v)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm y w)
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e (e.symm y) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm y v)=v at hv
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e (e.symm y) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm y w)=w at hw
  rw [hv,hw,e.apply_symm_apply] at h
  exact h.symm

end PreservesTwoFormOn

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem FormNeighborhoodEmbedding.transport
    {K : Set N} {σ : ManifoldTwoForm F N} {Ω₀ Ω₁ : ManifoldTwoForm E M}
    {f : N → M} (hf : FormNeighborhoodEmbedding K σ Ω₁ f)
    {D : Set M} (he : M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ M)
    (hform : PreservesTwoFormOn he Ω₁ Ω₀ D) (himage : MapsTo f K (interior D)) :
    FormNeighborhoodEmbedding K σ Ω₀ (he ∘ f) := by
  obtain ⟨U,hU,hKU,hs,hfemb,hσ⟩ := hf
  let W := U ∩ f ⁻¹' interior D
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage hU isOpen_interior
  have hWU : W ⊆ U := inter_subset_left
  refine ⟨W,hW,fun x hx => ⟨hKU hx,himage hx⟩,
    he.contMDiff.comp_contMDiffOn (hs.mono hWU),?_,?_⟩
  · exact he.toHomeomorph.isEmbedding.comp (hfemb.comp (Topology.IsEmbedding.inclusion hWU))
  · intro x hx v w
    have hd := mfderiv_comp x (he.contMDiff.mdifferentiable (by simp) (f x))
      ((hs.contMDiffAt (hU.mem_nhds hx.1)).mdifferentiableAt (by simp))
    rw [hd]
    exact (hform (f x) (interior_subset hx.2) _ _).trans (hσ x hx.1 v w)

theorem transport_form_packing {ι : Type*} (K : ι → Set N)
    (σ : ManifoldTwoForm F N) (Ω₀ Ω₁ : ManifoldTwoForm E M) {D : Set M}
    (e : M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ M)
    (hform : PreservesTwoFormOn e Ω₀ Ω₁ D)
    (hD : e '' D=D) (hInt : e '' interior D=interior D)
    (f : ι → N → M) (hf : ∀ i, FormNeighborhoodEmbedding (K i) σ Ω₁ (f i))
    (himage : ∀ i, MapsTo (f i) (K i) (interior D))
    (hdis : Pairwise (fun i j => Disjoint (f i '' K i) (f j '' K j))) :
    (∀ i, FormNeighborhoodEmbedding (K i) σ Ω₀ (e.symm ∘ f i)) ∧
    (∀ i, MapsTo (e.symm ∘ f i) (K i) (interior D)) ∧
    Pairwise (fun i j => Disjoint ((e.symm ∘ f i) '' K i) ((e.symm ∘ f j) '' K j)) := by
  refine ⟨fun i => (hf i).transport e.symm (hform.symm hD) (himage i),?_,?_⟩
  · intro i x hx
    obtain ⟨y,hy,hyx⟩ := hInt.symm ▸ himage i hx
    simpa only [Function.comp_apply,←hyx,e.symm_apply_apply] using hy
  · intro i j hij
    rw [Set.image_comp,Set.image_comp]
    exact (hdis hij).image (e.symm.injective.injOn (s := Set.univ)) (subset_univ _) (subset_univ _)

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_AnnularFinalPacking
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy.concatMap_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem SmoothOneFormFamily.parameter_contDiffAt {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (v : V) (x : M) : ContDiffAt ℝ ∞ (fun w => Γ w x) v := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have hxt := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hcam := ((hΓ x).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x)).mem_nhds
      (show (v,extChartAt 𝓘(ℝ,E) x x)∈univ ×ˢ (extChartAt 𝓘(ℝ,E) x).target from ⟨mem_univ v,hxt⟩))).comp v
        (contDiffAt_id.prodMk contDiffAt_const)
  have hsm := hcam.clm_comp (contDiffAt_const (c := chartDifferential x x))
  apply hsm.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun w => by
    simpa only [(extChartAt 𝓘(ℝ,E) x).left_inv hx,Function.comp_def,id_eq] using
      (chartOneForm_reconstruct_target (α := Γ w) hxt).symm)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport
open Set

theorem constant_above_of_deriv_eq_zero {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {a t₀ : ℝ} (hzero : ∀ t, a < f t → deriv f t = 0) (h₀ : a < f t₀) :
    ∀ t, f t = f t₀ := by
  let s : Set ℝ := {t | f t = f t₀}
  have hclosed : IsClosed s := isClosed_eq hf.continuous continuous_const
  have hopen : IsOpen s := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hft : a < f t := by rw [ht]; exact h₀
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_lt continuous_const hf.continuous).mem_nhds hft)
    apply Filter.mem_of_superset (Metric.ball_mem_nhds t hr)
    intro u hu
    have he := Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball t r).isPreconnected hf.differentiableOn
      (fun {v} hv => hzero v (hball hv)) hu (Metric.mem_ball_self hr)
    exact he.trans ht
  have hs : s = univ := (show IsClopen s from ⟨hclosed,hopen⟩).eq_univ ⟨t₀,rfl⟩
  intro t
  have ht : t ∈ s := hs.symm ▸ mem_univ t
  exact ht

end PackingSufficiencySupport

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open scoped BigOperators
open scoped Manifold
open Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : E →L[ℝ] E →L[ℝ] ℝ}
namespace CompactHamiltonianIsotopy

theorem integral_constant_on_collar (Φ : CompactHamiltonianIsotopy A)
    {f : E → ℝ} (hf : Differentiable ℝ f) {a : ℝ}
    (hzero : ∀ t x, a < f x →
      fderiv ℝ f x (hamiltonianField A Φ.hamiltonian (t,x)) = 0)
    (x : E) {s : ℝ} (hs : a < f (Φ.map s x)) (t : ℝ) :
    f (Φ.map t x) = f (Φ.map s x) := by
  have hd (u : ℝ) := (hf (Φ.map u x)).hasFDerivAt.comp_hasDerivAt u (Φ.flow u x)
  exact constant_above_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u hu => (hd u).deriv.trans (hzero u (Φ.map u x) hu)) hs t

theorem preserves_integral_on_collar (Φ : CompactHamiltonianIsotopy A)
    {f : E → ℝ} (hf : Differentiable ℝ f) {a : ℝ}
    (hzero : ∀ t x, a < f x →
      fderiv ℝ f x (hamiltonianField A Φ.hamiltonian (t,x)) = 0)
    {x : E} (hx : a < f x) (t : ℝ) : f (Φ.map t x) = f x := by
  simpa only [Φ.zero,Homeomorph.refl_apply,id_eq] using
    Φ.integral_constant_on_collar hf hzero x (s := 0)
      (by simpa only [Φ.zero,Homeomorph.refl_apply,id_eq] using hx) t

theorem inverse_preserves_integral_on_collar (Φ : CompactHamiltonianIsotopy A)
    {f : E → ℝ} (hf : Differentiable ℝ f) {a : ℝ}
    (hzero : ∀ t x, a < f x →
      fderiv ℝ f x (hamiltonianField A Φ.hamiltonian (t,x)) = 0)
    {x : E} (hx : a < f x) (t : ℝ) : f ((Φ.map t).symm x) = f x := by
  simpa only [Φ.zero,Homeomorph.refl_apply,id_eq,Homeomorph.apply_symm_apply] using
    Φ.integral_constant_on_collar hf hzero ((Φ.map t).symm x) (s := t)
      (by simpa only [Homeomorph.apply_symm_apply] using hx) 0

end CompactHamiltonianIsotopy

theorem autonomousField_contraction (hA : A.IsInvertible) {f : E → ℝ}
    (hf : Differentiable ℝ f) (x v : E) :
    A (autonomousField A f x) v = -fderiv ℝ f x v := by
  rw [autonomousField,hamiltonianField_contraction hA]
  have hd := (hf x).hasFDerivAt.comp (0,x) (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt
  change HasFDerivAt (fun p : ℝ × E => f p.2) _ _ at hd
  change -fderiv ℝ (fun p : ℝ × E => f p.2) (0,x) (0,v) = _
  rw [hd.fderiv]
  rfl

theorem intertwines_autonomousField (hA : A.IsInvertible)
    (q : E ≃ₜ E) (hq : ContDiff ℝ ∞ q) (hqi : ContDiff ℝ ∞ q.symm)
    (hsymp : ∀ x v w, A (fderiv ℝ q x v) (fderiv ℝ q x w) = A v w)
    {f : E → ℝ} (hf : Differentiable ℝ f) (x : E)
    (hpres : (fun y => f (q y)) =ᶠ[𝓝 x] f) :
    fderiv ℝ q x (autonomousField A f x) = autonomousField A f (q x) := by
  have hinj : Injective A := by
    obtain ⟨e,he⟩ := hA
    rw [← he]
    exact e.injective
  apply hinj
  ext w
  let w' := fderiv ℝ q.symm (q x) w
  have hsurj : fderiv ℝ q x w' = w := by
    have he := ((hq.differentiable (by simp) (q.symm (q x))).hasFDerivAt.comp (q x)
      (hqi.differentiable (by simp) (q x)).hasFDerivAt)
    simp only [Homeomorph.symm_apply_apply] at he
    have he' : HasFDerivAt (fun y => q (q.symm y))
        ((fderiv ℝ q x).comp (fderiv ℝ q.symm (q x))) (q x) := he
    have hid : (fun y => q (q.symm y)) = id := by ext y; simp
    rw [hid] at he'
    have hw := congrArg (fun T : E →L[ℝ] E => T w)
      (he'.unique (hasFDerivAt_id (q x)))
    exact hw
  rw [← hsurj,hsymp,autonomousField_contraction hA hf,
    autonomousField_contraction hA hf]
  congr 1
  have hd := (hf (q x)).hasFDerivAt.comp x (hq.differentiable (by simp) x).hasFDerivAt
  have he : (fderiv ℝ f (q x)).comp (fderiv ℝ q x) = fderiv ℝ f x :=
    hd.fderiv.symm.trans hpres.fderiv_eq
  exact (congrArg (fun T : E →L[ℝ] ℝ => T w') he).symm

theorem homeomorph_fderiv_inverse (q : E ≃ₜ E)
    (hq : Differentiable ℝ q) (hqi : Differentiable ℝ q.symm) (x v : E) :
    fderiv ℝ q.symm (q x) (fderiv ℝ q x v) = v := by
  have hd := (hqi (q x)).hasFDerivAt.comp x (hq x).hasFDerivAt
  have he : (q.symm : E → E) ∘ q = id := by ext y; simp
  rw [he] at hd
  exact congrArg (fun T : E →L[ℝ] E => T v) (hd.unique (hasFDerivAt_id x))

namespace CompactHamiltonianIsotopy

theorem inverse_symplectic (Φ : CompactHamiltonianIsotopy A) (t : ℝ) (x v w : E) :
    A (fderiv ℝ (Φ.map t).symm x v) (fderiv ℝ (Φ.map t).symm x w) = A v w := by
  have hv := homeomorph_fderiv_inverse (Φ.map t).symm
    ((Φ.map_inverse_smooth t).differentiable (by simp))
    ((Φ.map_smooth t).differentiable (by simp)) x v
  have hw := homeomorph_fderiv_inverse (Φ.map t).symm
    ((Φ.map_inverse_smooth t).differentiable (by simp))
    ((Φ.map_smooth t).differentiable (by simp)) x w
  have hs := Φ.symplectic t ((Φ.map t).symm x)
    (fderiv ℝ (Φ.map t).symm x v) (fderiv ℝ (Φ.map t).symm x w)
  simp only [Homeomorph.symm_symm] at hv hw
  rw [hv,hw] at hs
  exact hs.symm

theorem intertwines_on_collar (Φ : CompactHamiltonianIsotopy A) (hA : A.IsInvertible)
    {f : E → ℝ} (hf : Differentiable ℝ f) {a : ℝ}
    (hzero : ∀ t x, a < f x →
      fderiv ℝ f x (hamiltonianField A Φ.hamiltonian (t,x)) = 0)
    {x : E} (hx : a < f x) (t : ℝ) :
    fderiv ℝ (Φ.map t) x (autonomousField A f x) = autonomousField A f (Φ.map t x) := by
  apply intertwines_autonomousField hA (Φ.map t) (Φ.map_smooth t) (Φ.map_inverse_smooth t)
    (Φ.symplectic t) hf x
  filter_upwards [(isOpen_lt continuous_const hf.continuous).mem_nhds hx] with y hy
  exact Φ.preserves_integral_on_collar hf hzero hy t

theorem inverse_intertwines_on_collar (Φ : CompactHamiltonianIsotopy A) (hA : A.IsInvertible)
    {f : E → ℝ} (hf : Differentiable ℝ f) {a : ℝ}
    (hzero : ∀ t x, a < f x →
      fderiv ℝ f x (hamiltonianField A Φ.hamiltonian (t,x)) = 0)
    {x : E} (hx : a < f x) (t : ℝ) :
    fderiv ℝ (Φ.map t).symm x (autonomousField A f x) = autonomousField A f ((Φ.map t).symm x) := by
  apply intertwines_autonomousField hA (Φ.map t).symm (Φ.map_inverse_smooth t) (Φ.map_smooth t)
    (Φ.inverse_symplectic t) hf x
  filter_upwards [(isOpen_lt continuous_const hf.continuous).mem_nhds hx] with y hy
  exact Φ.inverse_preserves_integral_on_collar hf hzero hy t

end CompactHamiltonianIsotopy

theorem hamiltonian_invariant_of_commutes (hA : A.IsInvertible)
    (hskew : ∀ v w, A v w = -A w v) (H : ℝ × E → ℝ)
    {f : E → ℝ} (hf : Differentiable ℝ f) (t : ℝ) (x : E)
    (hzero : fderiv ℝ f x (hamiltonianField A H (t,x)) = 0) :
    fderiv ℝ H (t,x) (0,autonomousField A f x) = 0 := by
  have hh := hamiltonianField_contraction hA H (t,x) (autonomousField A f x)
  rw [hskew,autonomousField_contraction hA hf,hzero] at hh
  linarith

end
section

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {μ : V → ℝ} {a : ℝ}

 theorem CollarInvariant.const (w : W) : CollarInvariant Ω μ a (fun _ => w) := by
  refine ⟨contDiff_const,fun v _ => ?_⟩
  simp

 theorem CollarInvariant.add {f g : V → W} (hf : CollarInvariant Ω μ a f)
    (hg : CollarInvariant Ω μ a g) : CollarInvariant Ω μ a (fun v => f v+g v) := by
  refine ⟨hf.1.add hg.1,fun v hv => ?_⟩
  change fderiv ℝ (f+g) v (autonomousField Ω μ v)=0
  rw [fderiv_add (hf.1.differentiable (by simp) v) (hg.1.differentiable (by simp) v)]
  simp [hf.2 v hv,hg.2 v hv]

 theorem CollarInvariant.sub {f g : V → W} (hf : CollarInvariant Ω μ a f)
    (hg : CollarInvariant Ω μ a g) : CollarInvariant Ω μ a (fun v => f v-g v) := by
  refine ⟨hf.1.sub hg.1,fun v hv => ?_⟩
  change fderiv ℝ (f-g) v (autonomousField Ω μ v)=0
  rw [fderiv_sub (hf.1.differentiable (by simp) v) (hg.1.differentiable (by simp) v)]
  simp [hf.2 v hv,hg.2 v hv]

 theorem CollarInvariant.smul {f : V → ℝ} {g : V → W} (hf : CollarInvariant Ω μ a f)
    (hg : CollarInvariant Ω μ a g) : CollarInvariant Ω μ a (fun v => f v • g v) := by
  refine ⟨hf.1.smul hg.1,fun v hv => ?_⟩
  change fderiv ℝ (f • g) v (autonomousField Ω μ v)=0
  rw [((hf.1.differentiable (by simp) v).hasFDerivAt.smul
    (hg.1.differentiable (by simp) v).hasFDerivAt).fderiv]
  simp [hf.2 v hv,hg.2 v hv]

 theorem CollarInvariant.const_mul {f : V → ℝ} (hf : CollarInvariant Ω μ a f) (b : ℝ) :
    CollarInvariant Ω μ a (fun v => b*f v) := (CollarInvariant.const b).smul hf

 theorem CollarInvariant.sum {ι : Type*} (s : Finset ι) {f : ι → V → W}
    (hf : ∀ i∈s,CollarInvariant Ω μ a (f i)) :
    CollarInvariant Ω μ a (fun v => ∑ i∈s,f i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CollarInvariant.const (Ω := Ω) (μ := μ) (a := a) (0:W))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

 theorem CollarInvariant.pullback {f : V → W} (hf : CollarInvariant Ω μ a f)
    (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,a<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0) (t : ℝ) :
    CollarInvariant Ω μ a (f ∘ Φ.map t) := by
  refine ⟨hf.1.comp (Φ.map_smooth t),fun v hv => ?_⟩
  rw [fderiv_comp v (hf.1.differentiable (by simp) _) ((Φ.map_smooth t).differentiable (by simp) _),
    ContinuousLinearMap.comp_apply,Φ.intertwines_on_collar hΩ hμ hzero hv t]
  apply hf.2
  rwa [Φ.preserves_integral_on_collar hμ hzero hv t]

 theorem CollarInvariant.inverse_pullback {f : V → W} (hf : CollarInvariant Ω μ a f)
    (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,a<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0) (t : ℝ) :
    CollarInvariant Ω μ a (f ∘ (Φ.map t).symm) := by
  refine ⟨hf.1.comp (Φ.map_inverse_smooth t),fun v hv => ?_⟩
  rw [fderiv_comp v (hf.1.differentiable (by simp) _) ((Φ.map_inverse_smooth t).differentiable (by simp) _),
    ContinuousLinearMap.comp_apply,Φ.inverse_intertwines_on_collar hΩ hμ hzero hv t]
  apply hf.2
  rwa [Φ.inverse_preserves_integral_on_collar hμ hzero hv t]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
 theorem CompactHamiltonianIsotopy.hamiltonian_collarInvariant
    (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hs : ∀ u v,Ω u v= -Ω v u) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,a<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0) (t : ℝ) :
    CollarInvariant Ω μ a (fun v => Φ.hamiltonian (t,v)) := by
  refine ⟨Φ.hamiltonian_smooth.comp (contDiff_const.prodMk contDiff_id),fun v hv => ?_⟩
  have hd := (Φ.hamiltonian_smooth.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (t,v)).hasFDerivAt.comp v
    ((hasFDerivAt_const t v).prodMk (hasFDerivAt_id v))
  change fderiv ℝ (Φ.hamiltonian ∘ Prod.mk t) v (autonomousField Ω μ v)=0
  rw [hd.fderiv]
  exact hamiltonian_invariant_of_commutes hΩ hs Φ.hamiltonian hμ t v (hzero t v hv)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
 theorem toric_collarInvariant {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    {G : (ι → ℝ) → W} (hG : ContDiff ℝ ∞ G) (a : ℝ) :
    CollarInvariant phaseArea (F ∘ planeMoments) a (G ∘ planeMoments) := by
  refine ⟨hG.comp planeMoments_smooth,fun v _ => ?_⟩
  rw [fderiv_comp v (hG.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (planeMoments_smooth.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _),
    ContinuousLinearMap.comp_apply]
  have he : autonomousField phaseArea (F ∘ planeMoments) v=
      hamiltonianField phaseArea (toricHamiltonian F) (0,v) := rfl
  rw [he,toricHamiltonian_preserves_moments hF (0,v),map_zero]

end

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
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {μ : V → ℝ} {c : ℝ}

 theorem surfaceSuspensionCoefficient_collarInvariant
    (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hs : ∀ u v,Ω u v= -Ω v u) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,c<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0)
    (S : ℝ → ℝ) (t s : ℝ) :
    CollarInvariant Ω μ c (fun v => surfaceSuspensionCoefficient Φ S ((t,v),s)) :=
  ((Φ.hamiltonian_collarInvariant hΩ hs hμ hzero (t*S s)).pullback
    Φ hΩ hμ hzero (t*S s)).const_mul t

 theorem surfaceFirstCorrectionCoefficient_collarInvariant
    (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,c<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0)
    {H : V → ℝ} (hH : CollarInvariant Ω μ c H) (S : ℝ → ℝ) (t s : ℝ) :
    CollarInvariant Ω μ c (fun v => surfaceFirstCorrectionCoefficient Φ S H ((t,v),s)) :=
  (((hH.inverse_pullback Φ hΩ hμ hzero t).pullback Φ hΩ hμ hzero (t*S s)).sub hH).const_mul (S s)

variable {κ : Type*} [Fintype κ]
 theorem surfaceSecondExtraCoefficient_collarInvariant
    (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,c<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0)
    {K H : V → ℝ} (hK : CollarInvariant Ω μ c K) (hH : CollarInvariant Ω μ c H)
    {h : κ → V → ℝ} (hh : ∀ i,CollarInvariant Ω μ c (h i))
    (S : ℝ → ℝ) (ρ : κ → ℝ → ℝ) (ρ₀ : ℝ → ℝ) (t s : ℝ) :
    CollarInvariant Ω μ c (fun v => surfaceSecondExtraCoefficient Φ S K H h ρ ρ₀ ((t,v),s)) := by
  have hr : CollarInvariant Ω μ c (surfaceRemainder K H h (Φ.map 1).symm) :=
    (((hK.inverse_pullback Φ hΩ hμ hzero 1).sub hK).add hH).sub
      (CollarInvariant.sum Finset.univ (fun i _ => hh i))
  have hf : CollarInvariant Ω μ c (fun v => surfaceFinalLayer (K-H) h
      (surfaceRemainder K H h (Φ.map 1).symm) ρ ρ₀ (s,v)) :=
    ((hK.sub hH).add (CollarInvariant.sum Finset.univ
      (fun i _ => (hh i).const_mul (ρ i s)))).add (hr.const_mul (ρ₀ s))
  have hfirst : CollarInvariant Ω μ c (fun v => surfaceFirstLayer S H (Φ.map 1).symm (s,v)) :=
    (hH.inverse_pullback Φ hΩ hμ hzero 1).const_mul (S s)
  have hi : CollarInvariant Ω μ c (fun v => surfaceInterpolatedLayer S K H h
      (Φ.map 1).symm ρ ρ₀ t (s,v)) :=
    (hfirst.const_mul (1-t)).add (hf.const_mul t)
  exact (((hi.pullback Φ hΩ hμ hzero (S s)).sub (hH.const_mul (S s))).sub
    ((hK.sub hH).const_mul t)).sub
    (surfaceFirstCorrectionCoefficient_collarInvariant Φ hΩ hμ hzero hH S 1 s)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {μ : V → ℝ} {c : ℝ}

variable {κ : Type*} [Fintype κ]
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 theorem globalSurfaceFirstPrimitive_collarInvariant
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hs : ∀ u v,Ω u v= -Ω v u) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,c<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0)
    {H : V → ℝ} (hH : CollarInvariant Ω μ c H) {Γ : V → ManifoldOneForm E M}
    (hΓ : ∀ x,CollarInvariant Ω μ c (fun v => Γ v x)) (t : ℝ) (x : M) :
    CollarInvariant Ω μ c (fun v => globalSurfaceFirstPrimitive D b Φ H Γ (t,v) x) := by
  by_cases hx : x∈D.chart.target
  · simpa only [globalSurfaceFirstPrimitive,Pi.add_apply,extendManifoldOneForm_inside hx,
      handleFirstCorrection] using
      (hΓ x).add (((surfaceSuspensionCoefficient_collarInvariant Φ hΩ hs hμ hzero
        (intervalClock (-b) b) t (D.chart.symm x).1).smul
          (CollarInvariant.const (D.radial b x))).add
        ((surfaceFirstCorrectionCoefficient_collarInvariant Φ hΩ hμ hzero hH
          (intervalClock (-b) b) t (D.chart.symm x).1).smul
            (CollarInvariant.const (D.dual x))))
  · simpa only [globalSurfaceFirstPrimitive,Pi.add_apply,extendManifoldOneForm_outside hx,add_zero]
      using hΓ x

 theorem globalSurfaceSecondPrimitive_collarInvariant
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hs : ∀ u v,Ω u v= -Ω v u) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,c<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0)
    {K H : V → ℝ} (hK : CollarInvariant Ω μ c K) (hH : CollarInvariant Ω μ c H)
    {h : κ → V → ℝ} (hh : ∀ i,CollarInvariant Ω μ c (h i))
    (ρ : κ → ℝ → ℝ) (ρ₀ : ℝ → ℝ) {Γ : V → ManifoldOneForm E M}
    (hΓ : ∀ x,CollarInvariant Ω μ c (fun v => Γ v x)) (t : ℝ) (x : M) :
    CollarInvariant Ω μ c (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (t,v) x) := by
  have hfirst := globalSurfaceFirstPrimitive_collarInvariant D b Φ hΩ hs hμ hzero hH hΓ 1 x
  have hbg := hfirst.add (((hK.sub hH).const_mul t).smul
    (CollarInvariant.const (D.dual x)))
  by_cases hx : x∈D.chart.target
  · simpa only [globalSurfaceSecondPrimitive,Pi.add_apply,Pi.smul_apply,
      extendManifoldOneForm_inside hx,handleSecondExtra] using
      hbg.add ((surfaceSecondExtraCoefficient_collarInvariant Φ hΩ hμ hzero hK hH hh
        (intervalClock (-b) b) ρ ρ₀ t (D.chart.symm x).1).smul
          (CollarInvariant.const (D.dual x)))
  · simpa only [globalSurfaceSecondPrimitive,Pi.add_apply,Pi.smul_apply,
      extendManifoldOneForm_outside hx,add_zero] using hbg

end

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

 theorem globalSurfaceSecondPath_moser_endpoint {κ : Type*} [Fintype κ]
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
    {Kbase : Set M} (heD : D.chart.target⊆interior Kbase) (hβD : tsupport D.dual⊆interior Kbase)
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
    {J : Type*} (F : J → (ι → ℝ) → ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j,α j < c j)
    (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v ≤ c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    (hzero : ∀ j t v,α j<(F j ∘ planeMoments) v→
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t,v))=0)
    (hhInv : ∀ j i,CollarInvariant phaseArea (F j ∘ planeMoments) (α j) (h i)) :
    ∃ ψ : (M × PlanePhase ι) ≃ₘ⟮𝓘(ℝ,Plane × PlanePhase ι),𝓘(ℝ,Plane × PlanePhase ι)⟯ (M × PlanePhase ι),
      ψ '' (Kbase ×ˢ (planeMoments ⁻¹' Y))=Kbase ×ˢ (planeMoments ⁻¹' Y) ∧
      ψ '' interior (Kbase ×ˢ (planeMoments ⁻¹' Y))=interior (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
      PreservesTwoFormOn ψ
        (globalHorizontalCoupling phaseArea (fun v =>
          globalSurfaceFirstPrimitive D b Φ (H ∘ planeMoments) (Γ ∘ planeMoments) (1,v)))
        (globalHorizontalCoupling phaseArea (fun v =>
          globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments) h ρ ρ₀
            (Γ ∘ planeMoments) (1,v)))
        (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
      (∃ C : Set (M × PlanePhase ι),IsCompact C ∧ ∀ z,z∉C→ψ z=z) ∧
      (∀ z,z.1∉(D.chart '' band b) ∪ tsupport (D.dual)→ψ z=z) := by
  have hSD : (D.chart '' band b) ∪ tsupport D.dual⊆interior Kbase :=
    union_subset ((D.image_band_subset_target hbw).trans heD) hβD
  have hparam : ∀ x,ContDiff ℝ ∞ (fun p => Γ p x) :=
    fun x => contDiff_iff_contDiffAt.mpr (fun p => hΓ.parameter_contDiffAt p x)
  obtain ⟨ψ,hD,hI,hp,hC,hfix⟩ := horizontal_moser_endpoint_bp240 phaseArea_isInvertible phaseArea_skew
    (globalSurfaceSecondPrimitive_smooth D hb hbw Φ
      (hK.comp planeMoments_smooth) (hH.comp planeMoments_smooth) hh hρ hρ₀ hlo hhi
      (hΓ.comp planeMoments_smooth))
    ((D.image_band_compact hbw).union D.dual_compact) hSD
    (fun x hx t v => by
      have hb' : x∉D.chart '' band b := fun h => hx (Or.inl h)
      have hf' : D.dual x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
      rw [globalSurfaceSecondPrimitive_off_band D hb Φ _ _ h ρ ρ₀ hlo hhi _ (t,v) hb',
        globalSurfaceSecondPrimitive_off_band D hb Φ _ _ h ρ ρ₀ hlo hhi _ (0,v) hb',hf']
      simp)
    (fun j => F j ∘ planeMoments) (fun j => (hF j).comp planeMoments_smooth)
    α c hαc (hYeq ▸ hYC)
    (fun j t x => globalSurfaceSecondPrimitive_collarInvariant D b Φ phaseArea_isInvertible
      phaseArea_skew (((hF j).comp planeMoments_smooth).differentiable (by simp)) (hzero j)
      (toric_collarInvariant (hF j) hK (α j)) (toric_collarInvariant (hF j) hH (α j))
      (hhInv j) ρ ρ₀ (fun x => toric_collarInvariant (hF j) (hparam x) (α j)) t x)
    (fun t ht z hz => globalSurfaceSecondPath_isInvertible_bp240 D hb hbw hor hΛ hsΛ hpΛ
      hr hγ hdγ hΓ hK hH hHp hbase hW hBW hWA hN Φ hΦ hh hρ hρ₀ hlo hhi hclock hclock₀
      hcap hres ht (by simpa only [hYeq] using hz))
  refine ⟨ψ,?_,?_,?_,hC,hfix⟩
  · simpa only [←hYeq] using hD
  · simpa only [←hYeq] using hI
  · simpa only [←hYeq,globalSurfaceSecondPrimitive_zero] using hp

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_AnnularDensityMass
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

 theorem exists_surface_normal_form_packing_bp240_oai {m N : ℕ}
    (D : AnnularHandleData Plane M)
    {b δ : ℝ} (hb : 0<b) (hbw : b<D.width) (hδ : 0<δ) (hsmall : δ<1/2)
    (hor : PositivePartialChart D.densityChart)
    (hclock : D.clock=positiveCircleClock δ)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0 < chartTwoForm Λ c y (1,0) (0,1))
    {γ : ManifoldOneForm Plane M} {ε : ℝ} (hε : 0<ε)
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x))
    (hdγ : ∀ x∈D.chart.target,manifoldExteriorOneForm γ x=ε • Λ x)
    {Γ : (Fin m  →  ℝ)  →  ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    {K H : (Fin m  →  ℝ)  →  ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    {Y V : Set (Fin m  →  ℝ)} (hHp : ∀ p∈Y,0≤H p)
    {Kbase : Set M} (heD : D.chart.target⊆interior Kbase) (hβD : tsupport D.dual⊆interior Kbase)
    (hΓpos : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
    (hWA : W⊆D.chart.target)
    (hN : ∀ p x,x∈W → Γ p x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (hV : IsOpen (planeMoments ⁻¹' V)) (hVY : V⊆Y)
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    (h : Fin N  →  (Fin m  →  ℝ)  →  ℝ) (hh : ∀ i,ContDiff ℝ ∞ (h i))
    (hhp : ∀ i p,p∈Y → 0≤h i p)
    (hres : ∀ v,planeMoments v∈Y → 0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments)
      (fun j => h j ∘ planeMoments) (Φ.map 1).symm v)
    (r r' : Fin N  →  ℝ) (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
    (hsimplex : ∀ i,∀ p : Fin m  →  ℝ,(∀ j,0≤p j) → (∑ j,p j) ≤ r' i → p∈V)
    (hheight : ∀ i,∀ p : Fin m  →  ℝ,(∀ j,0≤p j) → p∈V → r i-(∑ j,p j)≤h i p)
    {J : Type*} (F : J  →  (Fin m  →  ℝ)  →  ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
    (α c : J  →  ℝ) (hαc : ∀ j,α j < c j)
    (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v ≤ c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    (hzero : ∀ j t v,α j<(F j ∘ planeMoments) v →
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t,v))=0) :
    ∃ φ : Fin N  →  Ambient (m+1)  →  M × PlanePhase (Fin m),
      (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
        (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments)) (φ i)) ∧
      (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ×ˢ (planeMoments ⁻¹' Y)))) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  have hbase : D.chart '' band b⊆interior Kbase :=
    (D.image_band_subset_target hbw).trans heD
  obtain ⟨ρ,hρ,hρpos,hlo,hhi,φ,hφ,him,hdis⟩ := exists_global_surface_final_packing_bp240 D hb hbw hδ hsmall
    hor hclock hΛ hsΛ hpΛ hε hγ hdγ hΓ hK hH hbase hW hBW hN Φ hV hVY hΦ h hh
    (fun i p hp => hhp i p (hVY hp)) r r' hr' hrr hsimplex hheight
  obtain ⟨ψ₂,hD₂,hI₂,hform₂,_,_⟩ := globalSurfaceSecondPath_moser_endpoint D hb hbw hor
    hΛ hsΛ hpΛ hε hγ hdγ hΓ hK hH hHp heD hβD hΓpos hW hBW hWA hN Φ hΦ
    (fun i => (hh i).comp planeMoments_smooth) (fun i => hρ i.castSucc) (hρ (Fin.last N))
    (fun s hs => ⟨fun i => hlo s hs i.castSucc,hlo s hs _⟩)
    (fun s hs => ⟨fun i => hhi s hs i.castSucc,hhi s hs _⟩)
    (fun i => hρpos i.castSucc) (hρpos (Fin.last N)) (fun v hv i => hhp i _ hv) hres
    F hF α c hαc hYeq hYC hzero (fun j i => toric_collarInvariant (hF j) (hh i) (α j))
  obtain ⟨hφ₁,him₁,hd₁⟩ := transport_form_packing (fun i => closedBall (m+1) (r' i))
    (fun _ => successorStandardForm m) _ _ ψ₂ hform₂ hD₂ hI₂ φ hφ him hdis
  obtain ⟨ψ₁,hD₁,hI₁,hform₁,_,_⟩ := globalSurfaceFirstPath_moser_endpoint_bp240 D hb hbw hor
    hΛ hsΛ hpΛ hε hγ hdγ hΓ hH hHp heD hΓpos hW hBW hWA hN Φ hΦ F hF α c hαc hYeq hYC hzero
  obtain ⟨hφ₀,him₀,hd₀⟩ := transport_form_packing (fun i => closedBall (m+1) (r' i))
    (fun _ => successorStandardForm m) _ _ ψ₁ hform₁ hD₁ hI₁ (fun i => ψ₂.symm ∘ φ i) hφ₁ him₁ hd₁
  exact ⟨fun i => ψ₁.symm ∘ (ψ₂.symm ∘ φ i),hφ₀,him₀,hd₀⟩

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_normal_form_packing_bp240_oai.{u_1, u_2} := @OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_normal_form_packing_bp240_oai.{u_1, u_2}
