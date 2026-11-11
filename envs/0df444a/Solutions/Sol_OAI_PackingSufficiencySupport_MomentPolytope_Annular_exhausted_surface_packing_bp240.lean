-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:21.582682+00:00
-- url     : https://prove2.me/submissions/90ea4c44-fa1f-4951-b69c-13003e563b2d

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_exists_surface_normal_form_packing_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_exists_surface_step_two_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_horizontal_moser_endpoint_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_MomentPolytope_finite_surface_comparison_bp240

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

open scoped ContDiff Manifold Topology
open Set Function Manifold



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
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
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

 theorem compactSurfacePartition_subordinate {D : Set M} (hD : IsCompact D) :
    (compactSurfacePartition hD).IsSubordinate
      (fun B : compactSurfaceBoxes hD => B.1.carrier) :=
  Classical.choose_spec (Classical.choose_spec (SurfaceCoordinateBox.finite_partition hD))

end

end PackingSufficiencySupport.Hamiltonian

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
open scoped ContDiff Manifold Topology ENNReal NNReal
open Set Function Manifold MeasureTheory
section

 theorem planar_curve_image_null {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ × ℝ}
    (hf : ContDiffOn ℝ 1 f s) : volume (f '' s)=0 := by
  have hd : dimH (f '' s)≤dimH s := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro x hx
    obtain ⟨C,t,ht,hC⟩ := ((hf x hx).contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  have hb : dimH s≤1 := by
    calc
      dimH s≤dimH (Set.univ : Set ℝ) := dimH_mono (subset_univ _)
      _=1 := by simp only [Real.dimH_univ_eq_finrank,Module.finrank_self,Nat.cast_one]
  have hz := hausdorffMeasure_of_dimH_lt (d := (2:ℝ≥0)) ((hd.trans hb).trans_lt (by norm_num))
  simpa only [NNReal.coe_ofNat,hausdorffMeasure_prod_real] using hz

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × ℝ) M]
  [IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M]

 theorem smooth_curve_chart_null (c : M) {s : Set ℝ} (hs : IsOpen s) {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ × ℝ) ∞ γ s) :
    volume ((extChartAt 𝓘(ℝ,ℝ × ℝ) c).target ∩
      (extChartAt 𝓘(ℝ,ℝ × ℝ) c).symm ⁻¹' (γ '' s))=0 := by
  let U := s ∩ γ ⁻¹' (extChartAt 𝓘(ℝ,ℝ × ℝ) c).source
  have hU : IsOpen U := hγ.continuousOn.isOpen_inter_preimage hs (isOpen_extChartAt_source c)
  have hf : ContDiffOn ℝ 1 (extChartAt 𝓘(ℝ,ℝ × ℝ) c ∘ γ) U := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    have hc : ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℝ × ℝ) ∞ (extChartAt 𝓘(ℝ,ℝ × ℝ) c) (γ x) :=
      contMDiffAt_extChartAt' (by simpa only [extChartAt_source,mem_preimage] using hx.2)
    exact (hc.comp x ((hγ x hx.1).contMDiffAt (hs.mem_nhds hx.1))).contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  apply measure_mono_null _ (planar_curve_image_null hU hf)
  rintro y ⟨hy,t,ht,he⟩
  refine ⟨t,⟨ht,?_⟩,?_⟩
  · change γ t∈(extChartAt 𝓘(ℝ,ℝ × ℝ) c).source
    rw [he]
    exact (extChartAt 𝓘(ℝ,ℝ × ℝ) c).map_target hy
  · change extChartAt 𝓘(ℝ,ℝ × ℝ) c (γ t)=y
    rw [he,(extChartAt 𝓘(ℝ,ℝ × ℝ) c).right_inv hy]

 theorem countable_smooth_curve_cover_chart_null {J : Type*} [Countable J]
    (c : M) (s : J → Set ℝ) (γ : J → ℝ → M) (hs : ∀ i,IsOpen (s i))
    (hγ : ∀ i,ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ × ℝ) ∞ (γ i) (s i))
    {C : Set M} (hC : C⊆⋃ i,γ i '' s i) :
    volume ((extChartAt 𝓘(ℝ,ℝ × ℝ) c).target ∩
      (extChartAt 𝓘(ℝ,ℝ × ℝ) c).symm ⁻¹' C)=0 := by
  apply measure_mono_null _ (measure_iUnion_null (fun i => smooth_curve_chart_null c (hs i) (hγ i)))
  intro y hy
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hC hy.2)
  exact mem_iUnion.mpr ⟨i,hy.1,hi⟩

end

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × ℝ) M]
  [IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M]

 omit [IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M] in
 theorem smooth_boundary_coordinate_zero {D : Set M} (hD : IsClosed D)
    (e : PartialDiffeomorph 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℝ × ℝ) M (ℝ × ℝ) ∞)
    (he : ∀ y∈e.source,(y∈D ↔ 0≤(e y).2)) {x : M}
    (hx : x∈frontier D) (hxe : x∈e.source) : (e x).2=0 := by
  have hge := (he x hxe).mp (hD.frontier_subset hx)
  have hle : (e x).2≤0 := by
    by_contra! hp
    have hu : IsOpen (e.source ∩ e ⁻¹' {z : ℝ × ℝ | 0<z.2}) :=
      e.contMDiffOn.continuousOn.isOpen_inter_preimage e.open_source
        (isOpen_lt continuous_const continuous_snd)
    have hsub : e.source ∩ e ⁻¹' {z : ℝ × ℝ | 0<z.2}⊆D :=
      fun y hy => (he y hy.1).mpr hy.2.le
    exact hx.2 (interior_maximal hsub hu ⟨hxe,hp⟩)
  exact le_antisymm hle hge

 theorem smooth_surface_boundary_chart_null [T2Space M] {D : Set M}
    (hD : IsCompact D) (hb : HasSmoothSurfaceBoundary D) (c : M) :
    volume ((extChartAt 𝓘(ℝ,ℝ × ℝ) c).target ∩
      (extChartAt 𝓘(ℝ,ℝ × ℝ) c).symm ⁻¹' frontier D)=0 := by
  classical
  choose e he hm using (fun x : frontier D => hb x.1 x.2)
  obtain ⟨a,ha⟩ := (hD.of_isClosed_subset isClosed_frontier hD.isClosed.frontier_subset).elim_finite_subcover (fun x : frontier D => (e x).source)
    (fun x => (e x).open_source) (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,he ⟨x,hx⟩⟩)
  let s : a → Set ℝ := fun x => (fun t : ℝ => (t,0)) ⁻¹' (e x.1).target
  let γ : a → ℝ → M := fun x t => (e x.1).symm (t,0)
  have hs (x : a) : IsOpen (s x) := (e x.1).open_target.preimage (continuous_id.prodMk continuous_const)
  have hg (x : a) : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ × ℝ) ∞ (γ x) (s x) :=
    (e x.1).symm.contMDiffOn.comp ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffOn)
      (fun _ ht => ht)
  apply countable_smooth_curve_cover_chart_null c s γ hs hg
  intro y hy
  obtain ⟨x,hxa,hyx⟩ := mem_iUnion₂.mp (ha hy)
  have heq := smooth_boundary_coordinate_zero hD.isClosed (e x) (hm x) hy hyx
  have hepair : e x y=((e x y).1,0) := Prod.ext rfl heq
  refine mem_iUnion.mpr ⟨⟨x,hxa⟩,(e x y).1,?_,?_⟩
  · change ((e x y).1,0)∈(e x).target
    rw [← hepair]
    exact (e x).map_source hyx
  · change (e x).symm ((e x y).1,0)=y
    rw [← hepair]
    exact (e x).left_inv hyx

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

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem radialArea_nonneg (x : Plane) : 0 ≤ radialArea x :=
  mul_nonneg Real.pi_pos.le (by dsimp [radiusSq] <;> positivity)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem planeMoments_nonneg (z : PlanePhase ι) (i : ι) : 0 ≤ planeMoments z i :=
  radialArea_nonneg (z i)

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
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
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

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open scoped BigOperators
open scoped Manifold
open Manifold
section

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {μ : V → ℝ} {a : ℝ}

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
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_AnnularDensityMass
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
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem toricPrimitiveInterpolation_smooth {Γ₀ Γ₁ : P → ManifoldOneForm E M}
    (h₀ : SmoothOneFormFamily Γ₀) (h₁ : SmoothOneFormFamily Γ₁) :
    SmoothOneFormFamily (toricPrimitiveInterpolation Γ₀ Γ₁) :=
  ((h₀.comp contDiff_snd).smul (contDiff_const.sub contDiff_fst)).add
    ((h₁.comp contDiff_snd).smul contDiff_fst)

theorem toricPrimitiveInterpolation_exterior [IsManifold 𝓘(ℝ,E) ∞ M]
    {Γ₀ Γ₁ : P → ManifoldOneForm E M} (h₀ : SmoothOneFormFamily Γ₀)
    (h₁ : SmoothOneFormFamily Γ₁) (t : ℝ) (p : P) (x : M) :
    manifoldExteriorOneForm (toricPrimitiveInterpolation Γ₀ Γ₁ (t,p)) x=
      (1-t) • manifoldExteriorOneForm (Γ₀ p) x+t • manifoldExteriorOneForm (Γ₁ p) x := by
  have hx := (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source (I := 𝓘(ℝ,E)) x)
  have hc₀ := h₀.spatial_smooth p x hx
  have hc₁ := h₁.spatial_smooth p x hx
  have hs₀ : ContDiffAt ℝ ∞ (chartOneForm ((1-t) • Γ₀ p) x) (extChartAt 𝓘(ℝ,E) x x) := by
    rw [show chartOneForm ((1-t) • Γ₀ p) x=fun y => (1-t) • chartOneForm (Γ₀ p) x y
      from funext (chartOneForm_smul (1-t) (Γ₀ p) x)]
    exact hc₀.const_smul (1-t)
  have hs₁ : ContDiffAt ℝ ∞ (chartOneForm (t • Γ₁ p) x) (extChartAt 𝓘(ℝ,E) x x) := by
    rw [show chartOneForm (t • Γ₁ p) x=fun y => t • chartOneForm (Γ₁ p) x y
      from funext (chartOneForm_smul t (Γ₁ p) x)]
    exact hc₁.const_smul t
  exact (manifoldExteriorOneForm_add_at hs₀ hs₁).trans
    (congrArg₂ (Add.add (α := E →L[ℝ] E →L[ℝ] ℝ))
      (manifoldExteriorOneForm_smul_at (1-t) hc₀)
      (manifoldExteriorOneForm_smul_at t hc₁))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {N : Type*} [TopologicalSpace N] [ChartedSpace Plane N] [IsManifold 𝓘(ℝ,Plane) ∞ N]

theorem toricPrimitiveInterpolation_isInvertible
    {Γ₀ Γ₁ : (ι → ℝ) → ManifoldOneForm Plane N}
    (h₀ : SmoothOneFormFamily Γ₀) (h₁ : SmoothOneFormFamily Γ₁)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (z : N × PlanePhase ι)
    (hp₀ : 0 < chartTwoForm (manifoldExteriorOneForm (Γ₀ (planeMoments z.2)))
      z.1 (extChartAt 𝓘(ℝ,Plane) z.1 z.1) (1,0) (0,1))
    (hp₁ : 0 < chartTwoForm (manifoldExteriorOneForm (Γ₁ (planeMoments z.2)))
      z.1 (extChartAt 𝓘(ℝ,Plane) z.1 z.1) (1,0) (0,1)) :
    (globalHorizontalCoupling phaseArea (fun v => toricPrimitiveInterpolation Γ₀ Γ₁ (t,planeMoments v)) z).IsInvertible := by
  apply globalToricCoupling_isInvertible
    ((toricPrimitiveInterpolation_smooth h₀ h₁).comp
      (contDiff_const.prodMk (contDiff_id : ContDiff ℝ ∞ (fun p : ι → ℝ => p))))
  have he : manifoldExteriorOneForm (toricPrimitiveInterpolation Γ₀ Γ₁ (t,planeMoments z.2))=
      (1-t) • manifoldExteriorOneForm (Γ₀ (planeMoments z.2))+
        t • manifoldExteriorOneForm (Γ₁ (planeMoments z.2)) :=
    funext (toricPrimitiveInterpolation_exterior h₀ h₁ t (planeMoments z.2))
  dsimp only [Function.comp_apply,id_eq]
  rw [he,chartTwoForm_add,chartTwoForm_smul,chartTwoForm_smul]
  change 0<(1-t)*_+t*_
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hp₀) (mul_nonneg ht.1 hp₁.le)
  · simpa using hp₁

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem toric_redistribution_moser
    {Γ₀ Γ₁ : (ι → ℝ) → ManifoldOneForm Plane M}
    (h₀ : SmoothOneFormFamily Γ₀) (h₁ : SmoothOneFormFamily Γ₁)
    {D S : Set M} (hS : IsCompact S) (hSD : S⊆interior D)
    (hstation : ∀ x,x∉S→∀ p,Γ₁ p x=Γ₀ p x)
    {Y : Set (ι → ℝ)}
    (hp₀ : ∀ p∈Y,∀ x∈D,0 < chartTwoForm (manifoldExteriorOneForm (Γ₀ p))
      x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    (hp₁ : ∀ p∈Y,∀ x∈D,0 < chartTwoForm (manifoldExteriorOneForm (Γ₁ p))
      x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    {J : Type*} (F : J → (ι → ℝ) → ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j,α j < c j)
    (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v ≤ c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y)) :
    ∃ ψ : (M × PlanePhase ι) ≃ₘ⟮𝓘(ℝ,Plane × PlanePhase ι),𝓘(ℝ,Plane × PlanePhase ι)⟯ (M × PlanePhase ι),
      ψ '' (D ×ˢ (planeMoments ⁻¹' Y))=D ×ˢ (planeMoments ⁻¹' Y) ∧
      ψ '' interior (D ×ˢ (planeMoments ⁻¹' Y))=interior (D ×ˢ (planeMoments ⁻¹' Y)) ∧
      PreservesTwoFormOn ψ (globalHorizontalCoupling phaseArea (Γ₀ ∘ planeMoments))
        (globalHorizontalCoupling phaseArea (Γ₁ ∘ planeMoments)) (D ×ˢ (planeMoments ⁻¹' Y)) ∧
      (∃ C : Set (M × PlanePhase ι),IsCompact C ∧ ∀ z,z∉C→ψ z=z) ∧
      (∀ z,z.1∉S→ψ z=z) := by
  have hdom : {v | ∀ j,F j (planeMoments v) ≤ c j}=planeMoments ⁻¹' Y := hYeq.symm
  have hsmooth := toricPrimitiveInterpolation_smooth h₀ h₁
  have hparam : ∀ t x,ContDiff ℝ ∞ (fun p => toricPrimitiveInterpolation Γ₀ Γ₁ (t,p) x) := by
    intro t x
    exact (contDiff_iff_contDiffAt.mpr (fun q => hsmooth.parameter_contDiffAt q x)).comp
      (contDiff_const.prodMk contDiff_id)
  obtain ⟨ψ,hD,hI,hp,hC,hfix⟩ := horizontal_moser_endpoint_bp240 phaseArea_isInvertible phaseArea_skew
    (hsmooth.comp (contDiff_fst.prodMk (planeMoments_smooth.comp contDiff_snd))) hS hSD
    (fun x hx t v => by
      simp only [Function.comp_apply,toricPrimitiveInterpolation,Pi.add_apply,Pi.smul_apply,
        hstation x hx,←add_smul]
      congr 1; ring)
    (fun j => F j ∘ planeMoments) (fun j => (hF j).comp planeMoments_smooth)
    α c hαc (hYeq ▸ hYC)
    (fun j t x => toric_collarInvariant (hF j) (hparam t x) (α j))
    (fun t ht z hz => toricPrimitiveInterpolation_isInvertible h₀ h₁ ht z
      (hp₀ _ (by exact (show z.2∈planeMoments ⁻¹' Y from hYeq.symm ▸ hz.2)) _ hz.1)
      (hp₁ _ (by exact (show z.2∈planeMoments ⁻¹' Y from hYeq.symm ▸ hz.2)) _ hz.1))
  refine ⟨ψ,?_,?_,?_,hC,hfix⟩
  · simpa only [←hYeq] using hD
  · simpa only [←hYeq] using hI
  · simp only [Function.comp_apply,toricPrimitiveInterpolation_zero,
      toricPrimitiveInterpolation_one,hdom] at hp
    convert hp using 1 <;> rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold MeasureTheory

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]
  {I : Type*} [Fintype I]

 theorem exists_surface_initial_packing {m N : ℕ} {Kbase : Set M}
    (hD : IsCompact Kbase) (hcD : IsPreconnected (interior Kbase)) (hne : (interior Kbase).Nonempty)
    (hor : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (π : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M Kbase)
    (hπ : π.IsSubordinate (fun i => (B i).carrier))
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' frontier Kbase)=0)
    (D : AnnularHandleData Plane M)
    {b δ : ℝ} (hb : 0<b) (hbw : b<D.width) (hδ : 0<δ) (hsmall : δ<1/2)
    (heD : closure D.chart.target⊆interior Kbase) (hβD : tsupport D.dual⊆interior Kbase)
    (heor : PositivePartialChart D.densityChart)
    (hclock : D.clock=positiveCircleClock δ)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target →
      0 < chartTwoForm Λ c y (1,0) (0,1))
    {d : (Fin m → ℝ) × M → ℝ}
    (hd : ContMDiff (𝓘(ℝ,Fin m → ℝ).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ d)
    {Y V : Set (Fin m → ℝ)} (hY : IsCompact Y) (hdp : ∀ p∈Y,∀ x∈Kbase,0<d (p,x))
    {Γ₀ : (Fin m → ℝ) → ManifoldOneForm Plane M} (hΓ₀ : SmoothOneFormFamily Γ₀)
    (hdΓ₀ : ∀ p x,manifoldExteriorOneForm (Γ₀ p) x=d (p,x) • Λ x)
    {A : (Fin m → ℝ) → ℝ} {ε : ℝ} (hε : 0<ε) (hA : ∀ p∈Y,2*ε<A p)
    (herr : ∀ p∈Y,|restrictedPartitionFormMass B π Kbase (fun x => d (p,x) • Λ x)-A p|<ε)
    {K : (Fin m → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (hV : IsOpen (planeMoments ⁻¹' V)) (hVY : V⊆Y)
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    (h : Fin N → (Fin m → ℝ) → ℝ) (hh : ∀ i,ContDiff ℝ ∞ (h i))
    (hhp : ∀ i p,p∈Y → 0≤h i p)
    (hres : ∀ H : (Fin m → ℝ) → ℝ,(∀ p∈Y,|H p-A p|<2*ε) →
      ∀ v,planeMoments v∈Y → 0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments)
        (fun j => h j ∘ planeMoments) (Φ.map 1).symm v)
    (r r' : Fin N → ℝ) (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
    (hsimplex : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → (∑ j,p j) ≤ r' i → p∈V)
    (hheight : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → p∈V → r i-(∑ j,p j)≤h i p)
    {J : Type*} (F : J → (Fin m → ℝ) → ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j,α j < c j)
    (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v ≤ c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    (hzero : ∀ j t v,α j<(F j ∘ planeMoments) v →
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t,v))=0) :
    ∃ φ : Fin N → Ambient (m+1) → M × PlanePhase (Fin m),
      (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
        (globalHorizontalCoupling phaseArea (Γ₀ ∘ planeMoments)) (φ i)) ∧
      (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ×ˢ (planeMoments ⁻¹' Y)))) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  obtain ⟨q,s,H,Γ₁,γ,L,W,hq,_,hH,_,hbound,hΓ₁,hL,hLD,hW,hBW,hWA,haway,_,hpos,_,hγ,hdγ,hN,_⟩ :=
    exists_surface_step_two_bp240 hD hcD hne hor B π hπ hnull D hb hbw heD hβD heor hΛ hsΛ hpΛ
      hd hY hdp hΓ₀ hdΓ₀ hε hA herr
  have hΓ₁pos : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ₁ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1) := by
    intro p hp x hx
    exact hpos p hp x _ (mem_extChartAt_target x) (by simpa using hx)
  obtain ⟨φ,hφ,him,hdis⟩ := exists_surface_normal_form_packing_bp240 D hb hbw hδ hsmall heor hclock
    hΛ hsΛ hpΛ hq hγ hdγ hΓ₁ hK hH (fun p hp => (hbound p hp).1.le) (subset_closure.trans heD) hβD hΓ₁pos hW hBW hWA hN
    Φ hV hVY hΦ h hh hhp (hres H (fun p hp => (hbound p hp).2)) r r' hr' hrr hsimplex hheight
    F hF α c hαc hYeq hYC hzero
  have hp₀ : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ₀ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1) := by
    intro p hp x hx
    have heq : manifoldExteriorOneForm (Γ₀ p)=fun x => d (p,x) • Λ x := funext (hdΓ₀ p)
    rw [heq,chartTwoForm_spatial_smul]
    change 0<d (p,(extChartAt 𝓘(ℝ,Plane) x).symm (extChartAt 𝓘(ℝ,Plane) x x))*
      chartTwoForm Λ x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1)
    simpa using mul_pos (hdp p hp x hx) (hpΛ x _ (mem_extChartAt_target x))
  obtain ⟨ψ,hDψ,hIψ,hform,_,_⟩ := toric_redistribution_moser hΓ₀ hΓ₁ hL hLD
    (fun x hx p => haway p x hx) hp₀ hΓ₁pos F hF α c hαc hYeq hYC
  obtain ⟨hφ₀,him₀,hdis₀⟩ := transport_form_packing (fun i => closedBall (m+1) (r' i))
    (fun _ => successorStandardForm m) _ _ ψ hform hDψ hIψ φ hφ him hdis
  exact ⟨fun i => ψ.symm ∘ φ i,hφ₀,him₀,hdis₀⟩

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_DisjointClocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function

variable {ι : Type*} [Fintype ι]

theorem isCompact_preimage_planeMoments {D : Set (ι → ℝ)} (hD : IsCompact D) :
    IsCompact (planeMoments ⁻¹' D) := by
  obtain ⟨R,hR⟩ := hD.isBounded.exists_norm_le
  have hp : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hclosed : IsClosed (planeMoments ⁻¹' D) :=
    hD.isClosed.preimage planeMoments_smooth.continuous
  apply (isCompact_closedBall (0 : PlanePhase ι) (|R|+1)).of_isClosed_subset hclosed
  intro z hz
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ) ≤ |R|+1)).2
  intro i
  have hm : planeMoments z i ≤ |R| :=
    (le_abs_self _).trans ((norm_le_pi_norm (planeMoments z) i).trans ((hR _ hz).trans (le_abs_self R)))
  have hs : (z i).1^2+(z i).2^2 ≤ planeMoments z i := by
    change (z i).1^2+(z i).2^2 ≤ Real.pi*((z i).1^2+(z i).2^2)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  apply max_le
  · nlinarith [sq_abs (z i).1,abs_nonneg (z i).1,sq_nonneg (z i).2,abs_nonneg R]
  · nlinarith [sq_abs (z i).2,abs_nonneg (z i).2,sq_nonneg (z i).1,abs_nonneg R]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff BigOperators
open Set Function
open Hamiltonian

theorem planeRegion_isCompact {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hC : IsCompact (region b c)) : IsCompact (planeRegion b c) :=
  isCompact_preimage_planeMoments hC

end PackingSufficiencySupport.MomentPolytope

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_SurfaceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators Pointwise
open Set Function MeasureTheory
open Hamiltonian Comparison

theorem finite_uniform_area_error {m : ℕ} {D : Set (Moments m)}
    {A : ℕ → Moments m → ℝ} {H : Moments m → ℝ}
    (hA : TendstoUniformlyOn A H Filter.atTop D) {ε : ℝ} (hε : 0<ε) :
    ∃ L : ℕ,∀ ℓ ≥ L,∀ p ∈ D,|A ℓ p-H p|<ε := by
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hA) ε hε)
  refine ⟨L,fun ℓ hℓ p hp => ?_⟩
  simpa only [Real.dist_eq,abs_sub_comm] using hL ℓ hℓ p hp

 theorem strictRegion_subset {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) :
    strictRegion b c⊆region b c := fun _ hp => ⟨hp.1,fun ν => (hp.2 ν).le⟩

 theorem strictRegion_phase_open {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) :
    IsOpen (planeMoments ⁻¹' strictRegion b c) := by
  have he : planeMoments ⁻¹' strictRegion b c = ⋂ ν,{z | weightedMoment (b ν) z < c ν} := by
    ext z
    simp only [mem_preimage,strictRegion,mem_ofPred_eq,mem_iInter]
    exact ⟨fun h => h.2,fun h => ⟨planeMoments_nonneg z,h⟩⟩
  rw [he]
  exact isOpen_iInter_of_finite (fun ν => isOpen_lt (weightedMoment_smooth (b ν)).continuous continuous_const)

 theorem planeRegion_outer_constraints {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) :
    planeMoments ⁻¹' region b c = {z | ∀ ν,(fun p => ∑ j,b ν j*p j) (planeMoments z) ≤ c ν} := by
  ext z
  change ((∀ j,0≤planeMoments z j) ∧ _) ↔ _
  exact ⟨fun h => h.2,fun h => ⟨planeMoments_nonneg z,h⟩⟩

 theorem momentFace_smooth {m : ℕ} (b : Moments m) :
    ContDiff ℝ ∞ (fun p : Moments m => ∑ j,b j*p j) := by fun_prop

 theorem face_collars_of_comparison {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (hface : ∀ ν,∃ ρ>0,∀ t z,c ν-weightedMoment (b ν) z<ρ →
      fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z))=0) :
    ∃ α : Fin N → ℝ,(∀ ν,α ν < c ν) ∧ ∀ ν t z,
      α ν<(fun p => ∑ j,b ν j*p j) (planeMoments z) →
      fderiv ℝ ((fun p => ∑ j,b ν j*p j) ∘ planeMoments) z
        (hamiltonianField phaseArea Φ.hamiltonian (t,z))=0 := by
  classical
  choose ρ hρ hzero using hface
  refine ⟨fun ν => c ν-ρ ν,fun ν => sub_lt_self _ (hρ ν),?_⟩
  intro ν t z hz
  apply hzero ν t z
  change c ν-(∑ j,b ν j*planeMoments z j)<ρ ν
  linarith

 theorem comparison_preserves_region {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (hmem : ∀ t z,Φ.map t z∈planeRegion b c ↔ z∈planeRegion b c) :
    ∀ t,MapsTo (Φ.map t) (planeMoments ⁻¹' region b c) (planeMoments ⁻¹' region b c) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' region b c) (planeMoments ⁻¹' region b c) := by
  intro t
  refine ⟨fun z hz => (hmem t z).2 hz,?_⟩
  intro z hz
  apply (hmem t ((Φ.map t).symm z)).1
  change planeMoments ((Φ.map t) ((Φ.map t).symm z))∈region b c
  rw [Homeomorph.apply_symm_apply]
  exact hz

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope.Annular
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Manifold MeasureTheory
open Hamiltonian Hamiltonian.AnnularHandleData

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]

 theorem surface_packing_tolerance {m q N : ℕ} [Nonempty (Fin N)]
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
    (houter : ∀ p∈region bF cF,p∉τ • region bF cF → d₀≤A p-∑ i,max (r i-∑ j,p j) 0) :
    ∃ ε>0,∀ {I : Type*} [Fintype I],∀ (Kbase : Set M) (_hD : IsCompact Kbase) (_hcD : IsPreconnected (interior Kbase))
      (_hne : (interior Kbase).Nonempty) (_hor : PositivePlaneTransitions M)
      (B : I → SurfaceCoordinateBox M) (π : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M Kbase),
      π.IsSubordinate (fun i => (B i).carrier) →
      (∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
        (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' frontier Kbase)=0) →
      ∀ (D : AnnularHandleData Plane M)
      {b δ : ℝ}, 0<b → b<D.width → 0<δ → δ<1/2 →
      closure D.chart.target⊆interior Kbase → tsupport D.dual⊆interior Kbase →
      PositivePartialChart D.densityChart →
      D.clock=positiveCircleClock δ →
      ∀ {Λ : ManifoldTwoForm Plane M}, SmoothTwoForm Λ →
      (∀ x u v,Λ x u v= -Λ x v u) →
      (∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0 < chartTwoForm Λ c y (1,0) (0,1)) →
      ∀ {d : Moments m × M → ℝ},
      ContMDiff (𝓘(ℝ,Moments m).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ d →
      (∀ p∈region bF cF,∀ x∈Kbase,0<d (p,x)) →
      ∀ {Γ₀ : Moments m → ManifoldOneForm Plane M}, SmoothOneFormFamily Γ₀ →
      (∀ p x,manifoldExteriorOneForm (Γ₀ p) x=d (p,x) • Λ x) →
      (∀ p∈region bF cF,|restrictedPartitionFormMass B π Kbase (fun x => d (p,x) • Λ x)-A p|<ε) →
      ∃ φ : Fin N → Ambient (m+1) → M × PlanePhase (Fin m),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
          (globalHorizontalCoupling phaseArea (Γ₀ ∘ planeMoments)) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ×ˢ planeRegion bF cF))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  obtain ⟨K,Φ,g,ε,h,hK,hg,hε,_,hAε,hh,hhcap,_,hmem,hfaceΦ,hres⟩ :=
    finite_surface_comparison_bp240 bF cF hbF hcF hcomp A hA hAp r hconc hmean hτ hτ1 hd₀ houter
  obtain ⟨α,hαc,hzero⟩ := face_collars_of_comparison bF cF Φ hfaceΦ
  refine ⟨ε,hε,?_⟩
  intro I _ Kbase hD hcD hne hor B π hπ hnull D b δ hb hbw hδ hsmall heD hβD heor hclock
    Λ hΛ hsΛ hpΛ d hd hdp Γ₀ hΓ₀ hdΓ₀ herr
  have hSm : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j) ≤ r' i → p∈strictRegion bF cF := by
    intro i p hp hsum
    have hrp : (∑ j,p j) ≤ r i := hsum.trans (hrr i).le
    exact ⟨hp,fun ν => lt_of_le_of_ne ((hsimplex i p hp hrp).2 ν) (hface i p hp hrp ν)⟩
  exact exists_surface_initial_packing hD hcD hne hor B π hπ hnull D hb hbw hδ hsmall heD hβD heor hclock
    hΛ hsΛ hpΛ hd hcomp hdp hΓ₀ hdΓ₀ hε (fun p hp => by have := hAε p hp; linarith) herr
    hK Φ (strictRegion_phase_open bF cF) (strictRegion_subset bF cF)
    (fun t _ => comparison_preserves_region bF cF Φ hmem t) h hh
    (fun i p _ => (le_max_right _ _).trans (hhcap i p).le)
    (fun H hH v hv => (by linarith : (0:ℝ)<g/2).le.trans ((hres H hH).2 v hv).le)
    r r' hr' hrr hSm (fun i p _ _ => (le_max_left _ _).trans (hhcap i p).le)
    (fun ν p => ∑ j,bF ν j*p j) (fun ν => momentFace_smooth (bF ν)) α cF hαc
    (planeRegion_outer_constraints bF cF) (planeRegion_isCompact bF cF hcomp) hzero

 theorem intrinsic_surface_packing_tolerance {m q N : ℕ} [Nonempty (Fin N)]
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
    (houter : ∀ p∈region bF cF,p∉τ • region bF cF → d₀≤A p-∑ i,max (r i-∑ j,p j) 0) :
    ∃ ε>0,∀ (Kbase : Set M) (hD : IsCompact Kbase) (_hcD : IsPreconnected (interior Kbase))
      (_hne : (interior Kbase).Nonempty) (_hor : PositivePlaneTransitions M)
      (_hb : HasSmoothSurfaceBoundary Kbase),
      ∀ (D : AnnularHandleData Plane M)
      {b δ : ℝ}, 0<b → b<D.width → 0<δ → δ<1/2 →
      closure D.chart.target⊆interior Kbase → tsupport D.dual⊆interior Kbase →
      PositivePartialChart D.densityChart →
      D.clock=positiveCircleClock δ →
      ∀ {Λ : ManifoldTwoForm Plane M}, SmoothTwoForm Λ →
      (∀ x u v,Λ x u v= -Λ x v u) →
      (∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0 < chartTwoForm Λ c y (1,0) (0,1)) →
      ∀ {d : Moments m × M → ℝ},
      ContMDiff (𝓘(ℝ,Moments m).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ d →
      (∀ p∈region bF cF,∀ x∈Kbase,0<d (p,x)) →
      ∀ {Γ₀ : Moments m → ManifoldOneForm Plane M}, SmoothOneFormFamily Γ₀ →
      (∀ p x,manifoldExteriorOneForm (Γ₀ p) x=d (p,x) • Λ x) →
      (∀ p∈region bF cF,|compactSurfaceFormIntegral hD (fun x => d (p,x) • Λ x)-A p|<ε) →
      ∃ φ : Fin N → Ambient (m+1) → M × PlanePhase (Fin m),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
          (globalHorizontalCoupling phaseArea (Γ₀ ∘ planeMoments)) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ×ˢ planeRegion bF cF))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  obtain ⟨ε,hε,hpack⟩ := surface_packing_tolerance (M := M) bF cF hbF hcF hcomp A hA hAp r r' hr' hrr
    hsimplex hface hconc hmean hτ hτ1 hd₀ houter
  refine ⟨ε,hε,?_⟩
  intro Kbase hD hcD hne hor hb D b δ hbp hbw hδ hsmall heD hβD heor hclock
    Λ hΛ hsΛ hpΛ d hd hdp Γ₀ hΓ₀ hdΓ₀ herr
  exact hpack Kbase hD hcD hne hor
    (fun B : compactSurfaceBoxes hD => B.1) (compactSurfacePartition hD)
    (compactSurfacePartition_subordinate hD)
    (fun B => smooth_surface_boundary_chart_null hD hb B.1.center)
    D hbp hbw hδ hsmall heD hβD heor hclock
    hΛ hsΛ hpΛ hd hdp hΓ₀ hdΓ₀ herr

 theorem exhausted_surface_packing_bp240_oai {m q N : ℕ} [Nonempty (Fin N)]
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
    (Kbase : ℕ → Set M) (hD : ∀ ℓ,IsCompact (Kbase ℓ))
    (hmono : ∀ ℓ,Kbase ℓ⊆interior (Kbase (ℓ+1))) (hcover : (⋃ ℓ,Kbase ℓ)=univ)
    (hcD : ∀ ℓ,IsPreconnected (interior (Kbase ℓ))) (hne : ∀ ℓ,(interior (Kbase ℓ)).Nonempty)
    (hb : ∀ ℓ,HasSmoothSurfaceBoundary (Kbase ℓ)) (hor : PositivePlaneTransitions M)
    (D : AnnularHandleData Plane M)
    {b δ : ℝ} (hbp : 0<b) (hbw : b<D.width) (hδ : 0<δ) (hsmall : δ<1/2)
    (heor : PositivePartialChart D.densityChart)
    (hclock : D.clock=positiveCircleClock δ)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0 < chartTwoForm Λ c y (1,0) (0,1))
    (d : ℕ → Moments m × M → ℝ)
    (hd : ∀ ℓ,ContMDiff (𝓘(ℝ,Moments m).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ (d ℓ))
    (hdp : ∀ ℓ,∀ p∈region bF cF,∀ x∈Kbase ℓ,0<d ℓ (p,x))
    (Γ : ℕ → Moments m → ManifoldOneForm Plane M) (hΓ : ∀ ℓ,SmoothOneFormFamily (Γ ℓ))
    (hdΓ : ∀ ℓ p x,manifoldExteriorOneForm (Γ ℓ p) x=d ℓ (p,x) • Λ x)
    (hlim : TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (hD ℓ)
      (fun x => d ℓ (p,x) • Λ x)) A Filter.atTop (region bF cF)) :
    ∃ ℓ,∃ φ : Fin N → Ambient (m+1) → M × PlanePhase (Fin m),
      (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
        (globalHorizontalCoupling phaseArea (Γ ℓ ∘ planeMoments)) (φ i)) ∧
      (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ℓ ×ˢ planeRegion bF cF))) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  obtain ⟨ε,hε,hpack⟩ := intrinsic_surface_packing_tolerance (M := M) bF cF hbF hcF hcomp
    A hA hAp r r' hr' hrr hsimplex hface hconc hmean hτ hτ1 hd₀ houter
  obtain ⟨L,hL⟩ := finite_uniform_area_error hlim hε
  have hmo : Monotone Kbase := monotone_nat_of_le_succ (fun ℓ => (hmono ℓ).trans interior_subset)
  have hco : (closure D.chart.target ∪ tsupport D.dual)⊆⋃ ℓ,interior (Kbase ℓ) := by
    intro x _
    obtain ⟨ℓ,hx⟩ := mem_iUnion.mp (show x∈⋃ ℓ,Kbase ℓ by rw [hcover]; trivial)
    exact mem_iUnion.mpr ⟨ℓ+1,hmono ℓ hx⟩
  obtain ⟨J,hJ⟩ := (D.compact_target.union D.dual_compact).elim_directed_cover (fun ℓ => interior (Kbase ℓ)) (fun _ => isOpen_interior)
    hco (fun i j => ⟨max i j,interior_mono (hmo (le_max_left i j)),
      interior_mono (hmo (le_max_right i j))⟩)
  refine ⟨max L J,?_⟩
  exact hpack (Kbase (max L J)) (hD _) (hcD _) (hne _) hor (hb _) D hbp hbw hδ hsmall
    ((subset_union_left).trans (hJ.trans (interior_mono (hmo (le_max_right L J)))))
    ((subset_union_right).trans (hJ.trans (interior_mono (hmo (le_max_right L J))))) heor hclock
    hΛ hsΛ hpΛ (hd _) (hdp _) (hΓ _) (hdΓ _) (hL _ (le_max_left L J))

end PackingSufficiencySupport.MomentPolytope.Annular

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing_bp240_oai := @OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing_bp240_oai
