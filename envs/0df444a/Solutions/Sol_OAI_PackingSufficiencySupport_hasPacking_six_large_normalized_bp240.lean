-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.hasPacking_six_large_normalized_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:28.805508+00:00
-- url     : https://prove2.me/submissions/2fac7f2a-f220-4b72-b7ec-0a173705ea30

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_actual_cubic_representative_packing_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_cubic_bubble_target_packing_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_exists_actual_cubic_normal_transfer_into_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_exact_fibre_embedding_into_bp240

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

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldFormTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold
open scoped ContDiff Manifold Topology

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

 theorem polynomial_contDiff : ContDiff ℂ ∞ polynomial := by
  unfold polynomial
  fun_prop

 theorem source_equation_zero (x : BaseCurve) : (x.val.2 0)^2=x.val.1^2-1 := by
  simpa only [parameters_zero] using (mem_locus.mp x.property) 0
 theorem source_equation_one (x : BaseCurve) : (x.val.2 1)^2=x.val.1^2-2 := by
  simpa only [parameters_one] using (mem_locus.mp x.property) 1

 theorem inclusion_fst_ne_zero (x : BaseCurve) : (inclusion x).1≠0 := by
  intro h
  have he : x.val.2 0=x.val.1 := sub_eq_zero.mp h
  have h0 := source_equation_zero x
  rw [he] at h0
  have hh : (1:ℂ)=0 := by linear_combination h0
  exact one_ne_zero hh

 theorem inclusion_snd_ne_zero (x : BaseCurve) : (inclusion x).2≠0 := by
  intro h
  have he : x.val.2 1=x.val.1 := sub_eq_zero.mp h
  have h1 := source_equation_one x
  rw [he] at h1
  have hh : (1:ℂ)=0 := by linear_combination h1 / 2
  exact one_ne_zero hh

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_CubicFubiniStudy
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
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 theorem weightedProjection_contDiff (D m : ℕ) : ContDiff ℂ ∞ (weightedProjection D m) := by
  apply ContDiff.prodMk (contDiff_fst.pow (D-m))
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact contDiff_snd.pow (D-m)
  · exact (contDiff_fst.pow (D-m)).mul (contDiff_snd.pow m)
  · exact (contDiff_fst.pow m).mul (contDiff_snd.pow (D-m))

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

variable {ι : Type*} [Fintype ι]

theorem complexAffineLift_smooth : ContDiff ℝ ∞ (complexAffineLift (ι := ι)) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | none => exact contDiff_const
  | some i => exact contDiff_apply ℝ ℂ i

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_AnnularChartHelpers
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
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

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem primitivePullback_exterior {α : F → F →L[ℝ] ℝ} {g : E → F}
    (hα : ContDiff ℝ ∞ α) (hg : ContDiff ℝ ∞ g) (x : E) :
    euclideanExteriorOneForm (primitivePullback α g) x=
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  have hh := manifold_pullback_exterior (α := α) (g := g)
    (fun c => by
      rw [show chartOneForm α c=α from funext (vector_chartOneForm α c)]
      exact hα.contDiffOn)
    hg.contMDiff x
  have he : manifoldPullbackOneForm (fun _ => α) g 0=primitivePullback α g := by
    funext z
    simp [manifoldPullbackOneForm,manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback]
  rw [he] at hh
  simpa only [vector_exteriorOneForm,manifoldPullbackOneForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback] using hh

end

variable {ι : Type*} [Fintype ι]

 theorem hopfPrimitive_smoothAt (c : ℝ) {z : PlanePhase ι} (hz : z≠0) :
    ContDiffAt ℝ ∞ (hopfPrimitive c) z := by
  exact (contDiffAt_const.div (contDiffAt_const.mul phaseSq_smooth.contDiffAt)
    (mul_ne_zero (by norm_num) (phaseSq_pos hz).ne')).smul (phaseArea (ι := ι)).contDiff.contDiffAt

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_CubicEndCoordinates
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

theorem complexCartesian_affineComplex (z : Affine m) :
    complexCartesian (affineComplex m z)=affinePhase m z := by
  ext i <;> cases i <;> rfl

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RadialSwap
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

theorem lattice_zero (A B : ℕ) : ∃ i : TrapezoidWeight A B,latticeIndex i=(0,0) :=
  ⟨⟨(⟨0,by omega⟩,⟨0,by omega⟩),by simp⟩,rfl⟩


end


open scoped BigOperators Topology ContDiff
open Set Filter Function



end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialFamilyExtension
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

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold

 theorem totalWeight_le {A B : ℕ} (k : TrapezoidWeight A B) : totalWeight k≤B := k.property.2

end PackingSufficiencySupport.CubicModel
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
-- module Solutions.OAIQ240_BP.BallPacking_Models_BallVolume
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical

namespace PackingSufficiencySupport

theorem closedBall_isClosed (n : ℕ) (R : ℝ) : IsClosed (closedBall n R) :=
  isClosed_le (continuous_capacity n) continuous_const

theorem closedBall_isCompact (n : ℕ) (R : ℝ) : IsCompact (closedBall n R) := by
  apply (isCompact_closedBall (0 : Ambient n) (max R 0 + 1)).of_isClosed_subset
    (closedBall_isClosed n R)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ max R 0 + 1)).mpr
  intro j
  have hj : Complex.normSq (z j) ≤ ∑ k, Complex.normSq (z k) :=
    Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (z k)) (Finset.mem_univ j)
  have hj' := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
  have hq : 0 ≤ Complex.normSq (z j) := Complex.normSq_nonneg (z j)
  have hs : (∑ k, Complex.normSq (z k)) * Real.pi ≤ R := by
    simpa [closedBall, capacity, mul_comm] using hz
  have hb : Complex.normSq (z j) ≤ max R 0 := by
    nlinarith [Real.pi_gt_three, le_max_left R 0]
  rw [Complex.normSq_eq_norm_sq] at hb
  have hm := le_max_right R 0
  nlinarith [sq_nonneg (‖z j‖ - 1)]

open MeasureTheory

end PackingSufficiencySupport
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

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N] [TopologicalSpace P] [ChartedSpace G P]

theorem FormNeighborhoodEmbedding.postcompose {K : Set N}
    {σ : ManifoldTwoForm F N} {Ω₀ : ManifoldTwoForm E M} {Ω₁ : ManifoldTwoForm G P}
    {f : N → M} (hf : FormNeighborhoodEmbedding K σ Ω₀ f)
    {T : Set M} (hT : IsOpen T) {g : M → P}
    (hg : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ g T)
    (hemb : Topology.IsEmbedding (fun x : T => g x.val))
    (hform : ∀ x ∈ T, ∀ v w, Ω₁ (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x w) = Ω₀ x v w)
    (him : MapsTo f K T) : FormNeighborhoodEmbedding K σ Ω₁ (g ∘ f) := by
  obtain ⟨U,hU,hKU,hs,he,hσ⟩ := hf
  let W := U ∩ f ⁻¹' T
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage hU hT
  have hWU : W ⊆ U := inter_subset_left
  have hWT : MapsTo f W T := inter_subset_right
  refine ⟨W,hW,fun x hx => ⟨hKU hx,him hx⟩,hg.comp (hs.mono hWU) hWT,?_,?_⟩
  · have he' := (he.comp (Topology.IsEmbedding.inclusion hWU)).codRestrict T
      (fun x : W => show f x.val ∈ T from x.property.2)
    exact hemb.comp he'
  · intro x hx v w
    have hd := mfderiv_comp x ((hg.contMDiffAt (hT.mem_nhds hx.2)).mdifferentiableAt (by simp))
      ((hs.contMDiffAt (hU.mem_nhds hx.1)).mdifferentiableAt (by simp))
    rw [hd]
    exact (hform (f x) hx.2 _ _).trans (hσ x hx.1 v w)

theorem postcompose_form_packing {ι : Type*} (K : ι → Set N)
    (σ : ManifoldTwoForm F N) (Ω₀ : ManifoldTwoForm E M) (Ω₁ : ManifoldTwoForm G P)
    {T : Set M} (hT : IsOpen T) (g : M → P)
    (hg : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ g T)
    (hemb : Topology.IsEmbedding (fun x : T => g x.val))
    (hform : ∀ x ∈ T, ∀ v w, Ω₁ (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) g x w) = Ω₀ x v w)
    (f : ι → N → M) (hf : ∀ i, FormNeighborhoodEmbedding (K i) σ Ω₀ (f i))
    (him : ∀ i, MapsTo (f i) (K i) T)
    (hd : Pairwise (fun i j => Disjoint (f i '' K i) (f j '' K j))) :
    (∀ i, FormNeighborhoodEmbedding (K i) σ Ω₁ (g ∘ f i)) ∧
      Pairwise (fun i j => Disjoint ((g ∘ f i) '' K i) ((g ∘ f j) '' K j)) := by
  refine ⟨fun i => (hf i).postcompose hT hg hemb hform (him i),?_⟩
  have hinj : InjOn g T := by
    intro x hx y hy heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) heq)
  intro i j hij
  rw [Set.image_comp,Set.image_comp]
  exact (hd hij).image hinj (image_subset_iff.mpr (him i)) (image_subset_iff.mpr (him j))

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_MovingPrimitiveNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem primitivePullback_smoothAt {α : F → F →L[ℝ] ℝ} {g : E → F} {x : E}
    (hα : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (primitivePullback α g) x :=
  (hα.comp x hg).clm_comp (hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_EqualNormalModelConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

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

theorem exists_rational_above_in_open {ι : Type*} [Fintype ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) {r : ι → ℝ} (hr : r ∈ U) :
    ∃ q : ι → ℚ, (∀ i, r i < q i) ∧ (fun i => (q i : ℝ)) ∈ U := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.1 hU r hr
  have hinterval (i : ι) : ∃ q : ℚ, r i < q ∧ (q : ℝ) < r i+ε/2 :=
    exists_rat_btwn (by linarith)
  choose q hlo hhi using hinterval
  refine ⟨q,hlo,hball ?_⟩
  rw [Metric.mem_ball]
  apply (dist_pi_lt_iff hε).2
  intro i
  rw [Real.dist_eq,abs_of_pos (sub_pos.mpr (hlo i))]
  linarith [hhi i]

theorem rational_packing_slack {ι : Type*} [Fintype ι] (n : ℕ) (R : ℝ) (r : ι → ℝ)
    (hvol : ∑ i,r i^n < R^n) (hpair : ∀ i j, i≠j → r i+r j<R) :
    ∃ q : ι → ℚ, (∀ i,r i<q i) ∧ (∑ i,(q i:ℝ)^n)<R^n ∧
      ∀ i j, i≠j → (q i:ℝ)+(q j:ℝ)<R := by
  let U : Set (ι → ℝ) := {s | (∑ i,s i^n)<R^n ∧ ∀ i j,i≠j → s i+s j<R}
  have hpairOpen : IsOpen {s : ι → ℝ | ∀ i j,i≠j → s i+s j<R} := by
    simp only [ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    refine isOpen_iInter_of_finite fun _h => ?_
    exact isOpen_lt ((continuous_apply i).add (continuous_apply j)) continuous_const
  have hU : IsOpen U := (isOpen_lt
    (continuous_finsetSum _ fun i _ => (continuous_apply i).pow n) continuous_const).inter hpairOpen
  obtain ⟨q,hq,hUq⟩ := exists_rational_above_in_open hU (show r∈U from ⟨hvol,hpair⟩)
  exact ⟨q,hq,hUq⟩

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

end PackingSufficiencySupport

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

theorem physicalParameter_smooth (L : ℝ) : ContDiff ℝ ∞ (physicalParameter L) := by
  unfold physicalParameter
  fun_prop

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

 theorem FormNeighborhoodEmbedding.congr_target_near
    {K : Set N} {D : Set M} {σ : ManifoldTwoForm F N} {Ω Ω' : ManifoldTwoForm E M}
    {f : N → M} (hf : FormNeighborhoodEmbedding K σ Ω f)
    (hmap : MapsTo f K D) (he : Ω =ᶠ[𝓝ˢ D] Ω') : FormNeighborhoodEmbedding K σ Ω' f := by
  obtain ⟨U,hU,hKU,hs,hfemb,hσ⟩ := hf
  obtain ⟨V,hV,hDV,hVe⟩ := mem_nhdsSet_iff_exists.mp he
  let W := U ∩ f ⁻¹' V
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage hU hV
  have hWU : W⊆U := inter_subset_left
  refine ⟨W,hW,fun x hx => ⟨hKU hx,hDV (hmap hx)⟩,hs.mono hWU,
    hfemb.comp (Topology.IsEmbedding.inclusion hWU),?_⟩
  intro x hx v w
  rw [← hVe hx.2]
  exact hσ x hx.1 v w

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem globalHorizontalCoupling_congr_joint (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    {Γ Γ' : V → ManifoldOneForm E M} {z : M × V}
    (h : ∀ᶠ q in 𝓝 z,Γ q.2 q.1=Γ' q.2 q.1) :
    globalHorizontalCoupling Ω Γ z=globalHorizontalCoupling Ω Γ' z := by
  have he : productHorizontalLift Γ=ᶠ[𝓝 z] productHorizontalLift Γ' := by
    filter_upwards [h] with q hq
    exact congrArg (fun L : E →L[ℝ] ℝ => L.comp (ContinuousLinearMap.fst ℝ E V)) hq
  exact congrArg (fun B => Ω.bilinearComp (ContinuousLinearMap.snd ℝ E V)
    (ContinuousLinearMap.snd ℝ E V)+B) (manifoldExteriorOneForm_congr_germ he)

end PackingSufficiencySupport.Hamiltonian

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

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem globalHorizontalCoupling_congr_germs (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    {Γ Γ' : V → ManifoldOneForm E M} {K : Set (M × V)}
    (h : ∀ z∈K,∀ᶠ q in 𝓝 z,Γ q.2 q.1=Γ' q.2 q.1) :
    globalHorizontalCoupling Ω Γ=ᶠ[𝓝ˢ K] globalHorizontalCoupling Ω Γ' := by
  apply mem_nhdsSet_iff_forall.mpr
  intro z hz
  filter_upwards [(h z hz).eventually_nhds] with q hq
  exact globalHorizontalCoupling_congr_joint Ω hq

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

theorem physicalParameter_fiber_lower_near {A B : ℕ} {L : ℝ} (hL : 0≤L)
    {z : BaseCurve × PlanePhase (Fin 2)}
    (hz : physicalParameter L (planeMoments z.2)∈Radial.lowerTrapezoid A B) :
    ∀ᶠ q in 𝓝 z,physicalParameter L (planeMoments q.2)∈Radial.lowerTrapezoid A B := by
  have hc : Continuous (fun q : BaseCurve × PlanePhase (Fin 2) => physicalParameter L (planeMoments q.2)) :=
    (physicalParameter_smooth L).continuous.comp (planeMoments_smooth.continuous.comp continuous_snd)
  have h0 := (hc.fst.continuousAt.eventually_lt continuousAt_const hz.2.1)
  have h1 := ((hc.fst.add hc.snd).continuousAt.eventually_lt continuousAt_const hz.2.2.2)
  filter_upwards [h0,h1] with q hq0 hq1
  exact ⟨mul_nonneg hL (planeMoments_nonneg _ 0),hq0,
    mul_nonneg hL (planeMoments_nonneg _ 1),hq1⟩

theorem physicalPrimitive_representative_fiber_germ {A B D S q : ℕ} {c L : ℝ} (hL : 0≤L)
    {bF : Fin q → Moments 2} {cF : Fin q → ℝ}
    (hPS : MapsTo (physicalParameter L) (region bF cF) (Radial.lowerTrapezoid A B))
    {ℓ : ℕ} {Γ : Moments 2 → ManifoldOneForm RealModel BaseCurve}
    (he : ∀ᶠ q in 𝓝ˢ (region bF cF ×ˢ cubicExhaustion ℓ),
      physicalParameter L q.1∈Radial.lowerTrapezoid A B →
      Γ q.1 q.2=physicalPrimitive (A := A) (B := B) D S c L q.1 q.2) :
    ∀ z∈cubicExhaustion ℓ ×ˢ planeRegion bF cF,∀ᶠ q in 𝓝 z,
      Γ (planeMoments q.2) q.1=physicalPrimitive (A := A) (B := B) D S c L (planeMoments q.2) q.1 := by
  intro z hz
  have hn := mem_nhdsSet_iff_forall.mp he (planeMoments z.2,z.1) ⟨hz.2,hz.1⟩
  have hc : Continuous (fun q : BaseCurve × PlanePhase (Fin 2) => (planeMoments q.2,q.1)) :=
    (planeMoments_smooth.continuous.comp continuous_snd).prodMk continuous_fst
  have hi := physicalParameter_fiber_lower_near (A := A) (B := B) (z := z) hL (hPS hz.2)
  filter_upwards [hc.continuousAt.eventually hn,hi] with q hq hqp
  exact hq hqp

attribute [local irreducible] physicalPrimitive

theorem physicalCoupling_representative_near {A B D S q : ℕ} {c L : ℝ} (hL : 0≤L)
    {bF : Fin q → Moments 2} {cF : Fin q → ℝ}
    (hPS : MapsTo (physicalParameter L) (region bF cF) (Radial.lowerTrapezoid A B))
    {ℓ : ℕ} {Γ : Moments 2 → ManifoldOneForm RealModel BaseCurve}
    (he : ∀ᶠ q in 𝓝ˢ (region bF cF ×ˢ cubicExhaustion ℓ),
      physicalParameter L q.1∈Radial.lowerTrapezoid A B →
      Γ q.1 q.2=physicalPrimitive (A := A) (B := B) D S c L q.1 q.2) :
    globalHorizontalCoupling (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)) phaseArea (Γ ∘ planeMoments)=ᶠ[𝓝ˢ (cubicExhaustion ℓ ×ˢ planeRegion bF cF)]
      globalHorizontalCoupling (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)) phaseArea (physicalPrimitive (A := A) (B := B) D S c L ∘ planeMoments) := by
  have hg : ∀ z∈cubicExhaustion ℓ ×ˢ planeRegion bF cF,∀ᶠ q in 𝓝 z,
      Γ (planeMoments q.2) q.1=physicalPrimitive (A := A) (B := B) D S c L (planeMoments q.2) q.1 :=
    physicalPrimitive_representative_fiber_germ hL hPS he
  exact globalHorizontalCoupling_congr_germs (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)) phaseArea (Γ := Γ ∘ planeMoments)
    (Γ' := physicalPrimitive (A := A) (B := B) D S c L ∘ planeMoments) hg

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport
open scoped BigOperators
open MeasureTheory Set
open scoped Pointwise
open MomentPolytope

 theorem exists_positive_common_denominator {ι : Type*} [Fintype ι]
    (q : ι → ℚ) (hq : ∀ i,0≤q i) :
    ∃ L : ℕ,0<L ∧ ∃ k : ι → ℕ,∀ i,(k i:ℝ)=(L:ℝ)*(q i:ℝ) := by
  classical
  let L := ∏ i,(q i).den
  have hL : 0<L := Finset.prod_pos (fun i _ => (q i).den_pos)
  have hd i : (q i).den∣L := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hn i : 0≤(q i).num := Rat.num_nonneg.mpr (hq i)
  let k := fun i => (q i).num.toNat*(L/(q i).den)
  refine ⟨L,hL,k,fun i => ?_⟩
  have hc : ((q i).num.toNat:ℝ)=((q i).num:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hn i)
  have hmul : ((L/(q i).den:ℕ):ℝ)*((q i).den:ℝ)=(L:ℝ) := by
    exact_mod_cast Nat.div_mul_cancel (hd i)
  have hd0 : ((q i).den:ℝ)≠0 := by exact_mod_cast (q i).den_ne_zero
  dsimp only [k]
  rw [Nat.cast_mul,hc,Rat.cast_def]
  field_simp
  nlinarith [hmul]

theorem truncatedSimplex_isClosed (q : ℕ) (h b : ℝ) :
    IsClosed (truncatedSimplex q h b) := by
  have hn : IsClosed {x : ℝ × (Fin q → ℝ) | ∀ i,0≤x.2 i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)
  exact (isClosed_Icc.preimage continuous_fst).inter (hn.inter
    (isClosed_le (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_snd)
      (continuous_const.sub continuous_fst)))

theorem truncatedSimplex_isCompact (q : ℕ) (h b : ℝ) :
    IsCompact (truncatedSimplex q h b) := by
  refine (isCompact_Icc (a := (0,fun _ : Fin q => (0:ℝ)))
    (b := (h,fun _ => b))).of_isClosed_subset (truncatedSimplex_isClosed q h b) ?_
  intro x hx
  refine ⟨⟨hx.1.1,hx.2.1⟩,hx.1.2,fun i => ?_⟩
  have hi := (Finset.single_le_sum (fun j _ => hx.2.1 j) (Finset.mem_univ i)).trans hx.2.2
  linarith [hx.1.1]

theorem truncatedSimplex_fubini (q : ℕ) (h b : ℝ)
    (f : ℝ×(Fin q → ℝ) → ℝ) (hf : ContinuousOn f (truncatedSimplex q h b)) :
    (∫ x in truncatedSimplex q h b, f x) =
      ∫ u in Icc 0 h, ∫ p in momentSimplex q (b-u), f (u,p) := by
  let D := truncatedSimplex q h b
  have hD := (truncatedSimplex_isClosed q h b).measurableSet
  have hi : Integrable (D.indicator f) := (integrable_indicator_iff hD).2
    (hf.integrableOn_compact (truncatedSimplex_isCompact q h b))
  rw [←integral_indicator hD]
  change (∫ x, D.indicator f x ∂(volume.prod volume)) = _
  rw [integral_prod _ hi,←integral_indicator measurableSet_Icc]
  congr 1
  funext u
  by_cases hu : u∈Icc 0 h
  · rw [indicator_of_mem hu,←integral_indicator (momentSimplex_isClosed q (b-u)).measurableSet]
    congr 1
    funext p
    by_cases hp : p∈momentSimplex q (b-u)
    · rw [indicator_of_mem (show (u,p)∈D from ⟨hu,hp⟩),indicator_of_mem hp]
    · rw [indicator_of_notMem (show (u,p)∉D from fun hx => hp hx.2),indicator_of_notMem hp]
  · rw [indicator_of_notMem hu]
    have hz (p : Fin q → ℝ) : D.indicator f (u,p)=0 :=
      indicator_of_notMem (show (u,p)∉D from fun hx => hu hx.1) f
    simp_rw [hz]
    exact integral_zero _ _

theorem integral_truncated_simplex_power (q k : ℕ) {h b : ℝ} (hh : 0≤h) (hhb : h≤b) :
    (∫ x in truncatedSimplex q h b, (b-x.1-∑ i,x.2 i)^k) =
      (k.factorial : ℝ)/((q+k+1).factorial : ℝ)*
        (b^(q+k+1)-(b-h)^(q+k+1)) := by
  rw [truncatedSimplex_fubini q h b _ (by fun_prop)]
  have heq : (∫ u in Icc 0 h, ∫ p in momentSimplex q (b-u), (b-u-∑ i,p i)^k) =
      ∫ u in Icc 0 h, (k.factorial : ℝ)/((q+k).factorial : ℝ)*(b-u)^(q+k) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact integral_simplex_power q k (by linarith [hu.2])
  rw [heq,integral_const_mul,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le hh,
    intervalIntegral.integral_comp_sub_left (fun u : ℝ => u^(q+k)) b,
    sub_zero,integral_pow]
  rw [Nat.factorial_succ (q+k),Nat.cast_mul]
  simp only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_inv_rev]
  ring

theorem volumeReal_truncatedSimplex (q : ℕ) {h b : ℝ} (hh : 0≤h) (hhb : h≤b) :
    volume.real (truncatedSimplex q h b) =
      (b^(q+1)-(b-h)^(q+1))/((q+1).factorial : ℝ) := by
  simpa [div_eq_mul_inv,mul_comm] using integral_truncated_simplex_power q 0 hh hhb

theorem integral_truncated_tent (q : ℕ) {h b : ℝ} (hh : 0≤h) (hhb : h≤b) :
    (∫ x in truncatedSimplex q h b, b-x.1-∑ i,x.2 i) =
      (b^(q+2)-(b-h)^(q+2))/((q+2).factorial : ℝ) := by
  simpa [div_eq_mul_inv,mul_comm] using integral_truncated_simplex_power q 1 hh hhb

theorem integral_truncated_cap (q : ℕ) {h s b : ℝ}
    (hh : 0 ≤ h) (hhs : h ≤ s) (hsb : s ≤ b) :
    (∫ x in truncatedSimplex q h b, max (s-x.1-∑ i,x.2 i) 0) =
      (s^(q+2)-(s-h)^(q+2))/((q+2).factorial : ℝ) := by
  rw [←integral_truncated_tent q hh hhs,
    ←integral_indicator (truncatedSimplex_isClosed q h b).measurableSet,
    ←integral_indicator (truncatedSimplex_isClosed q h s).measurableSet]
  congr 1
  funext x
  by_cases hb : x∈truncatedSimplex q h b
  · rw [indicator_of_mem hb]
    by_cases hs : x∈truncatedSimplex q h s
    · rw [indicator_of_mem hs,max_eq_left]
      linarith [hs.2.2]
    · rw [indicator_of_notMem hs,max_eq_right]
      have hn : ¬ (∑ i,x.2 i) ≤ s-x.1 := fun he => hs ⟨hb.1,hb.2.1,he⟩
      linarith [not_le.1 hn]
  · rw [indicator_of_notMem hb,indicator_of_notMem]
    intro hs
    apply hb
    exact ⟨hs.1,hs.2.1,hs.2.2.trans (by linarith)⟩

theorem integral_truncated_affine {h b d : ℝ} (hh : 0 ≤ h) (hhd : h ≤ d) :
    (∫ x in truncatedSimplex 1 h d, b-x.1-∑ i,x.2 i) =
      (b-d)*(d^2-(d-h)^2)/2+(d^3-(d-h)^3)/6 := by
  have ht : IntegrableOn (fun x : ℝ×(Fin 1→ℝ) => d-x.1-∑ i,x.2 i)
      (truncatedSimplex 1 h d) := by
    apply ContinuousOn.integrableOn_compact (truncatedSimplex_isCompact 1 h d)
    fun_prop
  have hc : IntegrableOn (fun _ : ℝ×(Fin 1→ℝ) => b-d) (truncatedSimplex 1 h d) :=
    continuousOn_const.integrableOn_compact (truncatedSimplex_isCompact 1 h d)
  have heq (x : ℝ×(Fin 1→ℝ)) : b-x.1-∑ i,x.2 i = (b-d)+(d-x.1-∑ i,x.2 i) := by ring
  simp_rw [heq]
  rw [integral_add hc ht,setIntegral_const,integral_truncated_tent 1 hh hhd]
  simp only [smul_eq_mul,volumeReal_truncatedSimplex 1 hh hhd]
  norm_num
  ring

theorem integral_six_model {s b h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hhs : h₁ ≤ s) (hsh : s ≤ h₂) :
    (∫ x in truncatedSimplex 1 h₁ h₂,
      9*(b-x.1-∑ i,x.2 i)-2*max (s-x.1-∑ i,x.2 i) 0) =
      sixModelMean s b h₁ h₂ := by
  have hi (f : ℝ×(Fin 1→ℝ) → ℝ) (hf : Continuous f) :
      IntegrableOn f (truncatedSimplex 1 h₁ h₂) :=
    hf.continuousOn.integrableOn_compact (truncatedSimplex_isCompact 1 h₁ h₂)
  rw [integral_sub (hi _ (by fun_prop)) (hi _ (by fun_prop)),
    integral_const_mul,integral_const_mul,
    integral_truncated_affine hh₁ (hhs.trans hsh),
    integral_truncated_cap 1 hh₁ hhs hsh]
  norm_num [sixModelMean]
  ring

theorem continuous_sixModelMean (s b : ℝ) :
    Continuous (fun h : ℝ×ℝ => sixModelMean s b h.1 h.2) := by
  unfold sixModelMean
  fun_prop

theorem sixModelMean_limit_value (a : ℝ) :
    sixModelMean (1-a) ((2-a)/3) (1-a) ((2-a)/3) = (1-a^3)/6 := by
  unfold sixModelMean
  ring

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

theorem sixModelBounds_nonneg : ∀ ν j,0 ≤ sixModelBounds ν j := by
  intro ν j
  fin_cases ν <;> fin_cases j <;> (first | (simp [sixModelBounds]; all_goals first | (norm_num [sixModelBounds]; done) | rfl | decide) | (norm_num [sixModelBounds]; done) | norm_num [sixModelBounds])

theorem sixModelBounds_le_one : ∀ ν j,sixModelBounds ν j ≤ 1 := by
  intro ν j
  fin_cases ν <;> fin_cases j <;> (first | (simp [sixModelBounds]; all_goals first | (norm_num [sixModelBounds]; done) | rfl | decide) | (norm_num [sixModelBounds]; done) | norm_num [sixModelBounds])

theorem sixModelRegion_eq (h₁ h₂ : ℝ) :
    region sixModelBounds ![h₁,h₂] = (momentHeadTail 1) ⁻¹' truncatedSimplex 1 h₁ h₂ := by
  ext p
  change ((∀ j,0≤p j) ∧ ∀ ν,∑ j,sixModelBounds ν j*p j ≤ ![h₁,h₂] ν) ↔
    (p 0∈Icc 0 h₁ ∧ (fun j : Fin 1 => p j.succ)∈momentSimplex 1 (h₂-p 0))
  simp only [Fin.forall_fin_two,Fin.sum_univ_two,Fin.sum_univ_one,
    sixModelBounds,Matrix.cons_val_zero,Matrix.cons_val_one,momentSimplex,
    mem_ofPred_eq,Fin.forall_fin_one,mem_Icc,one_mul,zero_mul,add_zero]
  norm_num only [Fin.succ_zero_eq_one]
  constructor
  · rintro ⟨⟨h0,h1⟩,hh₁,hh₂⟩
    exact ⟨⟨h0,hh₁⟩,h1,by linarith⟩
  · rintro ⟨⟨h0,hh₁⟩,h1,hh₂⟩
    exact ⟨⟨h0,h1⟩,hh₁,by linarith⟩

theorem sixModelRegion_isCompact (h₁ h₂ : ℝ) :
    IsCompact (region sixModelBounds ![h₁,h₂]) := by
  rw [sixModelRegion_eq]
  exact isCompact_preimage_momentHeadTail 1 (truncatedSimplex_isCompact 1 h₁ h₂)

theorem sixModelRegion_contains_cap {r h₁ h₂ : ℝ} (hr₁ : r ≤ h₁) (hr₂ : r ≤ h₂) :
    momentSimplex 2 r ⊆ region sixModelBounds ![h₁,h₂] := by
  intro p hp
  refine ⟨hp.1,fun ν => ?_⟩
  fin_cases ν
  · change (∑ j,(![1,0] : Fin 2→ℝ) j*p j) ≤ h₁
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,one_mul,zero_mul,add_zero]
    have hs : p 0+p 1 ≤ r := by simpa only [Fin.sum_univ_two] using hp.2
    linarith [hp.1 1]
  · change (∑ j,(![1,1] : Fin 2→ℝ) j*p j) ≤ h₂
    simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,one_mul] using hp.2.trans hr₂

theorem sixModelGap_eq_cappedAffine {ι : Type*} [Fintype ι] (s b : ℝ) (r : ι → ℝ) :
    sixModelGap s b r = cappedAffine (9*b) (fun _ => 9)
      (Sum.elim (fun _ : Unit => s) r) (Sum.elim (fun _ : Unit => 2) (fun _ => 1)) := by
  funext p
  simp only [sixModelGap,sixModelDensity,cappedAffine,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,one_mul,←Finset.mul_sum]
  ring

theorem integral_sixModelDensity {s b h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hhs : h₁ ≤ s) (hsh : s ≤ h₂) :
    (∫ p in region sixModelBounds ![h₁,h₂],sixModelDensity s b p) = sixModelMean s b h₁ h₂ := by
  rw [sixModelRegion_eq]
  have he : sixModelDensity s b = (fun x : ℝ×(Fin 1→ℝ) =>
      9*(b-x.1-∑ j,x.2 j)-2*max (s-x.1-∑ j,x.2 j) 0) ∘ momentHeadTail 1 := by
    funext p
    simp only [sixModelDensity,Fin.sum_univ_succ,Function.comp_apply,momentHeadTail_apply]
    congr 2 <;> ring_nf
  rw [he]
  simp only [Function.comp_apply]
  rw [integral_momentHeadTail 1 (truncatedSimplex_isClosed 1 h₁ h₂).measurableSet
    (fun x : ℝ×(Fin 1→ℝ) => 9*(b-x.1-∑ j,x.2 j)-2*max (s-x.1-∑ j,x.2 j) 0)]
  exact integral_six_model hh₁ hhs hsh

theorem integral_sixModelGap {ι : Type*} [Fintype ι] (r : ι → ℝ) (hr : ∀ i,0 ≤ r i)
    {s b h₁ h₂ : ℝ} (hh₁ : 0 ≤ h₁) (hhs : h₁ ≤ s) (hsh : s ≤ h₂)
    (hr₁ : ∀ i,r i ≤ h₁) (hr₂ : ∀ i,r i ≤ h₂) :
    (∫ p in region sixModelBounds ![h₁,h₂],sixModelGap s b r p) =
      sixModelMean s b h₁ h₂-(∑ i,r i^3)/6 := by
  have hC := sixModelRegion_isCompact h₁ h₂
  have hcap (i : ι) := sixModelRegion_contains_cap (hr₁ i) (hr₂ i)
  unfold sixModelGap
  rw [integral_sub]
  · rw [integral_sixModelDensity hh₁ hhs hsh,
      integral_sum_tents r hr hC.measurableSet (fun _ hp => hp.1) hcap]
    norm_num
  · apply ContinuousOn.integrableOn_compact hC
    unfold sixModelDensity
    fun_prop
  · apply ContinuousOn.integrableOn_compact hC
    fun_prop

theorem sixModelDensity_lower {s b h₁ h₂ : ℝ} (hsh : s ≤ h₂)
    {p : Moments 2} (hp : p ∈ region sixModelBounds ![h₁,h₂]) :
    9*(b-h₂) ≤ sixModelDensity s b p := by
  have hs : (∑ j,p j) ≤ h₂ := by
    have ht := hp.2 1
    simpa [sixModelBounds,Fin.sum_univ_two] using ht
  have hm : max (s-∑ j,p j) 0 ≤ h₂-∑ j,p j := max_le (by linarith) (by linarith)
  unfold sixModelDensity
  linarith

end PackingSufficiencySupport

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators
open Set Function
open MomentPolytope FiniteMoment

 theorem physicalArea_eq_sixModelDensity {L D S : ℕ} (hL : 0<L) {a : ℝ}
    (hD : (D:ℝ)=(L:ℝ)*(2-a)) (hS : (S:ℝ)=(L:ℝ)*(1-a)) :
    physicalArea D S (1/((L:ℝ)*Real.pi)) L=sixModelDensity (1-a) ((2-a)/3) := by
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  funext p
  unfold physicalArea sixModelDensity
  rw [hD,hS,Fin.sum_univ_two]
  have he : (L:ℝ)*(1-a)-((L:ℝ)*p 0+(L:ℝ)*p 1)=(L:ℝ)*((1-a)-(p 0+p 1)) := by ring
  rw [he]
  have hm : max ((L:ℝ)*((1-a)-(p 0+p 1))) 0 = (L:ℝ)*max ((1-a)-(p 0+p 1)) 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg ((1-a)-(p 0+p 1)) 0 hLr.le).symm
  rw [hm]
  field_simp [hLr.ne',Real.pi_ne_zero]
  ring

 theorem physicalParameter_maps_six_region {L A B : ℕ} (hL : 0<L)
    {h₁ h₂ d₁ d₂ : ℝ} (hhd₁ : h₁<d₁) (hhd₂ : h₂<d₂)
    (hA : (A:ℝ)=(L:ℝ)*d₁) (hB : (B:ℝ)=(L:ℝ)*d₂) :
    MapsTo (physicalParameter L) (region sixModelBounds ![h₁,h₂]) (Radial.lowerTrapezoid A B) := by
  intro p hp
  have hn := hp.1
  have hp0 : p 0≤h₁ := by
    simpa [sixModelBounds,Fin.sum_univ_two] using hp.2 0
  have hpt : p 0+p 1≤h₂ := by
    simpa [sixModelBounds,Fin.sum_univ_two] using hp.2 1
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  refine ⟨mul_nonneg hLr.le (hn 0),?_,mul_nonneg hLr.le (hn 1),?_⟩
  · change (L:ℝ)*p 0<(A:ℝ)
    rw [hA]
    exact mul_lt_mul_of_pos_left (hp0.trans_lt hhd₁) hLr
  · change (L:ℝ)*p 0+(L:ℝ)*p 1<(B:ℝ)
    rw [hB,← mul_add]
    exact mul_lt_mul_of_pos_left (hpt.trans_lt hhd₂) hLr

 theorem exists_six_cubic_inner_weights {a d₁ d₂ : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hd₁0 : 0<d₁) (hd₁ : d₁<1-a) (hd₂s : 1-a<d₂) (hd₂ : d₂<(2-a)/3) :
    ∃ L A B D S : ℕ,0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<D ∧ 3*S<D ∧
      (A:ℝ)=(L:ℝ)*(d₁:ℝ) ∧ (B:ℝ)=(L:ℝ)*(d₂:ℝ) ∧
      (D:ℝ)=(L:ℝ)*(2-(a:ℝ)) ∧ (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) := by
  let q : Fin 4 → ℚ := ![1-a,2-a,d₁,d₂]
  have hq : ∀ i,0≤q i := by
    intro i
    fin_cases i <;> dsimp [q] <;> linarith
  obtain ⟨L,hL,k,hk⟩ := exists_positive_common_denominator q hq
  have hS : (k 0:ℝ)=(L:ℝ)*(1-(a:ℝ)) := by simpa [q] using hk 0
  have hD : (k 1:ℝ)=(L:ℝ)*(2-(a:ℝ)) := by simpa [q] using hk 1
  have hA : (k 2:ℝ)=(L:ℝ)*(d₁:ℝ) := by simpa [q] using hk 2
  have hB : (k 3:ℝ)=(L:ℝ)*(d₂:ℝ) := by simpa [q] using hk 3
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  have ha' : (1:ℝ)/2<(a:ℝ) := by
    have hh : (((1:ℚ)/2:ℚ):ℝ)<(a:ℝ) := Rat.cast_lt.mpr ha
    norm_num at hh ⊢
    exact hh
  have ha1' : (a:ℝ)<1 := by exact_mod_cast ha1
  have hd₁0' : 0<(d₁:ℝ) := by exact_mod_cast hd₁0
  have hd₁' : (d₁:ℝ)<1-(a:ℝ) := by exact_mod_cast hd₁
  have hd₂s' : 1-(a:ℝ)<d₂ := by exact_mod_cast hd₂s
  have hdd' : (d₁:ℝ)<d₂ := hd₁'.trans hd₂s'
  have hd₂' : (d₂:ℝ)<(2-(a:ℝ))/3 := by exact_mod_cast hd₂
  refine ⟨L,k 2,k 3,k 1,k 0,hL,?_,?_,?_,?_,?_,?_,?_,hA,hB,hD,hS⟩
  · apply (Nat.cast_pos (α := ℝ)).mp
    rw [hA]
    exact mul_pos hLr (by linarith)
  · apply (Nat.cast_pos (α := ℝ)).mp
    rw [hS]
    exact mul_pos hLr (by linarith)
  · apply (Nat.cast_lt (α := ℝ)).mp
    rw [hA,hS]
    exact mul_lt_mul_of_pos_left hd₁' hLr
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [hA,hB]
    exact mul_le_mul_of_nonneg_left hdd'.le hLr.le
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [hS,hB]
    exact mul_le_mul_of_nonneg_left (by linarith) hLr.le
  · have hm := mul_lt_mul_of_pos_left (show 3*(d₂:ℝ)<2-(a:ℝ) by linarith) hLr
    have hp : 3*(k 3:ℝ)<(k 1:ℝ) := by rw [hB,hD]; nlinarith
    exact_mod_cast hp
  · have hm := mul_lt_mul_of_pos_left (show 3*(1-(a:ℝ))<2-(a:ℝ) by linarith) hLr
    have hp : 3*(k 0:ℝ)<(k 1:ℝ) := by rw [hS,hD]; nlinarith
    exact_mod_cast hp

 theorem exists_six_cubic_inner_weights_large (Q : ℕ) {a d₁ d₂ : ℚ}
    (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hd₁0 : 0<d₁) (hd₁ : d₁<1-a) (hd₂s : 1-a<d₂) (hd₂ : d₂<(2-a)/3) :
    ∃ L A B D S : ℕ,Q<L ∧ 0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<D ∧ 3*S<D ∧
      (A:ℝ)=(L:ℝ)*(d₁:ℝ) ∧ (B:ℝ)=(L:ℝ)*(d₂:ℝ) ∧
      (D:ℝ)=(L:ℝ)*(2-(a:ℝ)) ∧ (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) := by
   obtain ⟨L,A,B,D,S,hL,hA,hS,hAS,hAB,hSB,hBD,hSD,heA,heB,heD,heS⟩ :=
     exists_six_cubic_inner_weights ha ha1 hd₁0 hd₁ hd₂s hd₂
   let M := Q+1
   have hM : 0<M := by dsimp [M]; omega
   refine ⟨M*L,M*A,M*B,M*D,M*S,?_,Nat.mul_pos hM hL,Nat.mul_pos hM hA,
     Nat.mul_pos hM hS,Nat.mul_lt_mul_of_pos_left hAS hM,
     Nat.mul_le_mul_left M hAB,Nat.mul_le_mul_left M hSB,?_,?_,?_,?_,?_,?_⟩
   · have hh := Nat.mul_le_mul_left M (show 1≤L by omega)
     dsimp [M] at hh ⊢
     nlinarith
   · nlinarith [Nat.mul_lt_mul_of_pos_left hBD hM]
   · nlinarith [Nat.mul_lt_mul_of_pos_left hSD hM]
   · push_cast
     rw [heA]
     ring
   · push_cast
     rw [heB]
     ring
   · push_cast
     rw [heD]
     ring
   · push_cast
     rw [heS]
     ring
end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport
open Set
open scoped BigOperators Pointwise
open MomentPolytope

theorem rational_truncation_pair (F : ℝ×ℝ → ℝ) (hF : Continuous F)
    {s₁ s₂ l₁ l₂ c : ℝ} (hl₁ : l₁ < s₁) (hl₂ : l₂ < s₂) (hc : c<F (s₁,s₂)) :
    ∃ h₁ h₂ d₁ d₂ : ℚ,
      l₁<h₁ ∧ h₁<d₁ ∧ (d₁:ℝ) < s₁ ∧
      l₂<h₂ ∧ h₂<d₂ ∧ (d₂:ℝ) < s₂ ∧ c<F (h₁,h₂) := by
  let U : Set (Fin 2 → ℝ) := {p | l₁<p 0 ∧ l₂<p 1 ∧ c<F (p 0,p 1)}
  have hU : IsOpen U := (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_lt continuous_const (hF.comp ((continuous_apply 0).prodMk (continuous_apply 1)))))
  let r : Fin 2 → ℝ := ![s₁,s₂]
  have hr : r∈U := ⟨hl₁,hl₂,hc⟩
  obtain ⟨h,hh,hU⟩ := exists_rational_below_in_open hU hr
  obtain ⟨d₁,hd₁,hd₁s⟩ := exists_rat_btwn (hh 0)
  obtain ⟨d₂,hd₂,hd₂s⟩ := exists_rat_btwn (hh 1)
  exact ⟨h 0,h 1,d₁,d₂,hU.1,by exact_mod_cast hd₁,hd₁s,
    hU.2.1,by exact_mod_cast hd₂,hd₂s,hU.2.2⟩

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
-- module Solutions.OAIQ240_BP.BallPacking_Toric_SixModelComparisonData
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped BigOperators Pointwise
open MeasureTheory Set
open MomentPolytope

theorem exists_six_model_comparison_data {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ι → ℝ) (hr : ∀ i,0 < r i) {a : ℝ} (ha : 1/2<a) (_ha1 : a<1)
    (hrs : ∀ i,r i<1-a) (hvol : ∑ i,r i^3<1-a^3) :
    ∃ h₁ c d₁ h₂ d₂ : ℚ, ∃ τ ε : ℝ,
      (∀ i,r i<h₁) ∧ h₁ < c ∧ (c:ℝ)<1-a ∧ 1-a<(d₁:ℝ) ∧ d₁<h₂ ∧
      h₂<d₂ ∧ (d₂:ℝ)<(2-a)/3 ∧ 0<(h₁:ℝ) ∧ 0<(h₂:ℝ) ∧
      0<τ ∧ τ<1 ∧ 0<ε ∧
      (∀ i,momentSimplex 2 (r i) ⊆ τ • region sixModelBounds ![h₁,h₂]) ∧
      ConcaveOn ℝ (region sixModelBounds ![h₁,h₂]) (sixModelGap (1-a) ((2-a)/3) r) ∧
      (0 < ∫ p in region sixModelBounds ![h₁,h₂],sixModelGap (1-a) ((2-a)/3) r p) ∧
      ∀ p ∈ region sixModelBounds ![h₁,h₂], p ∉ τ • region sixModelBounds ![h₁,h₂] →
        ε ≤ sixModelGap (1-a) ((2-a)/3) r p := by
  classical
  let S := Finset.univ.image r
  have hS : S.Nonempty := Finset.image_nonempty.2 Finset.univ_nonempty
  let R := S.max' hS
  have hR (i : ι) : r i ≤ R := Finset.le_max' S (r i) (Finset.mem_image_of_mem r (Finset.mem_univ i))
  have hRs : R<1-a := (Finset.max'_lt_iff S hS).2 (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 hx
    exact hrs i)
  have hRpos : 0<R := (hr (Classical.arbitrary ι)).trans_le (hR _)
  have hsb : 1-a<(2-a)/3 := by linarith
  have hlim : (∑ i,r i^3)/6 < sixModelMean (1-a) ((2-a)/3) (1-a) ((2-a)/3) := by
    rw [sixModelMean_limit_value]
    exact div_lt_div_of_pos_right hvol (by norm_num)
  obtain ⟨h₁,h₂,c,d₂,hRh₁,hch₁,hcs,hsh₂,hhd₂,hd₂,hmean⟩ :=
    rational_truncation_pair (fun h => sixModelMean (1-a) ((2-a)/3) h.1 h.2)
      (continuous_sixModelMean (1-a) ((2-a)/3)) hRs hsb hlim
  obtain ⟨d₁,hsd₁,hd₁h₂⟩ := exists_rat_btwn hsh₂
  have hd₁h₂' : d₁<h₂ := by exact_mod_cast hd₁h₂
  have hh₁ : (0:ℝ)<h₁ := hRpos.trans hRh₁
  have hRh₂ : R<(h₂:ℝ) := hRs.trans hsh₂
  have hh₂ : (0:ℝ)<h₂ := hRpos.trans hRh₂
  have hh₁s : (h₁:ℝ)<1-a := (by exact_mod_cast hch₁ : (h₁:ℝ) < c).trans hcs
  have hh₂b : (h₂:ℝ)<(2-a)/3 := (by exact_mod_cast hhd₂ : (h₂:ℝ)<d₂).trans hd₂
  have hratio : max (R/(h₁:ℝ)) (R/(h₂:ℝ))<1 := max_lt
    ((div_lt_one hh₁).2 hRh₁) ((div_lt_one hh₂).2 hRh₂)
  obtain ⟨τ,hτlo,hτhi⟩ := exists_between hratio
  have hτlo₁ : R/(h₁:ℝ)<τ := (le_max_left _ _).trans_lt hτlo
  have hτlo₂ : R/(h₂:ℝ)<τ := (le_max_right _ _).trans_lt hτlo
  have hτ : 0<τ := (div_pos hRpos hh₁).trans hτlo₁
  have hRτ₁ : R<τ*(h₁:ℝ) := (div_lt_iff₀ hh₁).1 hτlo₁
  have hRτ₂ : R<τ*(h₂:ℝ) := (div_lt_iff₀ hh₂).1 hτlo₂
  let ε := 9*((2-a)/3-(h₂:ℝ))
  have hε : 0<ε := mul_pos (by norm_num) (sub_pos.2 hh₂b)
  have hcap (i : ι) : momentSimplex 2 (r i) ⊆ τ • region sixModelBounds ![h₁,h₂] := by
    apply cap_into_scaled_region _ _ sixModelBounds_le_one hτ
    intro ν
    fin_cases ν
    · exact (hR i).trans hRτ₁.le
    · exact (hR i).trans hRτ₂.le
  refine ⟨h₁,c,d₁,h₂,d₂,τ,ε,fun i => (hR i).trans_lt hRh₁,hch₁,hcs,hsd₁,hd₁h₂',
    hhd₂,hd₂,hh₁,hh₂,hτ,hτhi,hε,hcap,?_,?_,?_⟩
  · rw [sixModelGap_eq_cappedAffine]
    apply concaveOn_cappedAffine _ _ _ _ ?_ (convex_region _ _)
    intro i
    cases i <;> norm_num
  · rw [integral_sixModelGap r (fun i => (hr i).le) hh₁.le hh₁s.le hsh₂.le
      (fun i => (hR i).trans hRh₁.le) (fun i => (hR i).trans hRh₂.le)]
    linarith
  · intro p hp hout
    have hz := sum_caps_zero_outside r (fun _ hp => hp.1) hcap hp hout
    simp only [sixModelGap,hz,sub_zero]
    exact sixModelDensity_lower hsh₂.le hp

end PackingSufficiencySupport

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

 theorem actual_six_cubic_inner_normal_packing_large (Q : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) {a : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hrs : ∀ i,r i<1-(a:ℝ)) (hvol : ∑ i,r i^3<1-(a:ℝ)^3) :
    ∃ L A B D S : ℕ,Q<L ∧ 0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<D ∧ 3*S<D ∧
      (D:ℝ)=(L:ℝ)*(2-(a:ℝ)) ∧ (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) ∧
      ∃ h₁ h₂ : ℚ, (∀ i,r i<h₁) ∧ h₁<h₂ ∧
        (h₁:ℝ)<(A:ℝ)/L ∧ (h₂:ℝ)<(B:ℝ)/L ∧
        ∃ ℓ,∃ φ : Fin N → Ambient 3 → BaseCurve × PlanePhase (Fin 2),
          (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
            (globalHorizontalCoupling phaseArea
              (physicalPrimitive (A := A) (B := B) D S (1/((L:ℝ)*Real.pi)) L ∘ planeMoments)) (φ i)) ∧
          (∀ i,MapsTo (φ i) (closedBall 3 (r' i))
            (interior (cubicExhaustion ℓ ×ˢ planeRegion sixModelBounds ![h₁,h₂]))) ∧
          Pairwise (fun i j => Disjoint (φ i '' closedBall 3 (r' i)) (φ j '' closedBall 3 (r' j))) := by
  have ha' : (1:ℝ)/2<(a:ℝ) := by
    have hh : (((1:ℚ)/2:ℚ):ℝ)<(a:ℝ) := Rat.cast_lt.mpr ha
    norm_num at hh ⊢
    exact hh
  have ha1' : (a:ℝ)<1 := by exact_mod_cast ha1
  obtain ⟨h₁,e,d₁,h₂,d₂,τ,ε,hrh,hhe,hes,hsd,hdh,hhd,hd₂,hh₁,hh₂,hτ,hτ1,hε,
      _hcap,hconc,hmean,houter⟩ := exists_six_model_comparison_data r hr ha' ha1' hrs hvol
  have hsd' : 1-a<d₁ := by exact_mod_cast hsd
  have hd₂' : d₂<(2-a)/3 := by exact_mod_cast hd₂
  obtain ⟨L,A,B,D,S,hQL,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heA,heB,heD,heS⟩ :=
    exists_six_cubic_inner_weights_large Q ha ha1
      (show 0<e by exact_mod_cast (hh₁.trans (show (h₁:ℝ)<e by exact_mod_cast hhe)))
      (show e<1-a by exact_mod_cast hes)
      (hsd'.trans (hdh.trans hhd)) hd₂'
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  have hh₁d : (h₁:ℝ)<d₁ := (show (h₁:ℝ)<e by exact_mod_cast hhe).trans (hes.trans hsd)
  have hh₂d : (h₂:ℝ)<d₂ := by exact_mod_cast hhd
  have hh₁₂ : h₁<h₂ := by
    have hh : (h₁:ℝ)<h₂ := hh₁d.trans (show (d₁:ℝ)<h₂ by exact_mod_cast hdh)
    exact_mod_cast hh
  have hh₁₂' : (h₁:ℝ)<h₂ := by exact_mod_cast hh₁₂
  have hPS := physicalParameter_maps_six_region hL (show (h₁:ℝ)<e by exact_mod_cast hhe) hh₂d heA heB
  have harea := physicalArea_eq_sixModelDensity hL heD heS
  have hsimp i p (hp : ∀ j,0≤p j) (ht : (∑ j,p j) ≤ r i) :
      p∈region sixModelBounds ![(h₁:ℝ),(h₂:ℝ)] :=
    sixModelRegion_contains_cap (hrh i).le ((hrh i).trans hh₁₂').le ⟨hp,ht⟩
  have hface (i : Fin N) (p : Moments 2) (hp : ∀ j,0≤p j) (ht : (∑ j,p j) ≤ r i) ν :
      (∑ j,sixModelBounds ν j*p j)≠![(h₁:ℝ),(h₂:ℝ)] ν := by
    have hs : p 0+p 1 ≤ r i := by simpa only [Fin.sum_univ_two] using ht
    fin_cases ν
    · simp only [sixModelBounds,Fin.sum_univ_two]
      change 1*p 0+0*p 1≠(h₁:ℝ)
      exact ne_of_lt (by linarith [hp 1,hrh i])
    · simp only [sixModelBounds,Fin.sum_univ_two]
      change 1*p 0+1*p 1≠(h₂:ℝ)
      exact ne_of_lt (by simpa only [one_mul] using hs.trans_lt ((hrh i).trans hh₁₂'))
  obtain ⟨ℓ,Γ,_hΓ,he,φ,hφ,hm,hd⟩ := actual_cubic_representative_packing_bp240 hA hS0 hAB hSB hB hS
    (one_div_pos.mpr (mul_pos hLr Real.pi_pos)) sixModelBounds ![(h₁:ℝ),(h₂:ℝ)]
    sixModelBounds_nonneg (by intro ν; fin_cases ν; exact hh₁; exact hh₂)
    (sixModelRegion_isCompact h₁ h₂) hPS r r' hr' hrr hsimp hface
    (by rw [harea]; exact hconc)
    (by rw [harea]; exact hmean) hτ hτ1 hε
    (by rw [harea]; exact houter)
  refine ⟨L,A,B,D,S,hQL,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heD,heS,h₁,h₂,hrh,hh₁₂,?_,?_,ℓ,φ,?_,hm,hd⟩
  · rw [heA,mul_div_cancel_left₀ _ hLr.ne']
    exact_mod_cast hhe
  · rw [heB,mul_div_cancel_left₀ _ hLr.ne']
    exact hh₂d
  · intro i
    exact (hφ i).congr_target_near (fun x hx => interior_subset (hm i hx))
      (physicalCoupling_representative_near hLr.le hPS he)

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_CubicToricAmbient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem ambientWeightedCoefficient_smooth (D m : ℕ) :
    ContDiff ℝ ∞ (ambientWeightedCoefficient D m) :=
  complexAffineLift_smooth.comp ((complexCartesian (ι := Option (Fin 3))).symm.contDiff.comp
    ((affinePhase 3).contDiff.comp ((weightedProjection_contDiff D m).restrict_scalars ℝ)))

 theorem conePolynomial_smooth {A B : ℕ} (D S : ℕ) :
    ContDiff ℝ ∞ (conePolynomial (A := A) (B := B) D S) := by
  apply contDiff_pi.mpr
  intro ij
  change ContDiff ℝ ∞ (fun p : CubicConeTarget => p.2.1^(latticeIndex ij.1).1 *
    p.2.2^(latticeIndex ij.1).2 * ambientWeightedCoefficient (cubicDegree D ij.1) (cubicMarkedOrder S ij.1) p.1 ij.2)
  have hc : ContDiff ℝ ∞ (fun p : CubicConeTarget =>
      ambientWeightedCoefficient (cubicDegree D ij.1) (cubicMarkedOrder S ij.1) p.1 ij.2) :=
    (contDiff_apply ℝ ℂ ij.2).comp
    ((ambientWeightedCoefficient_smooth (cubicDegree D ij.1) (cubicMarkedOrder S ij.1)).comp contDiff_fst)
  exact (((contDiff_snd.fst).pow _).mul ((contDiff_snd.snd).pow _)).mul hc

 theorem cubicNormalCoordinates_smooth (t : ℝ) : ContDiff ℝ ∞ (cubicNormalCoordinates t) :=
  contDiff_fst.prodMk (contDiff_snd.prodMk (((polynomial_contDiff.restrict_scalars ℝ).comp contDiff_fst).const_smul _))

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_CompactDegenerationTransfer
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

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N]

 theorem exists_compact_exact_fibre_embedding_central_into {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {K : Set M} (hK : IsCompact K)
    (hinv : ∀ x∈K,(manifoldExteriorOneForm (Γ 0) x).IsInvertible)
    {U : Set M} (hU : IsOpen U) (hKU : K⊆U)
    {δ : ℝ} (hδ : 0<δ) {A : ℝ × M → N}
    (hA : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ A)
    (hemb : ∀ t∈Ioc (0:ℝ) δ,Topology.IsEmbedding (fun x : U => A (t,x.val)))
    {T : Set N} (hT : IsOpen T) (hinto : MapsTo (fun x => A (0,x)) K T)
    (Ω : ℝ → ManifoldTwoForm F N)
    (hform : ∀ t∈Ioc (0:ℝ) δ,∀ x∈U,
      manifoldExteriorOneForm (Γ t) x=(Ω t (A (t,x))).bilinearComp
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)) :
    ∃ t∈Ioc (0:ℝ) δ,∃ g : M → N,∃ W : Set M,IsOpen W ∧ K⊆W ∧
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
      MapsTo g W T ∧ ∀ x∈W,∀ v w,Ω t (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x w)=manifoldExteriorOneForm (Γ 0) x v w := by
  have hS : IsOpen (A ⁻¹' T) := hT.preimage hA.continuous
  have hKS : ({0}:Set ℝ)×ˢK⊆A ⁻¹' T := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    rcases ht with rfl
    exact hinto hx
  obtain ⟨V,W,hV,hW,h0V,hKW,hVW⟩ := generalized_tube_lemma isCompact_singleton hK hS hKS
  obtain ⟨η,hη,hηV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  let δ' := min δ (η/2)
  have hδ' : 0<δ' := lt_min hδ (by positivity)
  have htδ {t : ℝ} (ht : t∈Ioc (0:ℝ) δ') : t∈Ioc (0:ℝ) δ :=
    ⟨ht.1,ht.2.trans (min_le_left _ _)⟩
  have htV {t : ℝ} (ht : t∈Ioc (0:ℝ) δ') : t∈V := by
    apply hηV
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht.1]
    have h := ht.2.trans (min_le_right δ (η/2))
    linarith
  obtain ⟨t,ht,g,O,hO,hKO,hg,hge,hgT,hgf⟩ :=
    exists_compact_exact_fibre_embedding_into_bp240 hΓ hK hinv (hU.inter hW)
      (fun x hx => ⟨hKU hx,hKW hx⟩) hδ' hA
      (fun t ht => (hemb t (htδ ht)).comp (Topology.IsEmbedding.inclusion inter_subset_left))
      (fun t ht x hx => hVW ⟨htV ht,hx.2⟩) Ω
      (fun t ht x hx => hform t (htδ ht) x hx.1)
  exact ⟨t,htδ ht,g,O,hO,hKO,hg,hge,hgT,hgf⟩

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem cubicAffineDomain_isOpen : IsOpen cubicAffineDomain :=
  (isOpen_ne_fun (continuous_fst.fst) continuous_const).inter
    (isOpen_ne_fun (continuous_fst.snd) continuous_const)

 theorem inclusion_mem_cubicAffineDomain (x : BaseCurve) (z : ℂ) :
    (inclusion x,z)∈cubicAffineDomain :=
  ⟨inclusion_fst_ne_zero x,inclusion_snd_ne_zero x⟩

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

 theorem productForm_isInvertible {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {A : V →L[ℝ] V →L[ℝ] ℝ} (hA : A.IsInvertible) :
    (productForm A).IsInvertible := by
  have he : oneCovectorForm A 1 0=productForm A := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp [oneCovectorForm_apply,productForm_apply,planarArea_apply]
    ring
  rw [←he]
  exact oneCovectorForm_isInvertible hA one_ne_zero 0

 theorem successorStandardForm_isInvertible (m : ℕ) : (successorStandardForm m).IsInvertible :=
  bilinearComp_equiv_isInvertible (complexSplitPhase m) (productForm_isInvertible phaseArea_isInvertible)

 theorem isInvertible_of_bilinearComp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E=Module.finrank ℝ F)
    {A : F →L[ℝ] F →L[ℝ] ℝ} {L : E →L[ℝ] F}
    (h : (A.bilinearComp L L).IsInvertible) : A.IsInvertible := by
  obtain ⟨e,he⟩ := h
  have hL : Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro v hv
    apply e.injective
    change (e : E →L[ℝ] E →L[ℝ] ℝ) v=(e : E →L[ℝ] E →L[ℝ] ℝ) 0
    rw [he]
    ext w
    simp [ContinuousLinearMap.bilinearComp_apply,hv]
  let c : E ≃L[ℝ] F := (L.toLinearMap.linearEquivOfInjective hL hdim).toContinuousLinearEquiv
  have hc : (c : E →L[ℝ] F)=L := by ext v; rfl
  apply (bilinearComp_equiv_isInvertible_iff c).mp
  rw [hc]
  exact ⟨e,he⟩

 theorem FormNeighborhoodEmbedding.target_invertible
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    {K : Set N} {σ : ManifoldTwoForm F N} {Ω : ManifoldTwoForm E M} {f : N → M}
    (hf : FormNeighborhoodEmbedding K σ Ω f) (hdim : Module.finrank ℝ F=Module.finrank ℝ E)
    {x : N} (hx : x∈K) (hσ : (σ x).IsInvertible) : (Ω (f x)).IsInvertible := by
  obtain ⟨U,_hU,hKU,_hs,_he,hform⟩ := hf
  apply isInvertible_of_bilinearComp (E := F) (F := E) hdim
    (L := manifoldMapDifferential (E := E) (F := F) f x)
  have hh : (Ω (f x)).bilinearComp (manifoldMapDifferential (E := E) (F := F) f x)
      (manifoldMapDifferential (E := E) (F := F) f x)=σ x := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact hform x (hKU hx) v w
  rw [hh]
  exact hσ

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_SixLargeCubicPacking
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope
open MvPolynomial
open FiniteMoment.Radial

 theorem actual_six_cubic_inner_polynomial_packing_avoid_axes_large (Q : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) {a : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hrs : ∀ i,r i<1-(a:ℝ)) (hvol : ∑ i,r i^3<1-(a:ℝ)^3) :
    ∃ L A B D S : ℕ,Q<L ∧ 0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<D ∧ 3*S<D ∧
      (D:ℝ)=(L:ℝ)*(2-(a:ℝ)) ∧ (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) ∧
      ∃ t : ℝ,0<t ∧ ∃ f : Fin N → Ambient 3 → CubicAmbient,
        (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
          (cubicAmbientForm (A := A) (B := B) D S (1/((L:ℝ)*Real.pi)) t) (f i)) ∧
        (∀ i,MapsTo (f i) (closedBall 3 (r' i)) cubicAffineDomain) ∧
        Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r' i)) (f j '' closedBall 3 (r' j))) := by
  classical
  obtain ⟨L,A,B,D,S,hQL,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heD,heS,h₁,h₂,_hrh,_hh₁₂,hh₁,hh₂,ℓ,φ,hφ,hm,hd⟩ :=
    actual_six_cubic_inner_normal_packing_large Q r r' hr hr' hrr ha ha1 hrs hvol
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  let K : Set CubicPhysicalSpace := ⋃ i,φ i '' closedBall 3 (r' i)
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hφ i
    exact (closedBall_isCompact 3 (r' i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hPS := physicalParameter_maps_six_region hL hh₁ hh₂
    (show (A:ℝ)=(L:ℝ)*((A:ℝ)/L) by field_simp)
    (show (B:ℝ)=(L:ℝ)*((B:ℝ)/L) by field_simp)
  have hKd (p : CubicPhysicalSpace) (hp : p∈K) :
      physicalParameter L (planeMoments p.2)∈Radial.lowerTrapezoid A B := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    exact hPS (interior_subset (hm i hx)).2
  have hinv (p : CubicPhysicalSpace) (hp : p∈K) :
      (cubicPhysicalForm (A := A) (B := B) D S L p).IsInvertible := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    exact (hφ i).target_invertible (complexSplitPhase 2).toLinearEquiv.finrank_eq hx
      (successorStandardForm_isInvertible 2)
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,hgT,hgform⟩ :=
    exists_actual_cubic_normal_transfer_into_bp240 hA hAB D S hLr hK hKd hinv
      cubicAffineDomain_isOpen inclusion_mem_cubicAffineDomain
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall 3 (r' i))
    (fun _ => successorStandardForm 2) (cubicPhysicalForm (A := A) (B := B) D S L)
    (cubicAmbientForm (A := A) (B := B) D S (1/((L:ℝ)*Real.pi)) t)
    hW g hg.contMDiffOn hgemb hgform φ hφ
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hd
  exact ⟨L,A,B,D,S,hQL,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heD,heS,t,ht,fun i => g ∘ φ i,hf,fun i x hx => hgT (hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)),hdj⟩

 theorem lift_exponents {n J K : ℕ} (hJ : J≤n) (hK : K≤n) :
    liftAlpha n J K+liftGamma n J K=J ∧
    liftAlpha n J K+liftDelta n J K=K ∧
    2*liftBeta n J K+liftGamma n J K+liftDelta n J K=2*n-(J+K) ∧
    liftAlpha n J K+liftBeta n J K+liftGamma n J K+liftDelta n J K=n := by
  dsimp [liftAlpha,liftBeta,liftGamma,liftDelta]
  omega

 theorem quadricLiftMonomial_smooth (n J K : ℕ) :
    ContDiff ℂ ∞ (quadricLiftMonomial n J K) :=
  ((((contDiff_apply ℂ ℂ 0).pow _).mul ((contDiff_apply ℂ ℂ 1).pow _)).mul
    ((contDiff_apply ℂ ℂ 2).pow _)).mul ((contDiff_apply ℂ ℂ 3).pow _)

 theorem quadricLiftMonomial_param {n J K : ℕ} (hJ : J≤n) (hK : K≤n)
    (u v w : ℂ) :
    quadricLiftMonomial n J K (quadricParam u v w)=u^(2*n-(J+K))*v^J*w^K := by
  obtain ⟨heJ,heK,heI,_⟩ := lift_exponents hJ hK
  change (v*w)^liftAlpha n J K*(u^2)^liftBeta n J K*
    (u*v)^liftGamma n J K*(u*w)^liftDelta n J K=_
  calc
    _=u^(2*liftBeta n J K+liftGamma n J K+liftDelta n J K)*
      v^(liftAlpha n J K+liftGamma n J K)*w^(liftAlpha n J K+liftDelta n J K) := by
        simp only [mul_pow,pow_add,pow_mul]
        ring
    _=_ := by rw [heJ,heK,heI]

 theorem quadricLiftPolynomial_smooth (n : ℕ) (q : MvPolynomial (Fin 2) ℂ) :
    ContDiff ℂ ∞ (quadricLiftPolynomial n q) := by
  unfold quadricLiftPolynomial
  exact ContDiff.sum (fun _ _ => contDiff_const.mul (quadricLiftMonomial_smooth _ _ _))

 theorem quadricLiftPolynomial_param {n : ℕ} (q : MvPolynomial (Fin 2) ℂ)
    (h0 : q.degreeOf 0≤n) (h1 : q.degreeOf 1≤n) (v w : ℂ) :
    quadricLiftPolynomial n q (quadricParam 1 v w)=MvPolynomial.eval ![v,w] q := by
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro d hd
  rw [quadricLiftMonomial_param ((MvPolynomial.monomial_le_degreeOf 0 hd).trans h0)
    ((MvPolynomial.monomial_le_degreeOf 1 hd).trans h1)]
  simp [Fin.prod_univ_two]

 theorem planeCubicPolynomial_eval (v w : ℂ) :
    eval ![v,w] planeCubicPolynomial=polynomial (v,w) := by
  simp only [planeCubicPolynomial,map_add,map_mul,map_pow,MvPolynomial.eval_X,MvPolynomial.eval_C]
  change v^2*w+(-1)*(v*w^2)+w+(-2)*v=v*w*(v-w)+w-2*v
  ring

 theorem planeCubicPolynomial_degreeOf (i : Fin 2) : planeCubicPolynomial.degreeOf i≤2 := by
  have h0 : (X 0^2*X 1 : MvPolynomial (Fin 2) ℂ).degreeOf i≤2 := by
    have h := degreeOf_mul_le i (X 0^2 : MvPolynomial (Fin 2) ℂ) (X 1)
    fin_cases i <;> simp [degreeOf_X_pow_of_ne,degreeOf_X] at h ⊢ <;> omega
  have h1 : (C (-1)*(X 0*X 1^2) : MvPolynomial (Fin 2) ℂ).degreeOf i≤2 := by
    apply (degreeOf_C_mul_le _ _ _).trans
    have h := degreeOf_mul_le i (X 0 : MvPolynomial (Fin 2) ℂ) (X 1^2)
    fin_cases i <;> simp [degreeOf_X_pow_of_ne,degreeOf_X] at h ⊢ <;> omega
  have h2 : (X 1 : MvPolynomial (Fin 2) ℂ).degreeOf i≤2 := by
    fin_cases i <;> simp [degreeOf_X]
  have h3 : (C (-2)*X 0 : MvPolynomial (Fin 2) ℂ).degreeOf i≤2 := by
    apply (degreeOf_C_mul_le _ _ _).trans
    fin_cases i <;> simp [degreeOf_X]
  exact (degreeOf_add_le _ _ _).trans (max_le ((degreeOf_add_le _ _ _).trans
    (max_le ((degreeOf_add_le _ _ _).trans (max_le h0 h1)) h2)) h3)

 theorem coefficientPowers_bounds {D m : ℕ} (hm : 2*m≤D) (i : WeightedHomogeneousIndex) :
    (coefficientPowers D m i).1≤D-m ∧ (coefficientPowers D m i).2≤D-m ∧
      (coefficientPowers D m i).1+(coefficientPowers D m i).2≤D := by
  cases i with
  | none => simp [coefficientPowers]
  | some i =>
    cases i with
    | none => simp [coefficientPowers]
    | some i => fin_cases i <;> dsimp [coefficientPowers] <;> omega

 theorem coefficientPolynomial_eval (D m : ℕ) (i : WeightedHomogeneousIndex) (v w : ℂ) :
    eval ![v,w] (coefficientPolynomial D m i)=ambientWeightedCoefficient D m (v,w) i := by
  unfold ambientWeightedCoefficient
  rw [←complexCartesian_affineComplex,ContinuousLinearEquiv.symm_apply_apply]
  simp only [coefficientPolynomial,map_mul,map_pow,MvPolynomial.eval_X]
  cases i with
  | none => simp [coefficientPowers,complexAffineLift]
  | some i =>
    cases i with
    | none => simp [coefficientPowers,complexAffineLift,weightedProjection,affineComplex]
    | some i => fin_cases i <;>
        simp [coefficientPowers,complexAffineLift,weightedProjection,affineComplex]

 theorem coefficientPolynomial_degreeOf {D m : ℕ} (hm : 2*m≤D)
    (i : WeightedHomogeneousIndex) (j : Fin 2) : (coefficientPolynomial D m i).degreeOf j≤D-m := by
  have h := degreeOf_mul_le j (X 0^(coefficientPowers D m i).1 : MvPolynomial (Fin 2) ℂ)
    (X 1^(coefficientPowers D m i).2)
  have hb := coefficientPowers_bounds hm i
  fin_cases j <;> simp [degreeOf_X_pow_of_ne] at h
  · exact h.trans hb.1
  · exact h.trans hb.2.1

 theorem cubicNormalSection_eval (D m k : ℕ) (i : WeightedHomogeneousIndex) (v w : ℂ) :
    eval ![v,w] (cubicNormalSection D m k i)=polynomial (v,w)^k*ambientWeightedCoefficient D m (v,w) i := by
  rw [cubicNormalSection,map_mul,map_pow,planeCubicPolynomial_eval,coefficientPolynomial_eval]

 theorem cubicNormalSection_degreeOf {D m : ℕ} (hm : 2*m≤D) (k : ℕ)
    (i : WeightedHomogeneousIndex) (j : Fin 2) : (cubicNormalSection D m k i).degreeOf j≤2*k+(D-m) := by
  exact (degreeOf_mul_le _ _ _).trans (add_le_add
    ((degreeOf_pow_le _ _ _).trans ((Nat.mul_le_mul_left k (planeCubicPolynomial_degreeOf j)).trans_eq (Nat.mul_comm k 2)))
    (coefficientPolynomial_degreeOf hm i j))

 theorem cubic_lift_integer_bounds {L S k₁ k₂ : ℕ} (hS : 2*S<L) (hk₁ : k₁<S)
    (hk : 3*(k₁+k₂)<L+S) :
    2*(S-(k₁+k₂))≤L+S-3*(k₁+k₂) ∧
    2*k₂+(L+S-3*(k₁+k₂)-(S-(k₁+k₂)))≤L-2*k₁ ∧
    L-S-k₁≤L-2*k₁ ∧
    3*k₂+(L+S-3*(k₁+k₂))+(L-S-k₁)≤2*(L-2*k₁) := by omega

 theorem firstQuadric_smooth : ContDiff ℂ ∞ firstQuadric :=
  ((contDiff_apply ℂ ℂ 0).mul (contDiff_apply ℂ ℂ 1)).sub
    ((contDiff_apply ℂ ℂ 2).mul (contDiff_apply ℂ ℂ 3))

 theorem inner_lattice_bounds {L S A B : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (k : TrapezoidWeight A B) :
    2*cubicMarkedOrder S k ≤ cubicDegree (L+S) k ∧
    2*(latticeIndex k).2+(cubicDegree (L+S) k-cubicMarkedOrder S k)≤L-2*(latticeIndex k).1 ∧
    L-S-(latticeIndex k).1≤L-2*(latticeIndex k).1 ∧
    3*(latticeIndex k).2+cubicDegree (L+S) k+(L-S-(latticeIndex k).1)≤2*(L-2*(latticeIndex k).1) := by
  have hk1 : (latticeIndex k).1<S := by
    have h := k.property.1
    change k.val.1.val<S
    omega
  have hk : 3*((latticeIndex k).1+(latticeIndex k).2)<L+S := by
    have h := totalWeight_le k
    change 3*totalWeight k<L+S
    omega
  exact cubic_lift_integer_bounds hS hk1 hk

 theorem liftedSection_smooth {A B : ℕ} (L S : ℕ) (k : TrapezoidWeight A B)
    (i : WeightedHomogeneousIndex) : ContDiff ℂ ∞ (liftedSection L S k i) :=
  (firstQuadric_smooth.pow _).mul (quadricLiftPolynomial_smooth _ _)

 theorem firstQuadricChart_smooth : ContDiff ℂ ∞ firstQuadricChart := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact contDiff_snd
  · exact contDiff_const
  · exact contDiff_fst.fst
  · exact contDiff_fst.snd

 theorem outerTube_smooth : ContDiff ℝ ∞ (fun p : ℝ × CubicAmbient => outerTube p.1 p.2) :=
  contDiff_snd.fst.prodMk ((contDiff_snd.fst.fst.mul contDiff_snd.fst.snd).add
    ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_snd.snd))

 theorem outerTube_firstQuadric (δ : ℝ) (p : CubicAmbient) :
    firstQuadric (firstQuadricChart (outerTube δ p))=(δ:ℂ)*p.2 := by
  simp only [firstQuadric,firstQuadricChart,outerTube,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,mul_one]
  ring

 theorem outerPolynomial_smooth {A B : ℕ} (L S : ℕ) (t δ : ℝ) :
    ContDiff ℂ ∞ (outerPolynomial (A := A) (B := B) L S t δ) := by
  exact contDiff_pi.mpr (fun ki => contDiff_const.mul (liftedSection_smooth _ _ _ _))

 theorem outerConePolynomial_smooth {A B : ℕ} (L S : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (outerConePolynomial (A := A) (B := B) L S t) := by
  apply contDiff_pi.mpr
  intro ki
  exact ((contDiff_snd.snd.pow _).mul contDiff_const).mul
    (((quadricLiftPolynomial_smooth _ _).restrict_scalars ℝ).comp
      ((firstQuadricChart_smooth.restrict_scalars ℝ).comp outerTube_smooth))

 theorem outerConePolynomial_eq {A B : ℕ} (L S : ℕ) (t : ℝ) {δ : ℝ} (hδ : δ≠0)
    (p : CubicAmbient) : outerConePolynomial (A := A) (B := B) L S t (δ,p)=
      outerPolynomial L S t δ (firstQuadricChart (outerTube δ p)) := by
  ext ki
  simp only [outerConePolynomial,outerPolynomial,liftedSection,outerTube_firstQuadric,mul_pow]
  have hδc : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hδ
  rw [show (δ:ℂ)⁻¹^(latticeIndex ki.1).1*(t:ℂ)⁻¹^(latticeIndex ki.1).2 *
      ((δ:ℂ)^(latticeIndex ki.1).1*p.2^(latticeIndex ki.1).1 *
      quadricLiftPolynomial (L-2*(latticeIndex ki.1).1)
        (cubicNormalSection (cubicDegree (L+S) ki.1) (cubicMarkedOrder S ki.1) (latticeIndex ki.1).2 ki.2)
        (firstQuadricChart (outerTube δ p)))=
      ((δ:ℂ)⁻¹*(δ:ℂ))^(latticeIndex ki.1).1 * outerConePolynomial (A := A) (B := B) L S t (δ,p) ki by
        simp only [mul_pow,outerConePolynomial]; ring]
  rw [inv_mul_cancel₀ hδc,one_pow,one_mul]
  rfl

 theorem outerConePolynomial_zero {L S A B : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (t : ℝ) (p : CubicAmbient) :
    outerConePolynomial (A := A) (B := B) L S t (0,p)=
      conePolynomial (L+S) S (cubicNormalCoordinates t p) := by
  ext ki
  obtain ⟨hm,hdeg,_,_⟩ := inner_lattice_bounds hAS hS hB ki.1
  have hd (j : Fin 2) := (cubicNormalSection_degreeOf hm (latticeIndex ki.1).2 ki.2 j).trans hdeg
  have hc : firstQuadricChart (outerTube 0 p)=quadricParam 1 p.1.1 p.1.2 := by
    ext j
    fin_cases j <;> simp [firstQuadricChart,outerTube,quadricParam]
  simp only [outerConePolynomial,hc,quadricLiftPolynomial_param _ (hd 0) (hd 1),cubicNormalSection_eval]
  change _=p.2^(latticeIndex ki.1).1*(t⁻¹ • polynomial p.1)^(latticeIndex ki.1).2*
    ambientWeightedCoefficient (cubicDegree (L+S) ki.1) (cubicMarkedOrder S ki.1) p.1 ki.2
  rw [Complex.real_smul,mul_pow,Complex.ofReal_inv]
  ring

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
 theorem primitivePullback_comp (α : G → G →L[ℝ] ℝ) {f : F → G} {g : E → F}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    primitivePullback (primitivePullback α f) g=primitivePullback α (f ∘ g) := by
  funext x
  unfold primitivePullback
  rw [fderiv_comp x (hf.differentiable (by simp) (g x)) (hg.differentiable (by simp) x)]
  rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem quadricLiftPolynomial_one (n : ℕ) (x : Fin 4 → ℂ) :
    quadricLiftPolynomial n 1 x=x 1^n := by
  classical
  simp [quadricLiftPolynomial,quadricLiftMonomial,liftAlpha,liftBeta,liftGamma,liftDelta]

 theorem outerConePolynomial_vertex {A B : ℕ} (L S : ℕ) (t : ℝ)
    (p : ℝ × CubicAmbient) (k : TrapezoidWeight A B) (hk : Radial.latticeIndex k=(0,0)) :
    outerConePolynomial L S t p (k,none)=1 := by
  simp [outerConePolynomial,hk,cubicNormalSection,coefficientPolynomial,coefficientPowers,
    quadricLiftPolynomial_one,firstQuadricChart]

 theorem outerPolynomial_vertex {A B : ℕ} (L S : ℕ) (t δ : ℝ)
    (p : CubicAmbient) (k : TrapezoidWeight A B) (hk : Radial.latticeIndex k=(0,0)) :
    outerPolynomial L S t δ (firstQuadricChart p) (k,none)=1 := by
  simp [outerPolynomial,liftedSection,hk,cubicNormalSection,coefficientPolynomial,
    coefficientPowers,quadricLiftPolynomial_one,firstQuadricChart]

 theorem outerConePolynomial_nonzero {A B : ℕ} (L S : ℕ) (t : ℝ) (p : ℝ × CubicAmbient) :
    complexCartesian (outerConePolynomial (A := A) (B := B) L S t p)≠0 := by
  obtain ⟨k,hk⟩ := lattice_zero A B
  intro h
  have he := congrFun (complexCartesian.injective (h.trans (map_zero _).symm)) (k,none)
  rw [outerConePolynomial_vertex L S t p k hk] at he
  exact one_ne_zero he

 theorem outerPolynomial_nonzero {A B : ℕ} (L S : ℕ) (t δ : ℝ) (p : CubicAmbient) :
    complexCartesian (outerPolynomial (A := A) (B := B) L S t δ (firstQuadricChart p))≠0 := by
  obtain ⟨k,hk⟩ := lattice_zero A B
  intro h
  have he := congrFun (complexCartesian.injective (h.trans (map_zero _).symm)) (k,none)
  rw [outerPolynomial_vertex L S t δ p k hk] at he
  exact one_ne_zero he

 theorem outerAmbientPrimitive_smooth {A B : ℕ} (L S : ℕ) (c t δ : ℝ) :
    ContDiff ℝ ∞ (outerAmbientPrimitive (A := A) (B := B) L S c t δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact primitivePullback_smoothAt (hopfPrimitive_smoothAt c (outerPolynomial_nonzero L S t δ p))
    ((complexCartesian (ι := TrapezoidWeight A B × WeightedHomogeneousIndex)).contDiff.comp
      (((outerPolynomial_smooth L S t δ).restrict_scalars ℝ).comp
        (firstQuadricChart_smooth.restrict_scalars ℝ))).contDiffAt

 theorem outerConePrimitive_smooth {A B : ℕ} (L S : ℕ) (c t : ℝ) :
    SmoothOneFormFamily (outerConePrimitive (A := A) (B := B) L S c t) := by
  let F : ℝ × CubicAmbient → PlanePhase (TrapezoidWeight A B × WeightedHomogeneousIndex) :=
    complexCartesian ∘ outerConePolynomial L S t
  have hF : ContDiff ℝ ∞ F := complexCartesian.contDiff.comp (outerConePolynomial_smooth L S t)
  have hβ : ContDiff ℝ ∞ (primitivePullback (hopfPrimitive c) F) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact primitivePullback_smoothAt (hopfPrimitive_smoothAt c (outerConePolynomial_nonzero L S t p)) hF.contDiffAt
  have he (p : ℝ × CubicAmbient) : outerConePrimitive (A := A) (B := B) L S c t p.1 p.2=
      (primitivePullback (hopfPrimitive c) F p).comp (ContinuousLinearMap.inr ℝ ℝ CubicAmbient) := by
    have hi : HasFDerivAt (fun x : CubicAmbient => (p.1,x)) (ContinuousLinearMap.inr ℝ ℝ CubicAmbient) p.2 := by
      convert! (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1
      all_goals try with_reducible_and_instances rfl
    have hd := (hF.differentiable (by simp) p).hasFDerivAt.comp p.2 hi
    unfold outerConePrimitive primitivePullback
    rw [show fderiv ℝ (fun x => complexCartesian (outerConePolynomial L S t (p.1,x))) p.2=_ from hd.fderiv]
    rfl
  have hΓ : ContDiff ℝ ∞ (fun p : ℝ × CubicAmbient => outerConePrimitive (A := A) (B := B) L S c t p.1 p.2) := by
    simp_rw [he]
    exact hβ.clm_comp contDiff_const
  intro z
  simpa only [vector_chartOneForm] using hΓ.contDiffOn

 theorem outerConePrimitive_zero {L S A B : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (c t : ℝ) :
    outerConePrimitive (A := A) (B := B) L S c t 0=cubicAmbientPrimitive (A := A) (B := B) (L+S) S c t := by
  have he : (fun p => complexCartesian (outerConePolynomial (A := A) (B := B) L S t (0,p)))=
      (complexCartesian ∘ conePolynomial (L+S) S) ∘ cubicNormalCoordinates t := by
    funext p
    rw [outerConePolynomial_zero hAS hS hB]
    rfl
  unfold outerConePrimitive cubicAmbientPrimitive cubicConePrimitive
  rw [he]
  symm
  exact primitivePullback_comp (hopfPrimitive (ι := TrapezoidWeight A B × WeightedHomogeneousIndex) c)
    (f := complexCartesian ∘ conePolynomial (A := A) (B := B) (L+S) S)
    (g := cubicNormalCoordinates t)
    (complexCartesian.contDiff.comp (conePolynomial_smooth _ _))
    (cubicNormalCoordinates_smooth t)

 theorem outerConePrimitive_positive {A B : ℕ} (L S : ℕ) (c t : ℝ) {δ : ℝ} (hδ : δ≠0) :
    outerConePrimitive (A := A) (B := B) L S c t δ=
      primitivePullback (outerAmbientPrimitive (A := A) (B := B) L S c t δ) (outerTube δ) := by
  have he : (fun p => complexCartesian (outerConePolynomial (A := A) (B := B) L S t (δ,p)))=
      (complexCartesian ∘ outerPolynomial L S t δ ∘ firstQuadricChart) ∘ outerTube δ := by
    funext p
    rw [outerConePolynomial_eq L S t hδ]
    rfl
  unfold outerConePrimitive outerAmbientPrimitive
  rw [he]
  symm
  exact primitivePullback_comp (hopfPrimitive (ι := TrapezoidWeight A B × WeightedHomogeneousIndex) c)
    (f := complexCartesian ∘ outerPolynomial (A := A) (B := B) L S t δ ∘ firstQuadricChart)
    (g := outerTube δ)
    (complexCartesian.contDiff.comp (((outerPolynomial_smooth L S t δ).restrict_scalars ℝ).comp
      (firstQuadricChart_smooth.restrict_scalars ℝ)))
    (outerTube_smooth.comp (contDiff_const.prodMk contDiff_id))

 theorem outerTube_isEmbedding {δ : ℝ} (hδ : δ≠0) : Topology.IsEmbedding (outerTube δ) := by
  let R : CubicAmbient → CubicAmbient := fun p => (p.1,(δ:ℂ)⁻¹*(p.2-p.1.1*p.1.2))
  have hR : Continuous R := continuous_fst.prodMk
    (continuous_const.mul (continuous_snd.sub (continuous_fst.fst.mul continuous_fst.snd)))
  have he : R ∘ outerTube δ=id := by
    funext p
    change (p.1,(δ:ℂ)⁻¹*((p.1.1*p.1.2+(δ:ℂ)*p.2)-p.1.1*p.1.2))=p
    refine Prod.ext ?_ ?_
    · rfl
    change (δ:ℂ)⁻¹*((p.1.1*p.1.2+(δ:ℂ)*p.2)-p.1.1*p.1.2)=p.2
    rw [add_sub_cancel_left,←mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hδ),one_mul]
  apply Topology.IsEmbedding.of_comp
    ((outerTube_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous) hR
  change Topology.IsEmbedding (R ∘ outerTube δ)
  rw [he]
  exact Topology.IsEmbedding.id

 theorem exists_actual_outer_normal_transfer {L S A B : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (c t : ℝ) {K : Set CubicAmbient} (hK : IsCompact K)
    (hKd : K⊆cubicAffineDomain)
    (hinv : ∀ p∈K,(cubicAmbientForm (A := A) (B := B) (L+S) S c t p).IsInvertible) :
    ∃ δ : ℝ,0<δ ∧ ∃ g : CubicAmbient → CubicAmbient,∃ W : Set CubicAmbient,
      IsOpen W ∧ K⊆W ∧ ContDiff ℝ ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
      (∀ x∈W,(g x).2≠0) ∧ ∀ x∈W,∀ v w,
      outerAmbientForm (A := A) (B := B) L S c t δ (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)=
        cubicAmbientForm (A := A) (B := B) (L+S) S c t x v w := by
  have hΓ := outerConePrimitive_smooth (A := A) (B := B) L S c t
  have hΓ0 : ∀ x,manifoldExteriorOneForm (outerConePrimitive (A := A) (B := B) L S c t 0) x=
      cubicAmbientForm (A := A) (B := B) (L+S) S c t x := by
    intro x
    rw [outerConePrimitive_zero hAS hS hB,vector_exteriorOneForm]
    rfl
  have hnondeg (x : CubicAmbient) (hx : x∈K) :
      (manifoldExteriorOneForm (outerConePrimitive (A := A) (B := B) L S c t 0) x).IsInvertible := by
    rw [hΓ0]
    exact hinv x hx
  have hform (δ : ℝ) (hδ : δ∈Ioc (0:ℝ) 1) (x : CubicAmbient) (_hx : x∈(univ : Set CubicAmbient)) :
      manifoldExteriorOneForm (outerConePrimitive (A := A) (B := B) L S c t δ) x=
      (outerAmbientForm (A := A) (B := B) L S c t δ (outerTube δ x)).bilinearComp
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicAmbient) (outerTube δ) x)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicAmbient) (outerTube δ) x) := by
    have hTube : ContDiff ℝ ∞ (outerTube δ) :=
      outerTube_smooth.comp (contDiff_const.prodMk contDiff_id)
    rw [outerConePrimitive_positive L S c t (ne_of_gt hδ.1),vector_exteriorOneForm,
      primitivePullback_exterior (outerAmbientPrimitive_smooth L S c t δ) hTube]
    simp only [outerAmbientForm,manifoldMapDifferential,mfderiv_eq_fderiv]
  have hinto : MapsTo (outerTube 0) K {p : CubicAmbient | p.2≠0} := by
    intro x hx
    have h := hKd hx
    change x.1.1*x.1.2+(0:ℂ)*x.2≠0
    rw [zero_mul,add_zero]
    exact mul_ne_zero h.1 h.2
  have hTubeM : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicAmbient)) 𝓘(ℝ,CubicAmbient) ∞
      (fun p : ℝ×CubicAmbient => outerTube p.1 p.2) := by
    rw [modelWithCornersSelf_prod,chartedSpaceSelf_prod]
    exact outerTube_smooth.contMDiff
  obtain ⟨δ,hδ,g,W,hW,hKW,hg,hgemb,hgT,hgform⟩ :=
    exists_compact_exact_fibre_embedding_central_into hΓ hK hnondeg isOpen_univ (subset_univ K)
      (by norm_num : 0<(1:ℝ)) hTubeM
      (fun δ hδ => (outerTube_isEmbedding (ne_of_gt hδ.1)).comp Topology.IsEmbedding.subtypeVal)
      (isOpen_ne_fun continuous_snd continuous_const) hinto
      (fun δ => outerAmbientForm (A := A) (B := B) L S c t δ) hform
  refine ⟨δ,hδ.1,g,W,hW,hKW,hg.contDiff,hgemb,hgT,?_⟩
  intro x hx v w
  have hh := hgform x hx v w
  rw [hΓ0] at hh
  simp only [mfderiv_eq_fderiv] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_SixLargeQuadricPacking
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

 theorem actual_six_quadric_polynomial_packing_large (Q : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) {a : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hrs : ∀ i,r i<1-(a:ℝ)) (hvol : ∑ i,r i^3<1-(a:ℝ)^3) :
    ∃ L A B S : ℕ,Q<L ∧ 0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<L+S ∧ 2*S<L ∧
      (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) ∧
      ∃ t δ : ℝ,0<t ∧ 0<δ ∧ ∃ f : Fin N → Ambient 3 → CubicAmbient,
        (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
          (outerAmbientForm (A := A) (B := B) L S (1/((L:ℝ)*Real.pi)) t δ) (f i)) ∧
        (∀ i,∀ x∈closedBall 3 (r' i),(f i x).2≠0) ∧
        Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r' i)) (f j '' closedBall 3 (r' j))) := by
  classical
  obtain ⟨L,A,B,D,S,hQL,hL,hA,hS0,hAS,hAB,hSB,hB,_hS,heD,heS,t,ht,f,hf,hinto,hd⟩ :=
    actual_six_cubic_inner_polynomial_packing_avoid_axes_large Q r r' hr hr' hrr ha ha1 hrs hvol
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  have hDL : D=L+S := by
    apply Nat.cast_injective (R := ℝ)
    push_cast
    rw [heD,heS]
    ring
  subst D
  have hSL : 2*S<L := by
    have har : (1:ℝ)/2<(a:ℝ) := by
      have hh : (((1:ℚ)/2:ℚ):ℝ)<(a:ℝ) := Rat.cast_lt.mpr ha
      norm_num at hh ⊢
      exact hh
    have hrS : 2*(S:ℝ)<(L:ℝ) := by rw [heS]; nlinarith
    exact_mod_cast hrS
  let K : Set CubicAmbient := ⋃ i,f i '' closedBall 3 (r' i)
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hf i
    exact (closedBall_isCompact 3 (r' i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hKd : K⊆cubicAffineDomain := by
    intro p hp
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    exact hinto i hx
  have hdim : Module.finrank ℝ (Ambient 3)=Module.finrank ℝ CubicAmbient := by
    simp [Ambient,CubicAmbient,PlaneBase,Module.finrank_pi_fintype,Complex.finrank_real_complex]
  have hinv (p : CubicAmbient) (hp : p∈K) :
      (cubicAmbientForm (A := A) (B := B) (L+S) S (1/((L:ℝ)*Real.pi)) t p).IsInvertible := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    exact (hf i).target_invertible hdim hx (successorStandardForm_isInvertible 2)
  obtain ⟨δ,hδ,g,W,hW,hKW,hg,he,hgT,hgform⟩ :=
    exists_actual_outer_normal_transfer hAS hSL hB (1/((L:ℝ)*Real.pi)) t hK hKd hinv
  obtain ⟨hgφ,hdj⟩ := postcompose_form_packing (fun i => closedBall 3 (r' i))
    (fun _ => successorStandardForm 2)
    (cubicAmbientForm (A := A) (B := B) (L+S) S (1/((L:ℝ)*Real.pi)) t)
    (outerAmbientForm (A := A) (B := B) L S (1/((L:ℝ)*Real.pi)) t δ)
    hW g hg.contMDiff.contMDiffOn he (by
      intro x hx v w
      have hh := hgform x hx v w
      simp only [mfderiv_eq_fderiv]
      convert! hh using 1) f hf
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hd
  exact ⟨L,A,B,S,hQL,hL,hA,hS0,hAS,hAB,hSB,hB,hSL,heS,t,δ,ht,hδ,fun i => g ∘ f i,
    hgφ,fun i x hx => hgT (f i x) (hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)),hdj⟩

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_CubicBubbleSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial
open MomentPolytope

 theorem exists_bubble_integer_orders {r a : ℝ} (hr : 0 ≤ r) (hra : r<a) :
     ∃ Q : ℕ,∀ L S : ℕ,Q<L → S≤L → (S:ℝ)=(L:ℝ)*(1-a) →
       ∃ m p N : ℕ,m+1<p ∧ p<L-S ∧ p<N ∧ r<(m+1:ℕ)/(L:ℝ) := by
   obtain ⟨Q,hQ⟩ := exists_nat_gt (3/(a-r))
   refine ⟨Q,?_⟩
   intro L S hQL hSL hS
   have hL : 0<(L:ℝ) := by exact_mod_cast (show 0<L by omega)
   have hδ : 0<a-r := sub_pos.mpr hra
   have hgap : 3<(L:ℝ)*(a-r) := (div_lt_iff₀ hδ).mp (hQ.trans (by exact_mod_cast hQL))
   let m : ℕ := ⌊r*(L:ℝ)⌋₊
   have hmle : (m:ℝ) ≤ r*(L:ℝ) := Nat.floor_le (mul_nonneg hr hL.le)
   have hmlt : r*(L:ℝ)<(m:ℝ)+1 := Nat.lt_floor_add_one _
   have he : ((L-S:ℕ):ℝ)=(L:ℝ)*a := by rw [Nat.cast_sub hSL,hS]; ring
   refine ⟨m,m+2,m+3,by omega,?_,by omega,?_⟩
   · apply (Nat.cast_lt (α := ℝ)).mp
     push_cast
     rw [he]
     nlinarith
   · apply (lt_div_iff₀ hL).mpr
     exact_mod_cast hmlt

 theorem actual_six_standard_packing {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) {a : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hrs : ∀ i,r i<1-(a:ℝ)) (hvol : ∑ i,r i^3<1-(a:ℝ)^3)
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₀a : r₀<(a:ℝ)) :
    HasPacking 3 (N+1) 1 (Fin.cons r₀ r') := by
   obtain ⟨Q,hQ⟩ := exists_bubble_integer_orders hr₀ hr₀a
   obtain ⟨L,A,B,S,hQL,hL,_hA,_hS0,hAS,_hAB,_hSB,hB,hS,heS,t,δ,_ht,_hδ,f,hf,hinto,hd⟩ :=
     actual_six_quadric_polynomial_packing_large Q r r' hr hr' hrr ha ha1 hrs hvol
   obtain ⟨m,p,M,hmp,hp,hM,hcap⟩ := hQ L S hQL (by omega) heS
   exact cubic_bubble_target_packing_bp240 hL hAS hS hB hp hM hmp t δ hcap r' f hf hinto hd

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Packings_ComplementPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open Hamiltonian DiagonalQuadrics DiagonalQuadrics.Explicit
open CubicModel

 theorem hasPacking_six_large_normalized_bp240_oai {N : ℕ} [Nonempty (Fin N)]
    (r : Fin (N+1) → ℝ) (hr : ∀ i,0 < r i) (hlarge : 1/2 ≤ r 0)
    (hvol : ∑ i,r i^3<1) (hpair : ∀ i j,i≠j → r i+r j<1) :
    HasPacking 3 (N+1) 1 r := by
  obtain ⟨q,hq,hqvol,hqpair⟩ := rational_packing_slack 3 1 r (by simpa using hvol) hpair
  have ha : (1:ℚ)/2<q 0 := by
    have hh : (1:ℝ)/2<(q 0:ℝ) := hlarge.trans_lt (hq 0)
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa using hh
  have ha1 : q 0<1 := by
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    have hh := hqpair 0 i.succ (Fin.succ_ne_zero i).symm
    have hp := (hr i.succ).trans (hq i.succ)
    have h : (q 0:ℝ)<1 := by linarith
    exact_mod_cast h
  have htail (i : Fin N) : (q i.succ:ℝ)<1-(q 0:ℝ) := by
    have hh := hqpair 0 i.succ (Fin.succ_ne_zero i).symm
    linarith
  have htvol : ∑ i : Fin N,(q i.succ:ℝ)^3<1-(q 0:ℝ)^3 := by
    rw [Fin.sum_univ_succ] at hqvol
    norm_num at hqvol
    linarith
  have hp := actual_six_standard_packing (fun i => (q i.succ:ℝ)) (fun i => r i.succ)
    (fun i => (hr i.succ).trans (hq i.succ)) (fun i => (hr i.succ).le)
    (fun i => hq i.succ) ha ha1 htail htvol (hr 0).le (hq 0)
  have he : Fin.cons (r 0) (fun i => r i.succ)=r := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rwa [he] at hp

end PackingSufficiencySupport

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.hasPacking_six_large_normalized_bp240_oai := @OAI.PackingSufficiencySupport.hasPacking_six_large_normalized_bp240_oai
