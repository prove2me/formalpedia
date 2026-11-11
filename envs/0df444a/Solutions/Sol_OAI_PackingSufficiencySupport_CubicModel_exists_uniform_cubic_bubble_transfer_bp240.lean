-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.CubicModel.exists_uniform_cubic_bubble_transfer_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:38.279257+00:00
-- url     : https://prove2.me/submissions/5cd19f92-2ef8-46d3-8386-c5344855f040

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_uniform_compact_exact_fibre_embedding_central_into_bp240

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
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem finrank_continuous_dual : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
  rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem bilinear_injective_of_taming {Ω : E →L[ℝ] E →L[ℝ] ℝ} {J : E → E}
    (h : ∀ v, v ≠ 0 → 0 < Ω v (J v)) : Injective Ω := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  change Ω v = 0 at hv
  by_contra hn
  have hp := h v hn
  rw [hv] at hp
  simp at hp

variable [FiniteDimensional ℝ E]

theorem bilinear_isInvertible_of_taming {Ω : E →L[ℝ] E →L[ℝ] ℝ} {J : E → E}
    (h : ∀ v, v ≠ 0 → 0 < Ω v (J v)) : Ω.IsInvertible := by
  have hI := bilinear_injective_of_taming h
  have hS : Surjective Ω :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_continuous_dual (E := E)).symm).mp hI
  exact ⟨(LinearEquiv.ofBijective Ω.toLinearMap ⟨hI,hS⟩).toContinuousLinearEquiv,rfl⟩

end

variable {ι : Type*} [Fintype ι]

theorem affineFSForm_eq_exterior (a : ℝ) :
    (affineFSForm a : PlanePhase ι → _) = euclideanExteriorOneForm (affineFSPrimitive a) := by
  funext z
  ext v w
  exact (affineFSPrimitive_exterior a z v w).symm

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
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
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

theorem complexPairing_re (z v : ι → ℂ) :
    (complexPairing z v).re=phaseDot (complexCartesian z) (complexCartesian v) := by
  simp only [complexPairing,Complex.re_sum,Complex.mul_re,Complex.star_def,
    Complex.conj_re,Complex.conj_im,phaseDot_apply,complexCartesian_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem complexPairing_im (z v : ι → ℂ) :
    (complexPairing z v).im=phaseArea (complexCartesian z) (complexCartesian v) := by
  simp only [complexPairing,Complex.im_sum,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,phaseArea_apply,complexCartesian_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem complexCartesian_I (z : ι → ℂ) :
    complexCartesian (Complex.I • z)=phaseJ (complexCartesian z) := by
  ext i <;> simp [Pi.smul_apply,Complex.mul_re,Complex.mul_im,phaseJ]

theorem complexAffineLift_smooth : ContDiff ℝ ∞ (complexAffineLift (ι := ι)) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | none => exact contDiff_const
  | some i => exact contDiff_apply ℝ ℂ i

theorem complexAffineLift_sq (z : ι → ℂ) :
    phaseSq (complexCartesian (complexAffineLift z))=1+phaseSq (complexCartesian z) := by
  rw [complexCartesian_sq,complexCartesian_sq]
  simp [Fintype.sum_option]

theorem complexCartesian_complex_smul_sq (ζ : ℂ) (y : ι → ℂ) :
    phaseSq (complexCartesian (ζ•y))=Complex.normSq ζ*phaseSq (complexCartesian y) := by
  simp only [complexCartesian_sq,Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum]

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

theorem primitivePullback_smooth {α : F → F →L[ℝ] ℝ} {g : E → F}
    (hα : ContDiff ℝ ∞ α) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (primitivePullback α g) :=
  (hα.comp hg).clm_comp (hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

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

 theorem hopfPrimitive_fderiv (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v w : PlanePhase ι) :
    fderiv ℝ (hopfPrimitive c) z v w=
      c/(2*phaseSq z)*phaseArea v w-c/(phaseSq z)^2*phaseDot z v*phaseArea z w := by
  have hc := ((hasDerivAt_inv (phaseSq_pos hz).ne').comp_hasFDerivAt z
    (phaseSq_hasFDerivAt z)).const_mul (c/2)
  have hc' : HasFDerivAt (fun y : PlanePhase ι => c/(2*phaseSq y))
      ((-c/(phaseSq z)^2) • phaseDot z) z := by
    have he : (fun y : PlanePhase ι => c/(2*phaseSq y))=(fun y => c/2*(phaseSq y)⁻¹) := by
      funext y
      ring
    rw [he]
    apply hc.congr_fderiv
    ext v
    simp only [smul_apply,smul_eq_mul,smul_smul]
    ring
  have hd := hc'.smul (phaseArea (ι := ι)).hasFDerivAt
  rw [show fderiv ℝ (hopfPrimitive c) z=_ from hd.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

 theorem hopfForm_apply (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v w : PlanePhase ι) :
    hopfForm c z v w=c/phaseSq z*phaseArea v w-
      c/(phaseSq z)^2*(phaseDot z v*phaseArea z w-phaseDot z w*phaseArea z v) := by
  simp only [hopfForm,euclideanExteriorOneForm,sub_apply,
    ContinuousLinearMap.flip_apply,hopfPrimitive_fderiv c hz,phaseArea_skew w v]
  ring

 theorem hopfForm_radial (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v : PlanePhase ι) :
    hopfForm c z z v=0 := by
  rw [hopfForm_apply c hz]
  simp only [phaseArea_self,mul_zero,sub_zero,phaseSq]
  field_simp [show phaseDot z z≠0 from (phaseSq_pos hz).ne']
  ring

 theorem hopfForm_circle (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v : PlanePhase ι) :
    hopfForm c z (phaseJ z) v=0 := by
  rw [hopfForm_apply c hz]
  simp only [phaseDot_J_right,phaseArea_J_left,phaseArea_self,neg_zero,zero_mul,
    phaseArea_J_right,phaseSq,zero_sub]
  field_simp [show phaseDot z z≠0 from (phaseSq_pos hz).ne']
  ring

theorem complexCartesian_complex_smul (ζ : ℂ) (z : ι → ℂ) :
    complexCartesian (ζ•z)=ζ.re•complexCartesian z+ζ.im•phaseJ (complexCartesian z) := by
  ext i <;> simp [complexCartesian_apply,Pi.smul_apply,Complex.mul_re,Complex.mul_im,phaseJ] <;> ring

theorem hopfForm_skew (c : ℝ) (z v w : PlanePhase ι) :
    hopfForm c z v w= -hopfForm c z w v := by
  simp only [hopfForm,euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply]
  ring

theorem hopfForm_complex_line (c : ℝ) {z : ι → ℂ} (hz : complexCartesian z≠0)
    (ζ : ℂ) (v : PlanePhase ι) : hopfForm c (complexCartesian z) (complexCartesian (ζ•z)) v=0 := by
  rw [complexCartesian_complex_smul]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul,
    hopfForm_radial c hz,hopfForm_circle c hz,mul_zero,add_zero]

theorem complexPairing_complex_smul (ζ : ℂ) (z v : ι → ℂ) :
    complexPairing (ζ•z) (ζ•v)=(Complex.normSq ζ : ℂ)*complexPairing z v := by
  simp only [complexPairing,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_mul,Complex.star_def,Complex.normSq_eq_conj_mul_self]
  ring

theorem complexCartesian_smul_dot (ζ : ℂ) (z v : ι → ℂ) :
    phaseDot (complexCartesian (ζ•z)) (complexCartesian (ζ•v))=
      Complex.normSq ζ*phaseDot (complexCartesian z) (complexCartesian v) := by
  rw [←complexPairing_re,complexPairing_complex_smul,Complex.mul_re]
  simp [complexPairing_re]

theorem complexCartesian_smul_area (ζ : ℂ) (z v : ι → ℂ) :
    phaseArea (complexCartesian (ζ•z)) (complexCartesian (ζ•v))=
      Complex.normSq ζ*phaseArea (complexCartesian z) (complexCartesian v) := by
  rw [←complexPairing_im,complexPairing_complex_smul,Complex.mul_im]
  simp [complexPairing_im]

theorem hopfForm_complex_scale (c : ℝ) {ζ : ℂ} (hζ : ζ≠0) {z : ι → ℂ}
    (hz : complexCartesian z≠0) (v w : ι → ℂ) :
    hopfForm c (complexCartesian (ζ•z)) (complexCartesian (ζ•v)) (complexCartesian (ζ•w))=
      hopfForm c (complexCartesian z) (complexCartesian v) (complexCartesian w) := by
  have hn : Complex.normSq ζ≠0 := (Complex.normSq_pos.mpr hζ).ne'
  have hz' : complexCartesian (ζ•z)≠0 := by
    intro h
    have hs := complexCartesian_complex_smul_sq ζ z
    simp only [h,phaseSq,map_zero] at hs
    exact (mul_ne_zero hn (phaseSq_pos hz).ne') hs.symm
  rw [hopfForm_apply c hz',hopfForm_apply c hz,complexCartesian_complex_smul_sq,
    complexCartesian_smul_area,complexCartesian_smul_dot,complexCartesian_smul_area,
    complexCartesian_smul_dot,complexCartesian_smul_area]
  field_simp [hn,(phaseSq_pos hz).ne']

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hopfForm_variable_gauge {S : E → ℂ} {G : E → (ι → ℂ)} {x : E}
    (hS : DifferentiableAt ℝ S x) (hG : DifferentiableAt ℝ G x)
    (hSx : S x≠0) (hGx : complexCartesian (G x)≠0) (c : ℝ) (v w : E) :
    hopfForm c (complexCartesian (S x•G x))
      (fderiv ℝ (fun y => complexCartesian (S y•G y)) x v)
      (fderiv ℝ (fun y => complexCartesian (S y•G y)) x w)=
    hopfForm c (complexCartesian (G x))
      (fderiv ℝ (fun y => complexCartesian (G y)) x v)
      (fderiv ℝ (fun y => complexCartesian (G y)) x w) := by
  have hdG := complexCartesian.hasFDerivAt.comp x hG.hasFDerivAt
  have hd := complexCartesian.hasFDerivAt.comp x (hS.hasFDerivAt.smul hG.hasFDerivAt)
  have hz' : complexCartesian (S x•G x)≠0 := by
    intro h
    have hs := complexCartesian_complex_smul_sq (S x) (G x)
    simp only [h,phaseSq,map_zero] at hs
    exact (mul_ne_zero ((Complex.normSq_pos.mpr hSx).ne') (phaseSq_pos hGx).ne') hs.symm
  have hline (u : E) (q : PlanePhase ι) :
      hopfForm c (complexCartesian (S x•G x)) (complexCartesian (fderiv ℝ S x u•G x)) q=0 := by
    have he : fderiv ℝ S x u•G x=(fderiv ℝ S x u/S x)•(S x•G x) := by
      rw [smul_smul,div_mul_cancel₀ _ hSx]
    rw [he]
    exact hopfForm_complex_line c hz' _ q
  have hliner (u : E) (q : PlanePhase ι) :
      hopfForm c (complexCartesian (S x•G x)) q (complexCartesian (fderiv ℝ S x u•G x))=0 := by
    rw [hopfForm_skew,hline,neg_zero]
  rw [show fderiv ℝ (fun y => complexCartesian (S y•G y)) x=_ from hd.fderiv,
    show fderiv ℝ (fun y => complexCartesian (G y)) x=_ from hdG.fderiv]
  simp only [ContinuousLinearMap.comp_apply,add_apply,
    ContinuousLinearMap.smulRight_apply,smul_apply,
    map_add,ContinuousLinearEquiv.coe_coe]
  simp only [hline,hliner,add_zero]
  exact hopfForm_complex_scale c hSx hGx _ _

 variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem complexAffineLift_derivative (z v : ι → ℂ) :
    fderiv ℝ complexAffineLift z v=fun i => match i with
      | none => 0
      | some i => v i := by
  have h : HasFDerivAt (complexAffineLift (ι := ι))
      (ContinuousLinearMap.pi fun i => match i with
        | none => 0
        | some i => (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ)) z := by
    apply hasFDerivAt_pi.mpr
    intro i
    cases i with
    | none => exact hasFDerivAt_const _ _
    | some i => exact (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).hasFDerivAt
  rw [h.fderiv]
  funext i
  cases i <;> rfl

 theorem affineFSPrimitive_hopf (c : ℝ) (z v : ι → ℂ) :
    hopfPrimitive c (complexCartesian (complexAffineLift z))
      (complexCartesian (fderiv ℝ complexAffineLift z v))=
    affineFSPrimitive c (complexCartesian z) (complexCartesian v) := by
  rw [hopfPrimitive,complexAffineLift_sq,smul_apply,smul_eq_mul]
  change _=c/(2*(1+phaseSq (complexCartesian z)))*phaseArea (complexCartesian z) (complexCartesian v)
  congr 1
  rw [← complexPairing_im,← complexPairing_im,complexAffineLift_derivative]
  simp [complexPairing,Fintype.sum_option,complexAffineLift]

end PackingSufficiencySupport.Hamiltonian
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

theorem primitivePullback_exteriorAt {α : F → F →L[ℝ] ℝ} {g : E → F} {x : E}
    (hα : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    euclideanExteriorOneForm (primitivePullback α g) x=
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  have hh := manifold_pullback_exterior_at (α := α) (g := g)
    (by rw [show chartOneForm α (g x)=α from funext (vector_chartOneForm α (g x))]
        simpa only [extChartAt_model_space_eq_id,PartialEquiv.refl_coe,id_eq] using hα) hg.contMDiffAt
  have he : manifoldPullbackOneForm (fun _ => α) g 0=primitivePullback α g := by
    funext z
    simp [manifoldPullbackOneForm,manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback]
  rw [he] at hh
  simpa only [vector_exteriorOneForm,manifoldPullbackOneForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback] using hh

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_SixLargeCubicPacking
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

 theorem lift_order_bounds {n J K r : ℕ} (hJ : J≤n) (hK : K≤n)
    (hr : r≤n) (hJK : J+K+r≤2*n) :
    r≤liftBeta n J K+liftGamma n J K+liftDelta n J K ∧
    liftBeta n J K+liftGamma n J K+liftDelta n J K≤n := by
  dsimp [liftAlpha,liftBeta,liftGamma,liftDelta]
  omega

 theorem quadricLiftMonomial_smooth (n J K : ℕ) :
    ContDiff ℂ ∞ (quadricLiftMonomial n J K) :=
  ((((contDiff_apply ℂ ℂ 0).pow _).mul ((contDiff_apply ℂ ℂ 1).pow _)).mul
    ((contDiff_apply ℂ ℂ 2).pow _)).mul ((contDiff_apply ℂ ℂ 3).pow _)

 theorem quadricLiftPolynomial_smooth (n : ℕ) (q : MvPolynomial (Fin 2) ℂ) :
    ContDiff ℂ ∞ (quadricLiftPolynomial n q) := by
  unfold quadricLiftPolynomial
  exact ContDiff.sum (fun _ _ => contDiff_const.mul (quadricLiftMonomial_smooth _ _ _))

 theorem quadricLiftPolynomial_orders {n r : ℕ} (q : MvPolynomial (Fin 2) ℂ)
    (h0 : q.degreeOf 0≤n) (h1 : q.degreeOf 1≤n)
    (hr : r≤n) (hdeg : q.totalDegree+r≤2*n) (d : Fin 2 →₀ ℕ) (hd : d∈q.support) :
    r≤liftBeta n (d 0) (d 1)+liftGamma n (d 0) (d 1)+liftDelta n (d 0) (d 1) ∧
    liftBeta n (d 0) (d 1)+liftGamma n (d 0) (d 1)+liftDelta n (d 0) (d 1)≤n := by
  apply lift_order_bounds ((MvPolynomial.monomial_le_degreeOf 0 hd).trans h0)
    ((MvPolynomial.monomial_le_degreeOf 1 hd).trans h1) hr
  have h := MvPolynomial.le_totalDegree hd
  have he : d.sum (fun _ e => e)=d 0+d 1 := by
    rw [d.sum_fintype (fun _ e => e) (by simp)]
    simp [Fin.sum_univ_two]
  rw [he] at h
  omega

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

 theorem planeCubicPolynomial_totalDegree : planeCubicPolynomial.totalDegree≤3 := by
  have h0 : (X 0^2*X 1 : MvPolynomial (Fin 2) ℂ).totalDegree≤3 := by
    have h := totalDegree_mul (X 0^2 : MvPolynomial (Fin 2) ℂ) (X 1)
    rw [totalDegree_X_pow,totalDegree_X] at h
    exact h
  have h1 : (C (-1)*(X 0*X 1^2) : MvPolynomial (Fin 2) ℂ).totalDegree≤3 := by
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C,zero_add]
    have h := totalDegree_mul (X 0 : MvPolynomial (Fin 2) ℂ) (X 1^2)
    rw [totalDegree_X,totalDegree_X_pow] at h
    exact h
  have h2 : (X 1 : MvPolynomial (Fin 2) ℂ).totalDegree≤3 := by simp
  have h3 : (C (-2)*X 0 : MvPolynomial (Fin 2) ℂ).totalDegree≤3 := by
    exact (totalDegree_mul _ _).trans (by simp)
  exact (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
    (max_le ((totalDegree_add _ _).trans (max_le h0 h1)) h2)) h3)

 theorem coefficientPowers_bounds {D m : ℕ} (hm : 2*m≤D) (i : WeightedHomogeneousIndex) :
    (coefficientPowers D m i).1≤D-m ∧ (coefficientPowers D m i).2≤D-m ∧
      (coefficientPowers D m i).1+(coefficientPowers D m i).2≤D := by
  cases i with
  | none => simp [coefficientPowers]
  | some i =>
    cases i with
    | none => simp [coefficientPowers]
    | some i => fin_cases i <;> dsimp [coefficientPowers] <;> omega

 theorem coefficientPolynomial_degreeOf {D m : ℕ} (hm : 2*m≤D)
    (i : WeightedHomogeneousIndex) (j : Fin 2) : (coefficientPolynomial D m i).degreeOf j≤D-m := by
  have h := degreeOf_mul_le j (X 0^(coefficientPowers D m i).1 : MvPolynomial (Fin 2) ℂ)
    (X 1^(coefficientPowers D m i).2)
  have hb := coefficientPowers_bounds hm i
  fin_cases j <;> simp [degreeOf_X_pow_of_ne] at h
  · exact h.trans hb.1
  · exact h.trans hb.2.1

 theorem coefficientPolynomial_totalDegree {D m : ℕ} (hm : 2*m≤D) (i : WeightedHomogeneousIndex) :
    (coefficientPolynomial D m i).totalDegree≤D := by
  have h := totalDegree_mul (X 0^(coefficientPowers D m i).1 : MvPolynomial (Fin 2) ℂ)
    (X 1^(coefficientPowers D m i).2)
  simp only [totalDegree_X_pow] at h
  exact h.trans (coefficientPowers_bounds hm i).2.2

 theorem cubicNormalSection_degreeOf {D m : ℕ} (hm : 2*m≤D) (k : ℕ)
    (i : WeightedHomogeneousIndex) (j : Fin 2) : (cubicNormalSection D m k i).degreeOf j≤2*k+(D-m) := by
  exact (degreeOf_mul_le _ _ _).trans (add_le_add
    ((degreeOf_pow_le _ _ _).trans ((Nat.mul_le_mul_left k (planeCubicPolynomial_degreeOf j)).trans_eq (Nat.mul_comm k 2)))
    (coefficientPolynomial_degreeOf hm i j))

 theorem cubicNormalSection_totalDegree {D m : ℕ} (hm : 2*m≤D) (k : ℕ)
    (i : WeightedHomogeneousIndex) : (cubicNormalSection D m k i).totalDegree≤3*k+D := by
  exact (totalDegree_mul _ _).trans (add_le_add
    ((totalDegree_pow _ _).trans ((Nat.mul_le_mul_left k planeCubicPolynomial_totalDegree).trans_eq (Nat.mul_comm k 3)))
    (coefficientPolynomial_totalDegree hm i))

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

 theorem liftedSection_origin_orders {L S A B : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (k : TrapezoidWeight A B) (i : WeightedHomogeneousIndex)
    (d : Fin 2 →₀ ℕ)
    (hd : d∈(cubicNormalSection (cubicDegree (L+S) k) (cubicMarkedOrder S k) (latticeIndex k).2 i).support) :
    L-S≤(latticeIndex k).1+liftBeta (L-2*(latticeIndex k).1) (d 0) (d 1)+
      liftGamma (L-2*(latticeIndex k).1) (d 0) (d 1)+liftDelta (L-2*(latticeIndex k).1) (d 0) (d 1) := by
  obtain ⟨hm,hdeg,hr,horder⟩ := inner_lattice_bounds hAS hS hB k
  have hdj (j : Fin 2) := (cubicNormalSection_degreeOf hm (latticeIndex k).2 i j).trans hdeg
  have htotal := cubicNormalSection_totalDegree hm (latticeIndex k).2 i
  have hh := (quadricLiftPolynomial_orders _ (hdj 0) (hdj 1) hr
    (show (cubicNormalSection (cubicDegree (L+S) k) (cubicMarkedOrder S k) (latticeIndex k).2 i).totalDegree+
      (L-S-(latticeIndex k).1)≤2*(L-2*(latticeIndex k).1) by omega) d hd).1
  have hk := k.property.1
  dsimp [Radial.latticeIndex] at *
  omega

 theorem outerPolynomial_smooth {A B : ℕ} (L S : ℕ) (t δ : ℝ) :
    ContDiff ℂ ∞ (outerPolynomial (A := A) (B := B) L S t δ) := by
  exact contDiff_pi.mpr (fun ki => contDiff_const.mul (liftedSection_smooth _ _ _ _))

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_SixLargeQuadricPacking
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped BigOperators
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cartesianConjugate_smooth {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (cartesianConjugate P) :=
  (complexCartesian (ι := κ)).contDiff.comp (hP.comp (complexCartesian (ι := ι)).symm.contDiff)

end
section

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem cartesianConjugate_fderiv {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℂ ∞ P)
    (z v : PlanePhase ι) : fderiv ℝ (cartesianConjugate P) z v=
      complexCartesian (fderiv ℂ P (complexCartesian.symm z) (complexCartesian.symm v)) := by
  have hh := (hP.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (complexCartesian.symm z)).hasFDerivAt.restrictScalars ℝ
  have hd := complexCartesian.toContinuousLinearMap.hasFDerivAt.comp z
    (hh.comp z (complexCartesian (ι := ι)).symm.hasFDerivAt)
  exact congrArg (fun L => L v) hd.fderiv

 theorem cartesianConjugate_J {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℂ ∞ P)
    (z v : PlanePhase ι) : fderiv ℝ (cartesianConjugate P) z (phaseJ v)=
      phaseJ (fderiv ℝ (cartesianConjugate P) z v) := by
  have hJ : complexCartesian.symm (phaseJ v)=Complex.I•complexCartesian.symm v := by
    apply complexCartesian.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply,complexCartesian_I]
  rw [cartesianConjugate_fderiv hP,cartesianConjugate_fderiv hP,hJ,map_smul,complexCartesian_I]

end

variable {ι : Type} [Fintype ι]

 theorem homogeneousVeronese_smooth (m : ℕ) :
    ContDiff ℂ ∞ (homogeneousVeronese (ι := ι) m) := by
  apply contDiff_pi.mpr
  intro j
  exact contDiff_prod (fun i _ => contDiff_apply ℂ ℂ (j i))

omit [Fintype ι] in
 theorem homogeneousVeronese_homogeneous (m : ℕ) (ζ : ℂ) (z : ι → ℂ) :
    homogeneousVeronese m (ζ•z)=ζ^m•homogeneousVeronese m z := by
  ext j
  simp [homogeneousVeronese,Finset.prod_mul_distrib]

 theorem homogeneousVeronese_sq (m : ℕ) (z : ι → ℂ) :
    phaseSq (complexCartesian (homogeneousVeronese m z))=(phaseSq (complexCartesian z))^m := by
  classical
  simp only [complexCartesian_sq,homogeneousVeronese,map_prod]
  simpa using (Finset.sum_pow' (R := ℝ) Finset.univ (fun i => Complex.normSq (z i)) m).symm

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_AffineHopfRestriction
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
section
variable {ι : Type*} [Fintype ι]

theorem complexAffineLift_hasFDerivAt (z : ι → ℂ) :
    HasFDerivAt complexAffineLift complexAffineTangent z := by
  have he : complexAffineLift (ι := ι)=fun z => complexAffineLift 0+complexAffineTangent z := by
    ext z i
    cases i <;> simp
  rw [he]
  convert! (show HasFDerivAt
    ((fun _ : ι → ℂ => complexAffineLift (0 : ι → ℂ)) + ⇑(complexAffineTangent (ι := ι)))
    complexAffineTangent z from by
    simpa only [zero_add] using
    (hasFDerivAt_const (complexAffineLift (0 : ι → ℂ)) z).add
      (complexAffineTangent (ι := ι)).hasFDerivAt) using 1
  all_goals try with_reducible_and_instances rfl

@[simp] theorem complexAffineLift_fderiv (z : ι → ℂ) :
    fderiv ℝ complexAffineLift z=complexAffineTangent := (complexAffineLift_hasFDerivAt z).fderiv

theorem complexPairing_affine_tangent (z v : ι → ℂ) :
    complexPairing (complexAffineLift z) (complexAffineTangent v)=complexPairing z v := by
  simp [complexPairing,Fintype.sum_option]

theorem complexPairing_tangent_tangent (z v : ι → ℂ) :
    complexPairing (complexAffineTangent z) (complexAffineTangent v)=complexPairing z v := by
  simp [complexPairing,Fintype.sum_option]

theorem hopfForm_affine_restriction (c : ℝ) (z v w : ι → ℂ) :
    hopfForm c (complexCartesian (complexAffineLift z))
      (complexCartesian (complexAffineTangent v)) (complexCartesian (complexAffineTangent w))=
      affineFSForm c (complexCartesian z) (complexCartesian v) (complexCartesian w) := by
  have hn : complexCartesian (complexAffineLift z)≠0 := by
    intro he
    have hh := congrFun (complexCartesian.injective (he.trans (map_zero _).symm)) none
    exact one_ne_zero (by simpa only [complexAffineLift_none,Pi.zero_apply] using hh)
  have hd (u : ι → ℂ) :
      phaseDot (complexCartesian (complexAffineLift z)) (complexCartesian (complexAffineTangent u))=
        phaseDot (complexCartesian z) (complexCartesian u) := by
    rw [←complexPairing_re,complexPairing_affine_tangent,complexPairing_re]
  have ha (u : ι → ℂ) :
      phaseArea (complexCartesian (complexAffineLift z)) (complexCartesian (complexAffineTangent u))=
        phaseArea (complexCartesian z) (complexCartesian u) := by
    rw [←complexPairing_im,complexPairing_affine_tangent,complexPairing_im]
  have ht : phaseArea (complexCartesian (complexAffineTangent v)) (complexCartesian (complexAffineTangent w))=
      phaseArea (complexCartesian v) (complexCartesian w) := by
    rw [←complexPairing_im,complexPairing_tangent_tangent,complexPairing_im]
  rw [hopfForm_apply c hn,affineFSForm_apply,complexAffineLift_sq,hd,ha,hd,ha,ht]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hopfForm_affine_pullback {Z : E → (ι → ℂ)} {x : E}
    (hZ : DifferentiableAt ℝ Z x) (c : ℝ) (v w : E) :
    hopfForm c (complexCartesian (complexAffineLift (Z x)))
      (fderiv ℝ (fun y => complexCartesian (complexAffineLift (Z y))) x v)
      (fderiv ℝ (fun y => complexCartesian (complexAffineLift (Z y))) x w)=
    affineFSForm c (complexCartesian (Z x))
      (fderiv ℝ (fun y => complexCartesian (Z y)) x v)
      (fderiv ℝ (fun y => complexCartesian (Z y)) x w) := by
  have hd := complexCartesian.hasFDerivAt.comp x
    ((complexAffineLift_hasFDerivAt (Z x)).comp x hZ.hasFDerivAt)
  have hdz := complexCartesian.hasFDerivAt.comp x hZ.hasFDerivAt
  rw [show fderiv ℝ (fun y => complexCartesian (complexAffineLift (Z y))) x=_ from hd.fderiv,
    show fderiv ℝ (fun y => complexCartesian (Z y)) x=_ from hdz.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
  exact hopfForm_affine_restriction c (Z x) _ _

end

variable {ι : Type} [Fintype ι]

 theorem bubbleCoordinates_smooth :
    ContDiff ℂ ∞ (fun a : ℂ×(Option ι → ℂ) => bubbleCoordinates a.1 a.2) := by
  apply contDiff_pi.mpr
  rintro (_|i)
  · exact contDiff_fst.mul ((contDiff_apply ℂ ℂ none).comp contDiff_snd)
  · exact (contDiff_apply ℂ ℂ (some i)).comp contDiff_snd

 theorem homogeneousBubble_joint_smooth (L m p : ℕ) :
    ContDiff ℂ ∞ (fun a : ℂ×(Option ι → ℂ) => homogeneousBubble L m p a.1 a.2) := by
  apply contDiff_pi.mpr
  intro j
  exact ((contDiff_fst.pow _).mul (((contDiff_apply ℂ ℂ none).comp contDiff_snd).pow _)).mul
    ((contDiff_apply ℂ ℂ j).comp ((homogeneousVeronese_smooth m).comp bubbleCoordinates_smooth))

omit [Fintype ι] in
 theorem bubbleCoordinates_affine (ε : ℂ) (z : ι → ℂ) :
    bubbleCoordinates ε (complexAffineLift (ε•z))=ε•complexAffineLift z := by
  ext i
  cases i <;> simp [bubbleCoordinates,complexAffineLift,Pi.smul_apply,smul_eq_mul]

omit [Fintype ι] in
 theorem homogeneousBubble_scaled {m p : ℕ} (hp : m≤p) (L : ℕ) (ε : ℂ) (z : ι → ℂ) :
    homogeneousBubble L m p ε (complexAffineLift (ε•z))=ε^p•homogeneousVeronese m (complexAffineLift z) := by
  ext j
  simp only [homogeneousBubble,complexAffineLift_none,one_pow,mul_one,bubbleCoordinates_affine,
    homogeneousVeronese_homogeneous,Pi.smul_apply,smul_eq_mul]
  rw [←mul_assoc,←pow_add,Nat.sub_add_cancel hp]

variable {κ : Type} [Fintype κ]

 theorem bubblePolynomial_joint_smooth (L m p N : ℕ) {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℂ ∞ P) :
    ContDiff ℂ ∞ (fun a : ℂ×(Option ι → ℂ) => bubblePolynomial L m p N P a.1 a.2) := by
  apply contDiff_pi.mpr
  rintro (i|(j|k))
  · exact (contDiff_apply ℂ ℂ i).comp (hP.comp contDiff_snd)
  · exact (contDiff_apply ℂ ℂ j).comp (homogeneousBubble_joint_smooth L m p)
  · exact (contDiff_fst.pow N).mul ((contDiff_apply ℂ ℂ k).comp ((homogeneousVeronese_smooth L).comp contDiff_snd))

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff BigOperators
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem distinguishedResidualTerm_factor {p n k J K : ℕ}
    (hp : p≤k+liftBeta n J K+liftGamma n J K+liftDelta n J K)
    (ε : ℂ) (z : Fin 3 → ℂ) :
    firstQuadric (distinguishedChart ε z)^k * quadricLiftMonomial n J K (distinguishedChart ε z)=
      ε^p*distinguishedResidualTerm p n k J K ε z := by
  have he : firstQuadric (distinguishedChart ε z)=ε*(z 0-ε*z 1*z 2) := by
    simp only [firstQuadric,distinguishedChart,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    ring
  rw [he]
  simp only [quadricLiftMonomial,distinguishedChart,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,one_pow,one_mul,mul_pow,distinguishedResidualTerm]
  have hpw : ε^p*ε^(k+liftBeta n J K+liftGamma n J K+liftDelta n J K-p)=
      ε^k*ε^liftBeta n J K*ε^liftGamma n J K*ε^liftDelta n J K := by
    rw [←pow_add,Nat.add_sub_of_le hp]
    simp only [pow_add]
  calc
    _=(ε^k*ε^liftBeta n J K*ε^liftGamma n J K*ε^liftDelta n J K)*
      ((z 0-ε*z 1*z 2)^k*z 0^liftBeta n J K*z 1^liftGamma n J K*z 2^liftDelta n J K) := by ring
    _=_ := by rw [←hpw]; ring

 theorem outerPolynomial_distinguished_factor {L S A B p : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (hp : p≤L-S) (t δ : ℝ) (ε : ℂ) (z : Fin 3 → ℂ) :
    outerPolynomial (A := A) (B := B) L S t δ (distinguishedChart ε z)=
      ε^p•distinguishedResidualPolynomial p L S t δ ε z := by
  classical
  ext ki
  unfold outerPolynomial liftedSection quadricLiftPolynomial distinguishedResidualPolynomial
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hh := distinguishedResidualTerm_factor
    (hp.trans (liftedSection_origin_orders hAS hS hB ki.1 ki.2 d hd)) ε z
  calc
    _=((δ:ℂ)⁻¹^(latticeIndex ki.1).1*(t:ℂ)⁻¹^(latticeIndex ki.1).2)*
      (cubicNormalSection (cubicDegree (L+S) ki.1) (cubicMarkedOrder S ki.1) (latticeIndex ki.1).2 ki.2).coeff d *
      (firstQuadric (distinguishedChart ε z)^(latticeIndex ki.1).1*
        quadricLiftMonomial (L-2*(latticeIndex ki.1).1) (d 0) (d 1) (distinguishedChart ε z)) := by ring
    _=_ := by rw [hh]; ring

 theorem distinguishedResidualPolynomial_zero {L S A B p : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (hp : p<L-S) (t δ : ℝ) (z : Fin 3 → ℂ) :
    distinguishedResidualPolynomial (A := A) (B := B) p L S t δ 0 z=0 := by
  classical
  ext ki
  unfold distinguishedResidualPolynomial
  rw [Finset.sum_eq_zero]
  · simp
  · intro d hd
    have hh := liftedSection_origin_orders hAS hS hB ki.1 ki.2 d hd
    have he : (latticeIndex ki.1).1+liftBeta (L-2*(latticeIndex ki.1).1) (d 0) (d 1)+
      liftGamma (L-2*(latticeIndex ki.1).1) (d 0) (d 1)+liftDelta (L-2*(latticeIndex ki.1).1) (d 0) (d 1)-p≠0 := by omega
    simp [distinguishedResidualTerm,zero_pow he]

 theorem distinguishedHomogeneousCoordinates_smooth :
     ContDiff ℂ ∞ distinguishedHomogeneousCoordinates := by
   apply contDiff_pi.mpr
   intro i
   fin_cases i <;> exact contDiff_apply ℂ ℂ _

 theorem cubicBubblePolynomial_joint_smooth {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ) :
     ContDiff ℂ ∞ (fun a : ℂ×(Option (Fin 3) → ℂ) =>
       cubicBubblePolynomial (A := A) (B := B) L S m p N t δ a.1 a.2) := by
   exact bubblePolynomial_joint_smooth L m p N
     ((outerPolynomial_smooth L S t δ).comp distinguishedHomogeneousCoordinates_smooth)

 theorem cubicBubblePolynomial_scaled {L S A B m p N : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p≤L-S)
     (hm : m≤p) (hN : p≤N) (t δ : ℝ) (ε : ℂ) (z : Fin 3 → ℂ) :
     cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε (complexAffineLift (ε•z))=
       ε^p•cubicBubbleResidual L S m p N t δ ε z := by
   ext i
   rcases i with (i|(j|k))
   · exact congrFun (outerPolynomial_distinguished_factor hAS hS hB hp t δ ε z) i
   · exact congrFun (homogeneousBubble_scaled hm L ε z) j
   · change ε^N*_=ε^p*(ε^(N-p)*_)
     rw [←mul_assoc,←pow_add,Nat.add_sub_of_le hN]

 theorem cubicBubbleResidual_nonzero {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ)
     (ε : ℂ) (z : Fin 3 → ℂ) :
     cubicBubbleResidual (A := A) (B := B) L S m p N t δ ε z≠0 := by
   intro h
   have hh := congrFun h (Sum.inr (Sum.inl (fun _ => none)))
   change homogeneousVeronese m (complexAffineLift z) (fun _ => none)=0 at hh
   simp [homogeneousVeronese] at hh

 theorem cubicBubbleResidual_zero {L S A B m p N : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (t δ : ℝ) (z : Fin 3 → ℂ) :
     cubicBubbleResidual (A := A) (B := B) L S m p N t δ 0 z=
       Sum.elim (0 : TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ)
         (Sum.elim (homogeneousVeronese m (complexAffineLift z))
           (0 : (Fin L → Option (Fin 3)) → ℂ)) := by
   ext i
   rcases i with (i|(j|k))
   · exact congrFun (distinguishedResidualPolynomial_zero hAS hS hB hp t δ z) i
   · rfl
   · simp [cubicBubbleResidual,zero_pow (show N-p≠0 by omega)]

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open scoped BigOperators
section

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem phasePowerMap_dot {F : PlanePhase ι → PlanePhase κ} (hF : ContDiff ℝ ∞ F)
    {m : ℕ} (hs : ∀ z,phaseSq (F z)=(phaseSq z)^m) (z v : PlanePhase ι) :
    phaseDot (F z) (fderiv ℝ F z v)=(m:ℝ)*(phaseSq z)^(m-1)*phaseDot z v := by
  have h₁ := (phaseSq_hasFDerivAt (F z)).comp z (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt
  have h₂ := (phaseSq_hasFDerivAt z).pow m
  have he : (fun z => phaseSq (F z))=(fun z => (phaseSq z)^m) := funext hs
  change HasFDerivAt (fun x => phaseSq (F x)) _ z at h₁
  rw [he] at h₁
  have hh := congrArg (fun L => L v) (h₁.unique h₂)
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,nsmul_eq_mul] at hh
  nlinarith only [hh]

 theorem phasePowerMap_area {F : PlanePhase ι → PlanePhase κ} (hF : ContDiff ℝ ∞ F)
    {m : ℕ} (hs : ∀ z,phaseSq (F z)=(phaseSq z)^m)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v)) (z v : PlanePhase ι) :
    phaseArea (F z) (fderiv ℝ F z v)=(m:ℝ)*(phaseSq z)^(m-1)*phaseArea z v := by
  have hh := phasePowerMap_dot hF hs z (phaseJ v)
  rw [hJ,phaseDot_J_right,phaseDot_J_right] at hh
  linarith

 theorem homogeneousVeronese_hopf (m : ℕ) (c : ℝ) {z : ι → ℂ} (hz : z≠0) (v : ι → ℂ) :
    hopfPrimitive c (complexCartesian (homogeneousVeronese (m+1) z))
      (fderiv ℝ (fun y => complexCartesian (homogeneousVeronese (m+1) y)) z v)=
      hopfPrimitive ((m+1:ℕ)*c) (complexCartesian z) (complexCartesian v) := by
  let F := cartesianConjugate (homogeneousVeronese (ι := ι) (m+1))
  have hV := homogeneousVeronese_smooth (ι := ι) (m+1)
  have hF : ContDiff ℝ ∞ F := cartesianConjugate_smooth (hV.restrict_scalars ℝ)
  have hs (x : PlanePhase ι) : phaseSq (F x)=(phaseSq x)^(m+1) := by
    change phaseSq (complexCartesian (homogeneousVeronese (m+1) (complexCartesian.symm x)))=_
    rw [homogeneousVeronese_sq,ContinuousLinearEquiv.apply_symm_apply]
  have hJ := cartesianConjugate_J hV
  have ha := phasePowerMap_area hF hs hJ (complexCartesian z) (complexCartesian v)
  have hD : fderiv ℝ F (complexCartesian z) (complexCartesian v)=
      fderiv ℝ (fun y => complexCartesian (homogeneousVeronese (m+1) y)) z v := by
    change fderiv ℝ (fun x : PlanePhase ι => complexCartesian (homogeneousVeronese (m+1) (complexCartesian.symm x))) (complexCartesian z) (complexCartesian v)=_
    have hh := ((complexCartesian.contDiff.comp (hV.restrict_scalars ℝ)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt.comp
      (complexCartesian z) complexCartesian.symm.hasFDerivAt
    simpa only [F,cartesianConjugate,Function.comp_def,ContinuousLinearEquiv.symm_apply_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using congrArg (fun L => L (complexCartesian v)) hh.fderiv
  change phaseArea (complexCartesian (homogeneousVeronese (m+1) z))
    (fderiv ℝ F (complexCartesian z) (complexCartesian v))=_ at ha
  rw [hD] at ha
  have hsz : phaseSq (complexCartesian z)≠0 := (phaseSq_pos (by
    intro h; exact hz (complexCartesian.injective (h.trans (map_zero _).symm)))).ne'
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,homogeneousVeronese_sq,ha,Nat.add_sub_cancel,
    Nat.cast_add,Nat.cast_one]
  rw [pow_succ]
  field_simp [hsz]

end
section

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

omit [Fintype ι] [Fintype κ] [Fintype ν] in
 theorem complexMiddleBlockCLM_apply (z : κ → ℂ) :
     complexMiddleBlockCLM (ι := ι) (ν := ν) z=complexMiddleBlock z := by
   ext i
   rcases i with (i|(k|j)) <;> rfl

 theorem complexMiddleBlock_sq (z : κ → ℂ) :
     phaseSq (complexCartesian (complexMiddleBlock (ι := ι) (ν := ν) z))=
       phaseSq (complexCartesian z) := by
   simp [complexCartesian_sq,complexMiddleBlock,Fintype.sum_sum_type]

 theorem complexMiddleBlock_pairing (z v : κ → ℂ) :
     complexPairing (complexMiddleBlock (ι := ι) (ν := ν) z) (complexMiddleBlock v)=
       complexPairing z v := by
   simp [complexPairing,complexMiddleBlock,Fintype.sum_sum_type]

 theorem complexMiddleBlock_hopf (c : ℝ) (z v : κ → ℂ) :
     hopfPrimitive c (complexCartesian (complexMiddleBlock (ι := ι) (ν := ν) z))
       (complexCartesian (complexMiddleBlock v))=
     hopfPrimitive c (complexCartesian z) (complexCartesian v) := by
   simp only [hopfPrimitive,smul_apply,smul_eq_mul,complexMiddleBlock_sq,
     ←complexPairing_im,complexMiddleBlock_pairing]

 theorem complexMiddleBlock_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
     {F : E → (κ → ℂ)} (hF : ContDiff ℝ ∞ F) (c : ℝ) :
     primitivePullback (hopfPrimitive c)
       (fun z => complexCartesian (complexMiddleBlock (ι := ι) (ν := ν) (F z)))=
     primitivePullback (hopfPrimitive c) (fun z => complexCartesian (F z)) := by
   ext z v
   have hD := complexCartesian.hasFDerivAt.comp z
     ((complexMiddleBlockCLM (ι := ι) (ν := ν)).hasFDerivAt.comp z
       (hF.differentiable (by simp) z).hasFDerivAt)
   have hD' := complexCartesian.hasFDerivAt.comp z (hF.differentiable (by simp) z).hasFDerivAt
   change hopfPrimitive c _ (fderiv ℝ _ z v)=hopfPrimitive c _ (fderiv ℝ _ z v)
   rw [show fderiv ℝ (fun z => complexCartesian (complexMiddleBlock (ι := ι) (ν := ν) (F z))) z=_ from by simpa only [Function.comp_def,complexMiddleBlockCLM_apply] using hD.fderiv,
     show fderiv ℝ (fun z => complexCartesian (F z)) z=_ from hD'.fderiv]
   simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
     complexMiddleBlockCLM_apply] using complexMiddleBlock_hopf (ι := ι) (ν := ν) c (F z) (fderiv ℝ F z v)

 theorem homogeneousVeronese_affinePrimitive (m : ℕ) (c : ℝ) :
     primitivePullback (hopfPrimitive c)
       (fun z : ι → ℂ => complexCartesian (homogeneousVeronese (m+1) (complexAffineLift z)))=
     primitivePullback (affineFSPrimitive ((m+1:ℕ)*c)) complexCartesian := by
   ext z v
   have hV := ((complexCartesian (ι := Fin (m+1) → Option ι)).contDiff.comp
     ((homogeneousVeronese_smooth (m+1)).restrict_scalars ℝ)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (complexAffineLift z)
   have hD := hV.hasFDerivAt.comp z (complexAffineLift_hasFDerivAt z)
   have hz : complexAffineLift z≠0 := by
     intro h
     exact one_ne_zero (congrFun h none)
   change hopfPrimitive c _ (fderiv ℝ _ z v)=_
   rw [show fderiv ℝ (fun z => complexCartesian (homogeneousVeronese (m+1) (complexAffineLift z))) z=_ from hD.fderiv]
   simp only [ContinuousLinearMap.comp_apply]
   change hopfPrimitive c _ (fderiv ℝ (fun y => complexCartesian (homogeneousVeronese (m+1) y))
     (complexAffineLift z) (complexAffineTangent v))=_
   rw [homogeneousVeronese_hopf m c hz]
   rw [←complexAffineLift_fderiv z,affineFSPrimitive_hopf]
   simp only [primitivePullback,ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,
     ContinuousLinearEquiv.coe_coe]

end

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem fibrePrimitivePullback_smooth {α : F → F →L[ℝ] ℝ} {G : ℝ×E → F}
     (hG : ContDiff ℝ ∞ G) (hα : ∀ p,ContDiffAt ℝ ∞ α (G p)) :
     ContDiff ℝ ∞ (fun p : ℝ×E => primitivePullback α (fun x => G (p.1,x)) p.2) := by
   have hβ : ContDiff ℝ ∞ (primitivePullback α G) :=
     contDiff_iff_contDiffAt.mpr (fun p => primitivePullback_smoothAt (hα p) hG.contDiffAt)
   have he (p : ℝ×E) : primitivePullback α (fun x => G (p.1,x)) p.2=
       (primitivePullback α G p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
     have hi : HasFDerivAt (fun x : E => (p.1,x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
       convert! (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1
       all_goals try with_reducible_and_instances rfl
     have hd := (hG.differentiable (by simp) p).hasFDerivAt.comp p.2 hi
     unfold primitivePullback
     rw [show fderiv ℝ (fun x => G (p.1,x)) p.2=_ from hd.fderiv]
     rfl
   simp_rw [he]
   exact hβ.clm_comp contDiff_const

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_DegreeHopfDeformation
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {q : ℝ} {ℓ : ℕ}

theorem hopfCurvaturePullback_comp {G : E' → (ι → ℂ)} {H : E → E'} {x : E}
    (hG : DifferentiableAt ℝ G (H x)) (hH : DifferentiableAt ℝ H x)
    (c : ℝ) (v w : E) :
    hopfCurvaturePullback c (fun y => G (H y)) x v w=
      hopfCurvaturePullback c G (H x) (fderiv ℝ H x v) (fderiv ℝ H x w) := by
  unfold hopfCurvaturePullback
  have hD (u : E) : fderiv ℝ (fun y => complexCartesian (G (H y))) x u=
      fderiv ℝ (fun y => complexCartesian (G y)) (H x) (fderiv ℝ H x u) :=
    congrArg (fun L => L u) (fderiv_comp x (complexCartesian.differentiableAt.comp (H x) hG) hH)
  rw [hD,hD]

end

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']

 theorem degreeAffineForm_apply (q : ℝ) (P : (Option ι → ℂ) → (κ → ℂ)) (c d : ℝ)
    (x v w : ι → ℂ) : degreeAffineForm q P c d x v w=
      degreeHopfCurvaturePullback q P c d complexAffineLift x v w := rfl

 theorem degreeHopfCurvaturePullback_comp {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) {G : E' → (ι → ℂ)} {H : E → E'} {x : E}
    (hG : DifferentiableAt ℝ G (H x)) (hH : DifferentiableAt ℝ H x)
    (q c d : ℝ) (v w : E) :
    degreeHopfCurvaturePullback q P c d (fun y => G (H y)) x v w=
      degreeHopfCurvaturePullback q P c d G (H x) (fderiv ℝ H x v) (fderiv ℝ H x w) := by
  unfold degreeHopfCurvaturePullback
  rw [hopfCurvaturePullback_comp hG hH]
  have h₂ := hopfCurvaturePullback_comp (G := fun y => P (G y))
    ((hP.differentiable (by simp) _).comp (H x) hG) hH c v w
  exact congrArg (fun u : ℝ => (1-q*d)*hopfCurvaturePullback c G (H x)
    (fderiv ℝ H x v) (fderiv ℝ H x w)+d*u) h₂

 theorem degreeAffineForm_pullback {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) {f : E → (ι → ℂ)} {x : E} (hf : DifferentiableAt ℝ f x)
    (q c d : ℝ) (v w : E) :
    degreeAffineForm q P c d (f x) (fderiv ℝ f x v) (fderiv ℝ f x w)=
      degreeHopfCurvaturePullback q P c d (fun y => complexAffineLift (f y)) x v w := by
  rw [degreeAffineForm_apply]
  exact (degreeHopfCurvaturePullback_comp hP (complexAffineLift_smooth.differentiable (by simp) _) hf q c d v w).symm

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem distinguishedResidualTerm_real_smooth (p n k J K : ℕ) :
     ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => distinguishedResidualTerm p n k J K a.1 a.2) := by
   have hε : ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => (a.1:ℂ)) :=
     Complex.ofRealCLM.contDiff.comp contDiff_fst
   have hz (i : Fin 3) : ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => a.2 i) :=
     (contDiff_apply ℝ ℂ i).comp contDiff_snd
   unfold distinguishedResidualTerm
   exact (((hε.pow _).mul (((hz 0).sub ((hε.mul (hz 1)).mul (hz 2))).pow _)).mul
     ((hz 0).pow _ ) |>.mul ((hz 1).pow _)).mul ((hz 2).pow _)

 theorem distinguishedResidualPolynomial_real_smooth {A B : ℕ} (p L S : ℕ) (t δ : ℝ) :
     ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => distinguishedResidualPolynomial (A := A) (B := B) p L S t δ a.1 a.2) := by
   apply contDiff_pi.mpr
   intro ki
   exact contDiff_const.mul (ContDiff.sum (fun _ _ => contDiff_const.mul
     (distinguishedResidualTerm_real_smooth _ _ _ _ _)))

 theorem cubicBubbleResidual_real_smooth {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ) :
     ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) =>
       cubicBubbleResidual (A := A) (B := B) L S m p N t δ a.1 a.2) := by
   apply contDiff_pi.mpr
   rintro (i|(j|k))
   · change ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => distinguishedResidualPolynomial p L S t δ a.1 a.2 i)
     exact (contDiff_apply ℝ ℂ i).comp (distinguishedResidualPolynomial_real_smooth (A := A) (B := B) p L S t δ)
   · change ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => homogeneousVeronese m (complexAffineLift a.2) j)
     exact (contDiff_apply ℝ ℂ j).comp (((homogeneousVeronese_smooth m).restrict_scalars ℝ).comp
       (complexAffineLift_smooth.comp contDiff_snd))
   · change ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => (a.1:ℂ)^(N-p)*homogeneousVeronese L (complexAffineLift ((a.1:ℂ)•a.2)) k)
     have hs : ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => (a.1:ℂ)•a.2) :=
       (Complex.ofRealCLM.contDiff.comp contDiff_fst).smul contDiff_snd
     exact ((Complex.ofRealCLM.contDiff.comp contDiff_fst).pow (N-p)).mul
       ((contDiff_apply ℝ ℂ k).comp (((homogeneousVeronese_smooth L).restrict_scalars ℝ).comp
         (complexAffineLift_smooth.comp hs)))

 theorem cubicBubblePrimitive_joint_smooth {A B : ℕ} (L S m p N : ℕ) (t δ c d : ℝ) :
     ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c d a.1 a.2) := by
   have hF : ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => complexCartesian ((a.1:ℂ)•a.2)) :=
     (complexCartesian (ι := Fin 3)).contDiff.comp
       (show ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => (a.1:ℂ)•a.2) from
         (Complex.ofRealCLM.contDiff.comp contDiff_fst).smul contDiff_snd)
   have hQ := complexCartesian.contDiff.comp (cubicBubbleResidual_real_smooth (A := A) (B := B) L S m p N t δ)
   have hn (a : ℝ×(Fin 3 → ℂ)) :
       complexCartesian (cubicBubbleResidual (A := A) (B := B) L S m p N t δ a.1 a.2)≠0 := by
     intro h
     exact cubicBubbleResidual_nonzero L S m p N t δ _ _
       (complexCartesian.injective (h.trans (map_zero _).symm))
   exact ((fibrePrimitivePullback_smooth hF (fun _ => (affineFSPrimitive_smooth c).contDiffAt)).const_smul (1-(L:ℝ)*d)).add
     ((fibrePrimitivePullback_smooth hQ (fun a => hopfPrimitive_smoothAt c (hn a))).const_smul d)

 theorem cubicBubblePrimitive_zero {L S A B p N : ℕ} (m : ℕ)
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (t δ c d : ℝ) :
     cubicBubblePrimitive (A := A) (B := B) L S (m+1) p N t δ c d 0=
       d•primitivePullback (affineFSPrimitive ((m+1:ℕ)*c)) complexCartesian := by
   have he : (fun z => complexCartesian (cubicBubbleResidual (A := A) (B := B) L S (m+1) p N t δ (0:ℝ) z))=
       (fun z => complexCartesian (complexMiddleBlock
         (homogeneousVeronese (m+1) (complexAffineLift z)))) := by
     funext z
     rw [Complex.ofReal_zero,cubicBubbleResidual_zero hAS hS hB hp hN]
     rfl
   have hF : ContDiff ℝ ∞ (fun z : Fin 3 → ℂ => homogeneousVeronese (m+1) (complexAffineLift z)) :=
     ((homogeneousVeronese_smooth (m+1)).restrict_scalars ℝ).comp complexAffineLift_smooth
   unfold cubicBubblePrimitive
   rw [he,complexMiddleBlock_primitive hF,homogeneousVeronese_affinePrimitive]
   have hz : primitivePullback (affineFSPrimitive (ι := Fin 3) c)
       (fun _ : Fin 3 → ℂ => (0 : PlanePhase (Fin 3)))=0 := by
     ext x v
     simp [primitivePullback]
   simp only [Complex.ofReal_zero,zero_smul,map_zero,hz,smul_zero,zero_add]

 theorem cubicBubblePrimitive_zero_exterior {L S A B p N : ℕ} (m : ℕ)
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (t δ c d : ℝ) (z v w : Fin 3 → ℂ) :
     manifoldExteriorOneForm (cubicBubblePrimitive (A := A) (B := B) L S (m+1) p N t δ c d 0) z v w=
       d*affineFSForm ((m+1:ℕ)*c) (complexCartesian z) (complexCartesian v) (complexCartesian w) := by
   rw [cubicBubblePrimitive_zero m hAS hS hB hp hN,vector_exteriorOneForm,
     euclideanExteriorOneForm_smul d ((primitivePullback_smooth (affineFSPrimitive_smooth ((m+1:ℕ)*c))
       (complexCartesian (ι := Fin 3)).contDiff).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z),
     primitivePullback_exterior (affineFSPrimitive_smooth ((m+1:ℕ)*c)) (complexCartesian (ι := Fin 3)).contDiff,←affineFSForm_eq_exterior]
   simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,
     ContinuousLinearEquiv.fderiv,ContinuousLinearEquiv.coe_coe]

 theorem cubicBubblePrimitive_zero_invertible {L S A B p N : ℕ} (m : ℕ)
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (t δ : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0<d) (z : Fin 3 → ℂ) :
     (manifoldExteriorOneForm (cubicBubblePrimitive (A := A) (B := B) L S (m+1) p N t δ c d 0) z).IsInvertible := by
   apply bilinear_isInvertible_of_taming (J := fun v => complexCartesian.symm (phaseJ (complexCartesian v)))
   intro v hv
   rw [cubicBubblePrimitive_zero_exterior m hAS hS hB hp hN,
     ContinuousLinearEquiv.apply_symm_apply]
   apply mul_pos hd
   apply affineFSForm_positive (mul_pos (by positivity) hc)
   intro he
   apply hv
   exact complexCartesian.injective (he.trans (map_zero _).symm)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem residualPrimitive_exterior {F : E → (ι → ℂ)} {Q : E → (κ → ℂ)}
    (hF : ContDiff ℝ ∞ F) (hQ : ContDiff ℝ ∞ Q) {z : E}
    (hn : complexCartesian (Q z)≠0) (a c d : ℝ) (v w : E) :
    euclideanExteriorOneForm (a•primitivePullback (affineFSPrimitive c) (fun y => complexCartesian (F y))+
      d•primitivePullback (hopfPrimitive c) (fun y => complexCartesian (Q y))) z v w=
      a*affineFSForm c (complexCartesian (F z))
        (fderiv ℝ (fun y => complexCartesian (F y)) z v)
        (fderiv ℝ (fun y => complexCartesian (F y)) z w)+
      d*hopfCurvaturePullback c Q z v w := by
   have hFC := complexCartesian.contDiff.comp hF
   have hQC := complexCartesian.contDiff.comp hQ
   have hα := primitivePullback_smooth (affineFSPrimitive_smooth c) hFC
   have hβ := primitivePullback_smoothAt (g := fun y => complexCartesian (Q y)) (hopfPrimitive_smoothAt c hn) hQC.contDiffAt
   change euclideanExteriorOneForm (a•primitivePullback (affineFSPrimitive (ι := ι) c)
     (complexCartesian ∘ F)+d•primitivePullback (hopfPrimitive (ι := κ) c) (complexCartesian ∘ Q)) z v w=_
   erw [euclideanExteriorOneForm_add ((hα.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).const_smul a)
       ((hβ.differentiableAt (by simp)).const_smul d),
     euclideanExteriorOneForm_smul a (hα.differentiable (by simp) z),
     euclideanExteriorOneForm_smul d (hβ.differentiableAt (by simp)),
     primitivePullback_exterior (affineFSPrimitive_smooth c) hFC,
     primitivePullback_exteriorAt (g := fun y => complexCartesian (Q y)) (hopfPrimitive_smoothAt c hn) hQC.contDiffAt,
     ←affineFSForm_eq_exterior]
   rfl

 theorem residual_degreeAffineForm {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) {F : E → (ι → ℂ)} {Q : E → (κ → ℂ)}
    (hF : ContDiff ℝ ∞ F) (hQ : ContDiff ℝ ∞ Q) {ζ : ℂ} (hζ : ζ≠0)
    (he : (fun y => P (complexAffineLift (F y)))=(fun y => ζ•Q y))
    {z : E} (hn : complexCartesian (Q z)≠0) (q c d : ℝ) (v w : E) :
    degreeAffineForm q P c d (F z) (fderiv ℝ F z v) (fderiv ℝ F z w)=
      (1-q*d)*affineFSForm c (complexCartesian (F z))
        (fderiv ℝ (fun y => complexCartesian (F y)) z v)
        (fderiv ℝ (fun y => complexCartesian (F y)) z w)+
      d*hopfCurvaturePullback c Q z v w := by
   rw [degreeAffineForm_pullback hP (hF.differentiable (by simp) z)]
   unfold degreeHopfCurvaturePullback
   have ha := hopfForm_affine_pullback (hF.differentiable (by simp) z) c v w
   change hopfCurvaturePullback c (fun y => complexAffineLift (F y)) z v w=_ at ha
   rw [ha,he]
   exact congrArg (fun r : ℝ => (1-q*d)*affineFSForm c (complexCartesian (F z))
     (fderiv ℝ (fun y => complexCartesian (F y)) z v)
     (fderiv ℝ (fun y => complexCartesian (F y)) z w)+d*r)
       (hopfForm_variable_gauge (S := fun _ : E => ζ) (differentiableAt_const ζ)
         (hQ.differentiable (by simp) z) hζ hn c v w)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem cubicBubblePolynomial_real_smooth {L S A B m p N : ℕ} (t δ ε : ℝ) :
     ContDiff ℝ ∞ (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) := by
   exact ((cubicBubblePolynomial_joint_smooth L S m p N t δ).comp
       (contDiff_const.prodMk contDiff_id)).restrict_scalars ℝ

 theorem cubicBubbleResidual_fixed_real_smooth {L S A B m p N : ℕ} (t δ ε : ℝ) :
     ContDiff ℝ ∞ (cubicBubbleResidual (A := A) (B := B) L S m p N t δ ε) := by
   exact (cubicBubbleResidual_real_smooth (A := A) (B := B) L S m p N t δ).comp
     (f := fun y : Fin 3 → ℂ => (ε,y)) (contDiff_const.prodMk contDiff_id)

 theorem cubicBubblePrimitive_curvature {L S A B m p N : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p≤L-S)
     (hm : m≤p) (hN : p≤N) (t δ c d : ℝ) {ε : ℝ} (hε : ε≠0)
     (z v w : Fin 3 → ℂ) :
     manifoldExteriorOneForm (cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c d ε) z v w=
       degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) c d
         ((ε:ℂ)•z) (fderiv ℝ (fun y : Fin 3 → ℂ => (ε:ℂ)•y) z v)
           (fderiv ℝ (fun y : Fin 3 → ℂ => (ε:ℂ)•y) z w) := by
   have hscale : ContDiff ℝ ∞ (fun y : Fin 3 → ℂ => (ε:ℂ)•y) := (contDiff_const (c := (ε:ℂ))).smul (contDiff_id (𝕜 := ℝ) (E := Fin 3 → ℂ))
   have hP : ContDiff ℝ ∞ (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) :=
     cubicBubblePolynomial_real_smooth t δ ε
   have hQ : ContDiff ℝ ∞ (cubicBubbleResidual (A := A) (B := B) L S m p N t δ ε) :=
     cubicBubbleResidual_fixed_real_smooth t δ ε
   have hn : complexCartesian (cubicBubbleResidual (A := A) (B := B) L S m p N t δ ε z)≠0 := by
     intro he
     exact cubicBubbleResidual_nonzero L S m p N t δ _ _
       (complexCartesian.injective (he.trans (map_zero _).symm))
   have he : (fun y => cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε
       (complexAffineLift ((ε:ℂ)•y)))=
       (fun y => (ε:ℂ)^p•cubicBubbleResidual L S m p N t δ ε y) := by
     funext y
     exact cubicBubblePolynomial_scaled hAS hS hB hp hm hN t δ ε y
   rw [vector_exteriorOneForm,cubicBubblePrimitive]
   exact (residualPrimitive_exterior hscale hQ hn (1-(L:ℝ)*d) c d v w).trans
     (residual_degreeAffineForm hP hscale hQ
       (pow_ne_zero p (Complex.ofReal_ne_zero.mpr hε)) he hn (L:ℝ) c d v w).symm

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_CompactUniformCentral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial
open scoped Topology
open Set Function Manifold

 theorem cubicBubblePrimitive_coefficient_affine {A B : ℕ} (L S m p N : ℕ) (t δ c d ε : ℝ) :
     cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c d ε=
       cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c 0 ε+
         d•(cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c 1 ε-cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c 0 ε) := by
   simp only [cubicBubblePrimitive]
   module

 theorem cubicBubbleVariable_joint_smooth {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) :
     ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) =>
       cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c (D a.1) a.1 a.2) := by
   have he : (fun a : ℝ×(Fin 3 → ℂ) => cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c (D a.1) a.1 a.2)=
       (fun a : ℝ×(Fin 3 → ℂ) => cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c 0 a.1 a.2+
         D a.1•(cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c 1 a.1 a.2-cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c 0 a.1 a.2)) := by
     funext a
     exact congrFun (cubicBubblePrimitive_coefficient_affine (A := A) (B := B) L S m p N t δ c (D a.1) a.1) a.2
   rw [he]
   exact (cubicBubblePrimitive_joint_smooth (A := A) (B := B) L S m p N t δ c 0).add
     ((hD.comp contDiff_fst).smul ((cubicBubblePrimitive_joint_smooth (A := A) (B := B) L S m p N t δ c 1).sub
       (cubicBubblePrimitive_joint_smooth (A := A) (B := B) L S m p N t δ c 0)))

 theorem cubicBubbleVariable_smooth_family {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) :
     SmoothOneFormFamily (fun ε => cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c (D ε) ε) := by
   intro x
   simpa only [vector_chartOneForm] using (cubicBubbleVariable_joint_smooth (A := A) (B := B) L S m p N t δ c hD).contDiffOn

 theorem exists_uniform_cubic_bubble_transfer_bp240_oai {L S A B p N : ℕ} (m : ℕ)
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (hm : m+1≤p) (t δ : ℝ) {c : ℝ} (hc : 0 < c)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : 0<D 0)
     {K : Set (Fin 3 → ℂ)} (hK : IsCompact K)
     {T : Set (Fin 3 → ℂ)} (hT : IsOpen T) (h0T : (0 : Fin 3 → ℂ)∈T)
     {η : ℝ} (hη : 0<η) :
     ∃ τ>0,τ≤η ∧ ∀ ε∈Ioc (0:ℝ) τ,∃ g : (Fin 3 → ℂ) → (Fin 3 → ℂ),∃ W,
       IsOpen W ∧ K⊆W ∧ ContDiff ℝ ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
       MapsTo g W T ∧ ∀ x∈W,∀ v w,
         degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)
           (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)=
         D 0*affineFSForm ((m+1:ℕ)*c) (complexCartesian x) (complexCartesian v) (complexCartesian w) := by
   have hscale : ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => (a.1:ℂ)•a.2) :=
     (Complex.ofRealCLM.contDiff.comp contDiff_fst).smul contDiff_snd
   have hscaleM : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Fin 3 → ℂ)) 𝓘(ℝ,Fin 3 → ℂ) ∞
       (fun a : ℝ×(Fin 3 → ℂ) => (a.1:ℂ)•a.2) := by
     rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod]
     exact hscale.contMDiff
   have hemb (ε : ℝ) (hε : ε∈Ioc (0:ℝ) η) :
       Topology.IsEmbedding (fun x : (univ : Set (Fin 3 → ℂ)) => (ε:ℂ)•x.val) :=
     (Homeomorph.smulOfNeZero (α := Fin 3 → ℂ) (ε:ℂ) (Complex.ofReal_ne_zero.mpr hε.1.ne')).isEmbedding.comp
       Topology.IsEmbedding.subtypeVal
   let Γ := fun ε : ℝ => cubicBubblePrimitive (A := A) (B := B) L S (m+1) p N t δ c (D ε) ε
   let Ω := fun ε : ℝ => degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)
   have hform (ε : ℝ) (hε : ε∈Ioc (0:ℝ) η) (x : Fin 3 → ℂ) (_hx : x∈(univ : Set (Fin 3 → ℂ))) :
       manifoldExteriorOneForm (Γ ε) x=(Ω ε ((ε:ℂ)•x)).bilinearComp
         (manifoldMapDifferential (fun y : Fin 3 → ℂ => (ε:ℂ)•y) x)
         (manifoldMapDifferential (fun y : Fin 3 → ℂ => (ε:ℂ)•y) x) := by
     ext v w
     simp only [ContinuousLinearMap.bilinearComp_apply,manifoldMapDifferential,mfderiv_eq_fderiv]
     exact cubicBubblePrimitive_curvature hAS hS hB hp.le hm hN.le t δ c (D ε) hε.1.ne' x v w
   obtain ⟨τ,hτ,hτη,hall⟩ := exists_uniform_compact_exact_fibre_embedding_central_into_bp240
     (cubicBubbleVariable_smooth_family (A := A) (B := B) L S (m+1) p N t δ c hD) hK
     (fun x _ => cubicBubblePrimitive_zero_invertible m hAS hS hB hp hN t δ hc hD0 x)
     isOpen_univ (subset_univ K) hη hscaleM hemb hT
     (by intro x _; simpa only [Complex.ofReal_zero,zero_smul] using h0T) Ω hform
   refine ⟨τ,hτ,hτη,?_⟩
   intro ε hε
   obtain ⟨g,W,hW,hKW,hg,he,hgT,hgf⟩ := hall ε hε
   refine ⟨g,W,hW,hKW,hg.contDiff,he,hgT,?_⟩
   intro x hx v w
   have hh := hgf x hx v w
   simp only [mfderiv_eq_fderiv,cubicBubblePrimitive_zero_exterior m hAS hS hB hp hN] at hh
   convert! hh using 1
   all_goals try with_reducible_and_instances rfl

end PackingSufficiencySupport.CubicModel

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.CubicModel.exists_uniform_cubic_bubble_transfer_bp240_oai := @OAI.PackingSufficiencySupport.CubicModel.exists_uniform_cubic_bubble_transfer_bp240_oai
