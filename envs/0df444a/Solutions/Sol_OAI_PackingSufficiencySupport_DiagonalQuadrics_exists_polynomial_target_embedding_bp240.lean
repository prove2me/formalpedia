-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_polynomial_target_embedding_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:07:52.192429+00:00
-- url     : https://prove2.me/submissions/3fc99ba2-3765-43c1-a291-169a6de24d26

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_quadric_relative_shell_map_bp240

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

theorem fsBallDifferential_apply (a : ℝ) (z v : PlanePhase ι) :
    fsBallDifferential a z v = (Real.sqrt a / Real.sqrt (1+phaseSq z)) •
      (v-(phaseDot z v/(1+phaseSq z)) • z) := by
  simp only [fsBallDifferential,smul_apply,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  simp only [div_eq_mul_inv]
  rw [mul_comm ((1+phaseSq z)⁻¹) (phaseDot z v)]

theorem fsBallMap_hasFDerivAt (a : ℝ) (z : PlanePhase ι) :
    HasFDerivAt (fsBallMap a) (fsBallDifferential a z) z := by
  have hs : HasFDerivAt (fun y : PlanePhase ι => 1+phaseSq y)
      ((2:ℝ) • phaseDot z) z := by
    exact (phaseSq_hasFDerivAt z).const_add 1
  have ht := hs.sqrt (fs_den_pos z).ne'
  have hc := ((hasDerivAt_inv (Real.sqrt_pos.2 (fs_den_pos z)).ne').comp_hasFDerivAt z ht).const_mul (Real.sqrt a)
  have hc' : HasFDerivAt (fun y : PlanePhase ι => Real.sqrt a/Real.sqrt (1+phaseSq y))
      ((-(Real.sqrt a / Real.sqrt (1+phaseSq z))/(1+phaseSq z)) • phaseDot z) z := by
    change HasFDerivAt (fun y : PlanePhase ι => Real.sqrt a*(Real.sqrt (1+phaseSq y))⁻¹) _ z
    apply hc.congr_fderiv
    ext v
    simp only [smul_apply,smul_eq_mul,smul_smul]
    have hq := Real.sq_sqrt (fs_den_pos z).le
    field_simp [(Real.sqrt_pos.2 (fs_den_pos z)).ne',(fs_den_pos z).ne']
    rw [hq]
  apply (hc'.smul (hasFDerivAt_id z)).congr_fderiv
  ext v i <;>
    simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,id_eq,fsBallDifferential_apply,
      Pi.add_apply,Pi.smul_apply,Pi.sub_apply,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,Prod.fst_sub,Prod.snd_sub,smul_eq_mul] <;> ring

@[simp] theorem fsBallMap_fderiv (a : ℝ) (z v : PlanePhase ι) :
    fderiv ℝ (fsBallMap a) z v = (Real.sqrt a / Real.sqrt (1+phaseSq z)) •
      (v-(phaseDot z v/(1+phaseSq z)) • z) := by
  rw [(fsBallMap_hasFDerivAt a z).fderiv,fsBallDifferential_apply]

theorem affineFSForm_apply (a : ℝ) (z v w : PlanePhase ι) :
    affineFSForm a z v w = a/(1+phaseSq z)*phaseArea v w - a/(1+phaseSq z)^2*
      (phaseDot z v*phaseArea z w-phaseArea z v*phaseDot z w) := by
  simp only [affineFSForm,sub_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul]

theorem fsBallMap_pullback {a : ℝ} (ha : 0 ≤ a) (z v w : PlanePhase ι) :
    phaseArea (fderiv ℝ (fsBallMap a) z v) (fderiv ℝ (fsBallMap a) z w) =
      affineFSForm a z v w := by
  rw [fsBallMap_fderiv,fsBallMap_fderiv,affineFSForm_apply]
  simp only [map_smul,map_sub,smul_apply,sub_apply,smul_eq_mul,phaseArea_self,mul_zero,sub_zero]
  rw [phaseArea_skew v z]
  have hs : (Real.sqrt a/Real.sqrt (1+phaseSq z))^2 = a/(1+phaseSq z) := by
    rw [div_pow,Real.sq_sqrt ha,Real.sq_sqrt (fs_den_pos z).le]
  calc
    _ = (Real.sqrt a/Real.sqrt (1+phaseSq z))^2 *
        (phaseArea v w - (phaseDot z v*phaseArea z w-phaseArea z v*phaseDot z w)/(1+phaseSq z)) := by ring
    _ = _ := by rw [hs]; field_simp [(fs_den_pos z).ne']

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

theorem affineSphereScale_pos (z : ι → ℂ) : 0<affineSphereScale z :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by linarith [phaseSq_nonneg (complexCartesian z)]))

theorem affineSphereScale_smooth : ContDiff ℝ ∞ (affineSphereScale (ι := ι)) := by
  apply ContDiff.inv
  · apply ContDiff.sqrt
    · exact contDiff_const.add (phaseSq_smooth.comp (complexCartesian (ι := ι)).contDiff)
    · intro z
      exact ne_of_gt (by linarith [phaseSq_nonneg (complexCartesian z)])
  · intro z
    exact (Real.sqrt_pos.mpr (by linarith [phaseSq_nonneg (complexCartesian z)])).ne'

theorem complexSphereLift_smooth : ContDiff ℝ ∞ (complexSphereLift (ι := ι)) :=
  affineSphereScale_smooth.smul complexAffineLift_smooth

theorem complexSphereLift_sq (z : ι → ℂ) : phaseSq (complexCartesian (complexSphereLift z))=1 := by
  rw [complexSphereLift,map_smul,phaseSq_smul,complexAffineLift_sq]
  have hp : 0≤1+phaseSq (complexCartesian z) := by linarith [phaseSq_nonneg (complexCartesian z)]
  dsimp [affineSphereScale]
  rw [inv_pow,Real.sq_sqrt hp]
  exact inv_mul_cancel₀ (ne_of_gt (by linarith [phaseSq_nonneg (complexCartesian z)]))

theorem complexSphereLift_none_ne (z : ι → ℂ) : complexSphereLift z none≠0 := by
  change (affineSphereScale z : ℂ)*1≠0
  simpa using Complex.ofReal_ne_zero.mpr (affineSphereScale_pos z).ne'

theorem complexAffineQuotient_smoothAt {y : Option ι → ℂ} (hy : y none≠0) :
    ContDiffAt ℝ ∞ complexAffineQuotient y := by
  apply contDiffAt_pi.mpr
  intro i
  simp only [complexAffineQuotient,div_eq_mul_inv]
  exact (contDiff_apply ℝ ℂ (some i)).contDiffAt.mul
    ((contDiff_apply ℝ ℂ none).contDiffAt.inv hy)

omit [Fintype ι] in
theorem complexAffineQuotient_smul (ζ : ℂ) (hζ : ζ≠0) (y : Option ι → ℂ) :
    complexAffineQuotient (ζ•y)=complexAffineQuotient y := by
  ext i
  simp only [complexAffineQuotient,Pi.smul_apply,smul_eq_mul]
  exact mul_div_mul_left (y (some i)) (y none) hζ

@[simp] theorem complexAffineQuotient_sphereLift (z : ι → ℂ) :
    complexAffineQuotient (complexSphereLift z)=z := by
  change complexAffineQuotient ((affineSphereScale z : ℂ) • complexAffineLift z)=z
  rw [complexAffineQuotient_smul _ (Complex.ofReal_ne_zero.mpr (affineSphereScale_pos z).ne'),
    complexAffineQuotient_lift]

omit [Fintype ι] in
theorem complexAffineLift_quotient {y : Option ι → ℂ} (hy : y none≠0) :
    complexAffineLift (complexAffineQuotient y)=(y none)⁻¹•y := by
  ext i
  cases i with
  | none => simpa only [complexAffineLift_none,Pi.smul_apply,smul_eq_mul] using (inv_mul_cancel₀ hy).symm
  | some i => simp [complexAffineQuotient,div_eq_mul_inv,mul_comm]

theorem complexCartesian_complex_smul_sq (ζ : ℂ) (y : ι → ℂ) :
    phaseSq (complexCartesian (ζ•y))=Complex.normSq ζ*phaseSq (complexCartesian y) := by
  simp only [complexCartesian_sq,Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum]

theorem complexSphereLift_quotient_unit {y : Option ι → ℂ}
    (hy : y none≠0) (hys : phaseSq (complexCartesian y)=1) :
    ∃ ζ : ℂ,Complex.normSq ζ=1 ∧ complexSphereLift (complexAffineQuotient y)=ζ•y := by
  let ζ : ℂ := (affineSphereScale (complexAffineQuotient y) : ℂ)*(y none)⁻¹
  have he : complexSphereLift (complexAffineQuotient y)=ζ•y := by
    change (affineSphereScale (complexAffineQuotient y) : ℂ) •
      complexAffineLift (complexAffineQuotient y)=ζ•y
    rw [complexAffineLift_quotient hy,smul_smul]
  refine ⟨ζ,?_,he⟩
  have h := complexSphereLift_sq (complexAffineQuotient y)
  rw [he,complexCartesian_complex_smul_sq,hys,mul_one] at h
  exact h

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

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_CubicEndCoordinates
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators

variable {ι : Type*} [Fintype ι]

theorem veronese_contDiff : ContDiff ℂ ∞ (veronese : (ι → ℂ) → _) := by
  apply contDiff_pi.mpr
  rintro (⟨b,i⟩|⟨i,j⟩)
  · exact contDiff_apply ℂ ℂ i
  · exact (contDiff_apply ℂ ℂ i).mul (contDiff_apply ℂ ℂ j)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem holomorphicFS_exterior {f : E → (ι → ℂ)} (hf : ContDiff ℂ ∞ f)
    (c : ℝ) (z : E) :
    euclideanExteriorOneForm
      (primitivePullback (affineFSPrimitive c) (fun x => complexCartesian (f x))) z=
      (affineFSForm c (complexCartesian (f z))).bilinearComp
        (fderiv ℝ (fun x => complexCartesian (f x)) z)
        (fderiv ℝ (fun x => complexCartesian (f x)) z) := by
  have hs : ContDiff ℝ ∞ (fun x => complexCartesian (f x)) :=
    (complexCartesian (ι := ι)).contDiff.comp (hf.restrict_scalars ℝ)
  rw [primitivePullback_exterior (affineFSPrimitive_smooth c) hs,← affineFSForm_eq_exterior]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

theorem normalPolynomial_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℂ ∞ (normalPolynomial a t) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact (contDiff_apply ℂ ℂ i).comp (veronese_contDiff.comp (affineComplex m).contDiff)
  | inr j => exact contDiff_const.mul ((contDiff_apply ℂ ℂ j).comp (equations_contDiff a))

theorem normalPolynomialCartesian_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℝ ∞ (fun z => complexCartesian (normalPolynomial a t z)) :=
  (complexCartesian (ι := NormalPolynomialIndex m)).contDiff.comp
    ((normalPolynomial_smooth a t).restrict_scalars ℝ)

theorem ambientFSPrimitive_smooth (c : ℝ) :
    ContDiff ℝ ∞ (ambientFSPrimitive (m := m) c) :=
  ((affineFSPrimitive_smooth c).comp (affinePhase m).contDiff).clm_comp contDiff_const

theorem ambientFSPrimitive_exterior (c : ℝ) (z : Affine m) :
    euclideanExteriorOneForm (ambientFSPrimitive c) z=
      (affineFSForm c (affinePhase m z)).bilinearComp (affinePhase m) (affinePhase m) := by
  have he : ambientFSPrimitive (m := m) c=primitivePullback (affineFSPrimitive c) (affinePhase m) := by
    funext x
    simp only [ambientFSPrimitive,primitivePullback,(affinePhase m).fderiv]
  rw [he,primitivePullback_exterior (affineFSPrimitive_smooth c) (affinePhase m).contDiff,
    ← affineFSForm_eq_exterior,(affinePhase m).fderiv]

theorem normalAmbientForm_apply (a : Fin m → ℂ) (c d t : ℝ) (z v w : Affine m) :
    normalAmbientForm a c d t z v w=
      (1-2*d)*affineFSForm c (affinePhase m z) (affinePhase m v) (affinePhase m w)+
      d*affineFSForm c (complexCartesian (normalPolynomial a t z))
        (fderiv ℝ (fun x => complexCartesian (normalPolynomial a t x)) z v)
        (fderiv ℝ (fun x => complexCartesian (normalPolynomial a t x)) z w) := by
  have h₀ := (ambientFSPrimitive_smooth (m := m) c).differentiable (by simp) z
  have h₁ := (primitivePullback_smooth (affineFSPrimitive_smooth c)
    (normalPolynomialCartesian_smooth a t)).differentiable (by simp) z
  rw [normalAmbientForm,normalAmbientPrimitive,euclideanExteriorOneForm_add
    (h₀.const_smul _) (h₁.const_smul _),euclideanExteriorOneForm_smul _ h₀,
    euclideanExteriorOneForm_smul _ h₁,ambientFSPrimitive_exterior,
    holomorphicFS_exterior (normalPolynomial_smooth a t)]
  rfl

end PackingSufficiencySupport.DiagonalQuadrics

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

 theorem radialSymplectization_apply (z : PlanePhase ι) (α : PlanePhase ι →L[ℝ] ℝ)
    (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ) (v w : PlanePhase ι) :
    radialSymplectization z α C v w=
      2*(phaseDot z v*α w-α v*phaseDot z w)+phaseSq z*C v w := by
  simp only [radialSymplectization,add_apply,smul_apply,sub_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]

theorem mixedHopfPrimitive_smoothAt {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (c d : ℝ) :
    ContDiffAt ℝ ∞ (mixedHopfPrimitive F c d) z :=
  ((hopfPrimitive_smoothAt c hz).const_smul (1-2*d)).add
    ((primitivePullback_smoothAt (hopfPrimitive_smoothAt c hFz) hF).const_smul d)

theorem mixedHopfForm_eq {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (c d : ℝ) :
    mixedHopfForm F c d z=(1-2*d)•hopfForm c z+
      d•(hopfForm c (F z)).bilinearComp (fderiv ℝ F z) (fderiv ℝ F z) := by
  have h₀ := (hopfPrimitive_smoothAt c hz).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h₁ := (primitivePullback_smoothAt (hopfPrimitive_smoothAt c hFz) hF).differentiableAt (by simp)
  rw [mixedHopfForm,mixedHopfPrimitive,euclideanExteriorOneForm_add (h₀.const_smul _) (h₁.const_smul _),
    euclideanExteriorOneForm_smul _ h₀,euclideanExteriorOneForm_smul _ h₁,
    primitivePullback_exteriorAt (hopfPrimitive_smoothAt c hFz) hF]
  rfl

theorem homogeneousConePrimitive_exterior {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (c d : ℝ) :
    euclideanExteriorOneForm (homogeneousConePrimitive F c d) z=
      radialSymplectization z (mixedHopfPrimitive F c d z) (mixedHopfForm F c d z) := by
  have ha := (mixedHopfPrimitive_smoothAt hF hz hFz c d).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := (phaseSq_hasFDerivAt z).smul ha.hasFDerivAt
  rw [euclideanExteriorOneForm,show fderiv ℝ (homogeneousConePrimitive F c d) z=_ from he.fderiv]
  ext v w
  simp only [sub_apply,ContinuousLinearMap.flip_apply,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,radialSymplectization_apply,
    mixedHopfForm,euclideanExteriorOneForm]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mixedHopfCurvaturePullback_gauge {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^2•P z)
    {S : E → ℂ} {G : E → (ι → ℂ)} {x : E}
    (hS : DifferentiableAt ℝ S x) (hG : DifferentiableAt ℝ G x)
    (hSx : S x≠0) (hGx : G x≠0) (c d : ℝ) (v w : E) :
    mixedHopfCurvaturePullback P c d (fun y => S y•G y) x v w=
      mixedHopfCurvaturePullback P c d G x v w := by
  have hGxc : complexCartesian (G x)≠0 := by
    intro h; exact hGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have hPGxc : complexCartesian (P (G x))≠0 := by
    intro h; exact hPn (G x) hGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have he : (fun y => P (S y•G y))=(fun y => (S y)^2•P (G y)) := funext fun y => hPs _ _
  unfold mixedHopfCurvaturePullback
  change (1-2*d)*hopfCurvaturePullback c (fun y => S y•G y) x v w+
    d*hopfCurvaturePullback c (fun y => P (S y•G y)) x v w=_
  rw [he]
  unfold hopfCurvaturePullback
  rw [hopfForm_variable_gauge hS hG hSx hGxc]
  have h₂ := hopfForm_variable_gauge (S := fun y => S y^2) (G := fun y => P (G y))
    (hS.pow 2) ((hP.differentiable (by simp) (G x)).comp x hG)
      (pow_ne_zero 2 hSx) hPGxc c v w
  exact congrArg (fun q : ℝ => (1-2*d)*hopfCurvaturePullback c G x v w+d*q) h₂

theorem cartesianConjugate_smooth {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (cartesianConjugate P) :=
  (complexCartesian (ι := κ)).contDiff.comp (hP.comp (complexCartesian (ι := ι)).symm.contDiff)

theorem mixedHopfCurvaturePullback_eq {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) {G : E → (ι → ℂ)} {x : E}
    (hG : DifferentiableAt ℝ G x) (hGx : G x≠0) (hPGx : P (G x)≠0)
    (c d : ℝ) (v w : E) :
    mixedHopfCurvaturePullback P c d G x v w=
      mixedHopfForm (cartesianConjugate P) c d (complexCartesian (G x))
        (fderiv ℝ (fun y => complexCartesian (G y)) x v)
        (fderiv ℝ (fun y => complexCartesian (G y)) x w) := by
  have hz : complexCartesian (G x)≠0 := by
    intro h; exact hGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have hPz : cartesianConjugate P (complexCartesian (G x))≠0 := by
    rw [cartesianConjugate_cartesian]
    intro h; exact hPGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have hGc := complexCartesian.differentiableAt.comp x hG
  have hPc := (cartesianConjugate_smooth hP).differentiable (by simp) (complexCartesian (G x))
  have he : (fun y => cartesianConjugate P (complexCartesian (G y)))=
      (fun y => complexCartesian (P (G y))) := funext fun y => cartesianConjugate_cartesian P (G y)
  have hD (u : E) : fderiv ℝ (fun y => complexCartesian (P (G y))) x u=
      fderiv ℝ (cartesianConjugate P) (complexCartesian (G x))
        (fderiv ℝ (fun y => complexCartesian (G y)) x u) := by
    rw [←he]
    exact congrArg (fun L => L u) (fderiv_comp x hPc hGc)
  rw [mixedHopfForm_eq (cartesianConjugate_smooth hP).contDiffAt hz hPz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,
    cartesianConjugate_cartesian,mixedHopfCurvaturePullback,hopfCurvaturePullback,hD]

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_AffineHopfRestriction
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

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_DegreeHopfDeformation
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

theorem mixedHopfCurvaturePullback_comp {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) {G : E' → (ι → ℂ)} {H : E → E'} {x : E}
    (hG : DifferentiableAt ℝ G (H x)) (hH : DifferentiableAt ℝ H x)
    (c d : ℝ) (v w : E) :
    mixedHopfCurvaturePullback P c d (fun y => G (H y)) x v w=
      mixedHopfCurvaturePullback P c d G (H x) (fderiv ℝ H x v) (fderiv ℝ H x w) := by
  unfold mixedHopfCurvaturePullback
  rw [hopfCurvaturePullback_comp hG hH]
  have h₂ := hopfCurvaturePullback_comp (G := fun y => P (G y))
    ((hP.differentiable (by simp) _).comp (H x) hG) hH c v w
  exact congrArg (fun q : ℝ => (1-2*d)*hopfCurvaturePullback c G (H x)
    (fderiv ℝ H x v) (fderiv ℝ H x w)+d*q) h₂

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_CircleAction_DegreeCircleCovariance
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

theorem diffeomorphicFormPullback_inverse {f : E → F} {g : F → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfg : Function.RightInverse g f)
    (Ω₀ : E → E →L[ℝ] E →L[ℝ] ℝ) (Ω₁ : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hω : ∀ x v w,Ω₁ (f x) (fderiv ℝ f x v) (fderiv ℝ f x w)=Ω₀ x v w)
    (y v w : F) :
    Ω₀ (g y) (fderiv ℝ g y v) (fderiv ℝ g y w)=Ω₁ y v w := by
  have he : (fun z => f (g z))=id := funext hfg
  have hd := (hf.differentiable (by simp) (g y)).hasFDerivAt.comp y
    (hg.differentiable (by simp) y).hasFDerivAt
  have hD (u : F) : fderiv ℝ f (g y) (fderiv ℝ g y u)=u := by
    have hh := congrArg (fun L => L u) hd.fderiv
    change fderiv ℝ (fun z => f (g z)) y u=_ at hh
    rw [he,fderiv_id] at hh
    exact hh.symm
  rw [←hω (g y),hfg,hD,hD]

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_DegreeRelativeShell
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold
open scoped ContDiff Manifold Topology BigOperators

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complexQuotientGauge_smoothAt {y : Option ι → ℂ} (hy : y none≠0) :
    ContDiffAt ℝ ∞ complexQuotientGauge y := by
  apply ContDiffAt.mul
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp y
      (affineSphereScale_smooth.contDiffAt.comp y (complexAffineQuotient_smoothAt hy))
  · exact (contDiff_apply ℝ ℂ none).contDiffAt.inv hy

theorem complexQuotientGauge_ne {y : Option ι → ℂ} (hy : y none≠0) :
    complexQuotientGauge y≠0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (affineSphereScale_pos _).ne') (inv_ne_zero hy)

theorem complexSphereLift_quotient_gauge {y : Option ι → ℂ} (hy : y none≠0) :
    complexSphereLift (complexAffineQuotient y)=complexQuotientGauge y•y := by
  change (affineSphereScale (complexAffineQuotient y) : ℂ) •
    complexAffineLift (complexAffineQuotient y)=complexQuotientGauge y•y
  rw [complexAffineLift_quotient hy,smul_smul]
  rfl

theorem mixedHopfCurvaturePullback_sphereLift {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^2•P z)
    {Z : E → (ι → ℂ)} {x : E} (hZ : DifferentiableAt ℝ Z x)
    (c d : ℝ) (v w : E) :
    mixedHopfCurvaturePullback P c d (fun y => complexSphereLift (Z y)) x v w=
      mixedHopfCurvaturePullback P c d (fun y => complexAffineLift (Z y)) x v w := by
  have hS : DifferentiableAt ℝ (fun y => (affineSphereScale (Z y) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((affineSphereScale_smooth.differentiable (by simp) (Z x)).comp x hZ)
  have hG : DifferentiableAt ℝ (fun y => complexAffineLift (Z y)) x :=
    (complexAffineLift_smooth.differentiable (by simp) (Z x)).comp x hZ
  have hGx : complexAffineLift (Z x)≠0 := by
    intro he
    have hh := congrFun he none
    exact one_ne_zero (by simpa only [complexAffineLift_none,Pi.zero_apply] using hh)
  exact mixedHopfCurvaturePullback_gauge hP hPn hPs hS hG
    (Complex.ofReal_ne_zero.mpr (affineSphereScale_pos _).ne') hGx c d v w

theorem mixedHopfCurvaturePullback_chart_normalize {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^2•P z)
    {G : E → (Option ι → ℂ)} {x : E}
    (hG : DifferentiableAt ℝ G x) (hGn : ∀ y,G y none≠0)
    (c d : ℝ) (v w : E) :
    mixedHopfCurvaturePullback P c d (fun y => complexSphereLift (complexAffineQuotient (G y))) x v w=
      mixedHopfCurvaturePullback P c d G x v w := by
  have he : (fun y => complexSphereLift (complexAffineQuotient (G y)))=
      (fun y => complexQuotientGauge (G y)•G y) :=
    funext fun y => complexSphereLift_quotient_gauge (hGn y)
  rw [he]
  exact mixedHopfCurvaturePullback_gauge hP hPn hPs
    (((complexQuotientGauge_smoothAt (hGn x)).differentiableAt (by simp)).comp x hG)
    hG (complexQuotientGauge_ne (hGn x))
    (fun he => hGn x (by simpa only [Pi.zero_apply] using congrFun he none)) c d v w

variable {q : ℝ} {ℓ : ℕ}

theorem sphere_map_fderiv_tangent {N : E → PlanePhase ι} {x : E}
    (hN : DifferentiableAt ℝ N x) (hNs : ∀ y,phaseSq (N y)=1) (v : E) :
    phaseDot (N x) (fderiv ℝ N x v)=0 := by
  have he : (fun y => phaseSq (N y))=(fun _ : E => (1:ℝ)) := funext hNs
  have hd := (phaseSq_hasFDerivAt (N x)).comp x hN.hasFDerivAt
  have hD := congrArg (fun L => L v) hd.fderiv
  change fderiv ℝ (fun y => phaseSq (N y)) x v=_ at hD
  rw [he,show fderiv ℝ (fun _ : E => (1:ℝ)) x=0 from (hasFDerivAt_const (1:ℝ) x).fderiv] at hD
  simp only [zero_apply,ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul] at hD
  linarith

theorem homogeneousCone_sphere_tangent {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : phaseSq z=1) (hFz : F z≠0)
    (c d : ℝ) {v w : PlanePhase ι} (hv : phaseDot z v=0) (hw : phaseDot z w=0) :
    euclideanExteriorOneForm (homogeneousConePrimitive F c d) z v w=mixedHopfForm F c d z v w := by
  have hzn : z≠0 := by intro he; simp [he,phaseSq] at hz
  rw [homogeneousConePrimitive_exterior hF hzn hFz,radialSymplectization_apply,hv,hw,hz]
  ring

theorem cone_flow_sphere_pullback {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hFn : ∀ z,z≠0 → F z≠0)
    {f : PlanePhase ι → PlanePhase ι} (hf : ContDiff ℝ ∞ f)
    (hfr : ∀ z,phaseSq (f z)=phaseSq z) (c d : ℝ)
    (hfω : ∀ z,phaseSq z=1 → ∀ v w,
      euclideanExteriorOneForm (homogeneousConePrimitive F c d) (f z)
        (fderiv ℝ f z v) (fderiv ℝ f z w)=
      euclideanExteriorOneForm (homogeneousConePrimitive F c 0) z v w)
    {N : E → PlanePhase ι} {x : E} (hN : DifferentiableAt ℝ N x)
    (hNs : ∀ y,phaseSq (N y)=1) (v w : E) :
    mixedHopfForm F c d (f (N x))
      (fderiv ℝ (fun y => f (N y)) x v) (fderiv ℝ (fun y => f (N y)) x w)=
    mixedHopfForm F c 0 (N x) (fderiv ℝ N x v) (fderiv ℝ N x w) := by
  have hNz : N x≠0 := by intro he; have hh := hNs x; simp [he,phaseSq] at hh
  have hfNs : ∀ y,phaseSq (f (N y))=1 := fun y => (hfr _).trans (hNs y)
  have hfNz : f (N x)≠0 := by intro he; have hh := hfNs x; simp [he,phaseSq] at hh
  have hfN : DifferentiableAt ℝ (fun y => f (N y)) x :=
    (hf.differentiable (by simp) (N x)).comp x hN
  rw [←homogeneousCone_sphere_tangent hF.contDiffAt (hfNs x) (hFn _ hfNz) c d
    (sphere_map_fderiv_tangent hfN hfNs v) (sphere_map_fderiv_tangent hfN hfNs w),
    ←homogeneousCone_sphere_tangent hF.contDiffAt (hNs x) (hFn _ hNz) c 0
    (sphere_map_fderiv_tangent hN hNs v) (sphere_map_fderiv_tangent hN hNs w)]
  have hD (u : E) : fderiv ℝ (fun y => f (N y)) x u=
      fderiv ℝ f (N x) (fderiv ℝ N x u) :=
    congrArg (fun L => L u) (fderiv_comp x (hf.differentiable (by simp) _) hN)
  rw [hD,hD]
  exact hfω (N x) (hNs x) _ _

end

section
variable {ι : Type*} [Fintype ι]

theorem sphereAffineDescend_smooth {f : (Option ι → ℂ) → (Option ι → ℂ)}
    (hf : ContDiff ℝ ∞ f)
    (hfinf : ∀ y,phaseSq (complexCartesian y)=1 → (f y none=0 ↔ y none=0)) :
    ContDiff ℝ ∞ (sphereAffineDescend f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have hne : f (complexSphereLift z) none≠0 := by
    intro he
    exact complexSphereLift_none_ne z ((hfinf _ (complexSphereLift_sq z)).mp he)
  exact (complexAffineQuotient_smoothAt hne).comp z (hf.comp complexSphereLift_smooth).contDiffAt

theorem sphereAffineDescend_leftInverse {f g : (Option ι → ℂ) → (Option ι → ℂ)}
    (hgf : LeftInverse g f)
    (hfr : ∀ y,phaseSq (complexCartesian (f y))=phaseSq (complexCartesian y))
    (hfinf : ∀ y,phaseSq (complexCartesian y)=1 → (f y none=0 ↔ y none=0))
    (hgζ : ∀ ζ : ℂ,Complex.normSq ζ=1 → ∀ y,phaseSq (complexCartesian y)=1 →
      g (ζ•y)=ζ•g y) : LeftInverse (sphereAffineDescend g) (sphereAffineDescend f) := by
  intro z
  have hyr : phaseSq (complexCartesian (f (complexSphereLift z)))=1 :=
    (hfr _).trans (complexSphereLift_sq z)
  have hy : f (complexSphereLift z) none≠0 := by
    intro he
    exact complexSphereLift_none_ne z ((hfinf _ (complexSphereLift_sq z)).mp he)
  obtain ⟨ζ,hζ,he⟩ := complexSphereLift_quotient_unit hy hyr
  have hζne : ζ≠0 := by intro h; simp [h] at hζ
  change complexAffineQuotient (g (complexSphereLift
    (complexAffineQuotient (f (complexSphereLift z)))))=z
  rw [he,hgζ ζ hζ _ hyr,hgf,complexAffineQuotient_smul ζ hζne,
    complexAffineQuotient_sphereLift]

theorem sphereAffineDescend_equiv {f g : (Option ι → ℂ) → (Option ι → ℂ)}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hgf : LeftInverse g f) (hfg : RightInverse g f)
    (hfr : ∀ y,phaseSq (complexCartesian (f y))=phaseSq (complexCartesian y))
    (hgr : ∀ y,phaseSq (complexCartesian (g y))=phaseSq (complexCartesian y))
    (hfinf : ∀ y,phaseSq (complexCartesian y)=1 → (f y none=0 ↔ y none=0))
    (hginf : ∀ y,phaseSq (complexCartesian y)=1 → (g y none=0 ↔ y none=0))
    (hfζ : ∀ ζ : ℂ,Complex.normSq ζ=1 → ∀ y,phaseSq (complexCartesian y)=1 → f (ζ•y)=ζ•f y)
    (hgζ : ∀ ζ : ℂ,Complex.normSq ζ=1 → ∀ y,phaseSq (complexCartesian y)=1 → g (ζ•y)=ζ•g y) :
    ContDiff ℝ ∞ (sphereAffineDescend f) ∧ ContDiff ℝ ∞ (sphereAffineDescend g) ∧
      LeftInverse (sphereAffineDescend g) (sphereAffineDescend f) ∧
      RightInverse (sphereAffineDescend g) (sphereAffineDescend f) :=
  ⟨sphereAffineDescend_smooth hf hfinf,sphereAffineDescend_smooth hg hginf,
    sphereAffineDescend_leftInverse hgf hfr hfinf hgζ,
    sphereAffineDescend_leftInverse hfg hgr hginf hfζ⟩

end

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem complexConjugate_smooth {f : PlanePhase ι → PlanePhase κ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (complexConjugate f) :=
  (complexCartesian (ι := κ)).symm.contDiff.comp (hf.comp (complexCartesian (ι := ι)).contDiff)

theorem sphereAffineDescend_curvature {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^2•P z)
    {f : PlanePhase (Option ι) → PlanePhase (Option ι)} (hf : ContDiff ℝ ∞ f)
    (hfr : ∀ z,phaseSq (f z)=phaseSq z)
    (hfinf : ∀ z,phaseSq z=1 →
      (complexCartesian.symm (f z) none=0 ↔ complexCartesian.symm z none=0))
    (c d : ℝ)
    (hfω : ∀ z,phaseSq z=1 → ∀ v w,
      euclideanExteriorOneForm (homogeneousConePrimitive (cartesianConjugate P) c d) (f z)
        (fderiv ℝ f z v) (fderiv ℝ f z w)=
      euclideanExteriorOneForm (homogeneousConePrimitive (cartesianConjugate P) c 0) z v w)
    (x v w : ι → ℂ) :
    mixedHopfCurvaturePullback P c d
        (fun y => complexAffineLift (sphereAffineDescend (complexConjugate f) y)) x v w=
      mixedHopfCurvaturePullback P c 0 complexAffineLift x v w := by
  let G : (ι → ℂ) → (Option ι → ℂ) := fun y =>
    complexCartesian.symm (f (complexCartesian (complexSphereLift y)))
  have hG : ContDiff ℝ ∞ G := (complexConjugate_smooth hf).comp complexSphereLift_smooth
  have hGn (y : ι → ℂ) : G y none≠0 := by
    intro he
    have hh := (hfinf _ (complexSphereLift_sq y)).mp he
    exact complexSphereLift_none_ne y (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh)
  have hD : ContDiff ℝ ∞ (sphereAffineDescend (complexConjugate f)) := by
    apply sphereAffineDescend_smooth (complexConjugate_smooth hf)
    intro z hz
    simpa only [complexConjugate,ContinuousLinearEquiv.symm_apply_apply] using hfinf (complexCartesian z) hz
  have hNpc (y : ι → ℂ) : complexSphereLift y≠0 := by
    intro he
    exact complexSphereLift_none_ne y (by simpa only [Pi.zero_apply] using congrFun he none)
  have hGpc (y : ι → ℂ) : G y≠0 := by
    intro he
    exact hGn y (by simpa only [Pi.zero_apply] using congrFun he none)
  have hFn (z : PlanePhase (Option ι)) (hz : z≠0) : cartesianConjugate P z≠0 := by
    intro he
    have hn : complexCartesian.symm z≠0 := by
      intro hh
      exact hz (by simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero]
        using congrArg complexCartesian hh)
    exact hPn _ hn (complexCartesian.injective (he.trans (map_zero _).symm))
  have hω : mixedHopfCurvaturePullback P c d G x v w=
      mixedHopfCurvaturePullback P c 0 complexSphereLift x v w := by
    rw [mixedHopfCurvaturePullback_eq hP (hG.differentiable (by simp) x) (hGpc x) (hPn _ (hGpc x)),
      mixedHopfCurvaturePullback_eq hP (complexSphereLift_smooth.differentiable (by simp) x)
        (hNpc x) (hPn _ (hNpc x))]
    simpa only [G,ContinuousLinearEquiv.apply_symm_apply,Function.comp_def] using
      cone_flow_sphere_pullback (cartesianConjugate_smooth hP) hFn hf hfr c d hfω
        (((complexCartesian (ι := Option ι)).contDiff.comp complexSphereLift_smooth).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)
        complexSphereLift_sq v w
  calc
    _=mixedHopfCurvaturePullback P c d
        (fun y => complexSphereLift (sphereAffineDescend (complexConjugate f) y)) x v w :=
      (mixedHopfCurvaturePullback_sphereLift hP hPn hPs (hD.differentiable (by simp) x) c d v w).symm
    _=mixedHopfCurvaturePullback P c d G x v w :=
      mixedHopfCurvaturePullback_chart_normalize hP hPn hPs (hG.differentiable (by simp) x) hGn c d v w
    _=mixedHopfCurvaturePullback P c 0 complexSphereLift x v w := hω
    _=_ := mixedHopfCurvaturePullback_sphereLift hP hPn hPs differentiableAt_id c 0 v w

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_SphereCartesianDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Function
open scoped Manifold Topology
open Set Manifold
section
variable {ι : Type*} [Fintype ι]

theorem complexConjugate_leftInverse {f g : PlanePhase ι → PlanePhase ι}
    (h : LeftInverse g f) : LeftInverse (complexConjugate g) (complexConjugate f) := by
  intro z
  simp only [complexConjugate,ContinuousLinearEquiv.apply_symm_apply]
  rw [h,ContinuousLinearEquiv.symm_apply_apply]

theorem complexConjugate_radius {f : PlanePhase ι → PlanePhase ι}
    (h : ∀ z,phaseSq (f z)=phaseSq z) (z : ι → ℂ) :
    phaseSq (complexCartesian (complexConjugate f z))=phaseSq (complexCartesian z) := by
  simp only [complexConjugate,ContinuousLinearEquiv.apply_symm_apply,h]

theorem complexConjugate_circle {f : PlanePhase ι → PlanePhase ι}
    (h : ∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
      f (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
        phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (f z))
    (ζ : ℂ) (hζ : Complex.normSq ζ=1) (z : ι → ℂ) (hz : phaseSq (complexCartesian z)=1) :
    complexConjugate f (ζ•z)=ζ•complexConjugate f z := by
  have he (y : ι → ℂ) : complexDiagonal (fun _ => ζ) y=ζ•y := rfl
  have hh := h ζ hζ (complexCartesian z) hz
  simp only [phaseUnitDiagonal_apply,phaseDiagonal_cartesian,he] at hh
  apply complexCartesian.injective
  change f (complexCartesian (ζ•z))=complexCartesian (ζ•complexCartesian.symm (f (complexCartesian z)))
  rw [hh]
  rw [←he,←phaseDiagonal_cartesian,ContinuousLinearEquiv.apply_symm_apply]

theorem sphereCartesianDescend_equiv
    {f g : PlanePhase (Option ι) → PlanePhase (Option ι)}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hgf : LeftInverse g f) (hfg : RightInverse g f)
    (hfr : ∀ y,phaseSq (f y)=phaseSq y) (hgr : ∀ y,phaseSq (g y)=phaseSq y)
    (hfinf : ∀ y,phaseSq y=1 → (complexCartesian.symm (f y) none=0 ↔ complexCartesian.symm y none=0))
    (hginf : ∀ y,phaseSq y=1 → (complexCartesian.symm (g y) none=0 ↔ complexCartesian.symm y none=0))
    (hfζ : ∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
      f (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (f z))
    (hgζ : ∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
      g (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (g z)) :
    ContDiff ℝ ∞ (sphereAffineDescend (complexConjugate f)) ∧
      ContDiff ℝ ∞ (sphereAffineDescend (complexConjugate g)) ∧
      LeftInverse (sphereAffineDescend (complexConjugate g)) (sphereAffineDescend (complexConjugate f)) ∧
      RightInverse (sphereAffineDescend (complexConjugate g)) (sphereAffineDescend (complexConjugate f)) := by
  apply sphereAffineDescend_equiv (complexConjugate_smooth hf) (complexConjugate_smooth hg)
    (complexConjugate_leftInverse hgf) (complexConjugate_leftInverse hfg)
    (complexConjugate_radius hfr) (complexConjugate_radius hgr)
  · intro y hy
    simpa only [complexConjugate,ContinuousLinearEquiv.symm_apply_apply] using hfinf (complexCartesian y) hy
  · intro y hy
    simpa only [complexConjugate,ContinuousLinearEquiv.symm_apply_apply] using hginf (complexCartesian y) hy
  · exact complexConjugate_circle hfζ
  · exact complexConjugate_circle hgζ

end

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
section

theorem optionPhaseAmbient_capacity (m : ℕ) (z : PlanePhase (Option (Fin m))) :
    capacity (optionPhaseAmbient m z)=Real.pi*phaseSq z := by
  obtain ⟨z,rfl⟩ := complexCartesian.surjective z
  simp only [optionPhaseAmbient,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply,capacity,complexCartesian_sq]
  congr 1
  simp only [Fin.sum_univ_succ,Fintype.sum_option]
  rfl

theorem optionPhaseAmbient_form (m : ℕ) (v w : PlanePhase (Option (Fin m))) :
    standardForm (optionPhaseAmbient m v) (optionPhaseAmbient m w)=phaseArea v w := by
  obtain ⟨v,rfl⟩ := complexCartesian.surjective v
  obtain ⟨w,rfl⟩ := complexCartesian.surjective w
  simp only [optionPhaseAmbient,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply,standardForm,phaseArea_apply]
  simp only [Fin.sum_univ_succ,Fintype.sum_option]
  rfl

variable {ι : Type*} [Fintype ι]

theorem fsBallMap_isEmbedding {a : ℝ} (ha : 0<a) :
    Topology.IsEmbedding (fsBallMap (ι := ι) a) :=
  Topology.IsEmbedding.subtypeVal.comp (fsBallHomeomorph (ι := ι) ha).isEmbedding

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_QuadricLargeAmbientPacking
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Hamiltonian

variable {m : ℕ}

theorem homogeneousPolynomial_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℂ ∞ (homogeneousPolynomial a t) := by
  apply contDiff_pi.mpr
  rintro (_|((⟨b,i⟩|⟨i,j⟩)|j))
  · exact (contDiff_apply ℂ ℂ none).pow 2
  · exact (contDiff_apply ℂ ℂ none).mul (contDiff_apply ℂ ℂ (some i))
  · exact (contDiff_apply ℂ ℂ (some i)).mul (contDiff_apply ℂ ℂ (some j))
  · exact contDiff_const.mul (((contDiff_apply ℂ ℂ (some (some j))).pow 2).sub
      ((contDiff_apply ℂ ℂ (some none)).pow 2) |>.add
      (contDiff_const.mul ((contDiff_apply ℂ ℂ none).pow 2)))

theorem homogeneousPolynomial_homogeneous (a : Fin m → ℂ) (t : ℝ)
    (b : ℂ) (z : HomogeneousInput m) :
    homogeneousPolynomial a t (b•z)=b^2•homogeneousPolynomial a t z := by
  funext i
  rcases i with _|((⟨e,i⟩|⟨i,j⟩)|j)
  all_goals simp only [homogeneousPolynomial,Pi.smul_apply,smul_eq_mul]; ring

theorem homogeneousPolynomial_zero_iff (a : Fin m → ℂ) (t : ℝ) (z : HomogeneousInput m) :
    homogeneousPolynomial a t z=0 ↔ z=0 := by
  constructor
  · intro h
    funext i
    cases i with
    | none =>
      have hh := congrFun h none
      change z none^2=0 at hh
      exact eq_zero_of_pow_eq_zero hh
    | some i =>
      have hh := congrFun h (some (.inl (.inr (i,i))))
      change z (some i)*z (some i)=0 at hh
      exact (mul_self_eq_zero.mp hh)
  · rintro rfl
    funext i
    rcases i with _|((⟨e,i⟩|⟨i,j⟩)|j)
    all_goals simp [homogeneousPolynomial]

theorem homogeneousPolynomial_nonzero (a : Fin m → ℂ) (t : ℝ)
    {z : HomogeneousInput m} (hz : z≠0) : homogeneousPolynomial a t z≠0 :=
  fun h => hz ((homogeneousPolynomial_zero_iff a t z).mp h)

theorem homogeneousPolynomial_affine (a : Fin m → ℂ) (t : ℝ) (z : Affine m) :
    homogeneousPolynomial a t (fun i => match i with
      | none => 1 | some j => affineComplex m z j)=
    (fun i => match i with | none => 1 | some j => normalPolynomial a t z j) := by
  funext i
  rcases i with _|((⟨e,i⟩|⟨i,j⟩)|j)
  · simp [homogeneousPolynomial]
  · simp [homogeneousPolynomial,normalPolynomial,veronese]
  · rfl
  · simp [homogeneousPolynomial,normalPolynomial,equations,affineComplex]

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_QuadricRelativeShellFlow
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
section
variable {m : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mixedHopf_affine_pullback (a : Fin m → ℂ) (c d t : ℝ)
    {Z : E → Affine m} {x : E} (hZ : DifferentiableAt ℝ Z x) (v w : E) :
    mixedHopfCurvaturePullback (homogeneousPolynomial a t) c d
      (fun y => complexAffineLift (affineComplex m (Z y))) x v w=
      normalAmbientForm a c d t (Z x) (fderiv ℝ Z x v) (fderiv ℝ Z x w) := by
  have hAc : DifferentiableAt ℝ (fun y => affineComplex m (Z y)) x :=
    ((affineComplex m).restrictScalars ℝ).differentiableAt.comp x hZ
  have hPc : DifferentiableAt ℝ (fun y => normalPolynomial a t (Z y)) x :=
    (((normalPolynomial_smooth a t).restrict_scalars ℝ).differentiable (by simp) _).comp x hZ
  have he : (fun y => homogeneousPolynomial a t (complexAffineLift (affineComplex m (Z y))))=
      (fun y => complexAffineLift (normalPolynomial a t (Z y))) := by
    funext y
    have h₁ : complexAffineLift (affineComplex m (Z y))=
        (fun i => match i with | none => 1 | some j => affineComplex m (Z y) j) := by
      funext i; cases i <;> rfl
    have h₂ : complexAffineLift (normalPolynomial a t (Z y))=
        (fun i => match i with | none => 1 | some j => normalPolynomial a t (Z y) j) := by
      funext i; cases i <;> rfl
    rw [h₁,h₂]
    exact homogeneousPolynomial_affine a t (Z y)
  unfold mixedHopfCurvaturePullback hopfCurvaturePullback
  change (1-2*d)*hopfForm c (complexCartesian (complexAffineLift (affineComplex m (Z x))))
    (fderiv ℝ (fun y => complexCartesian (complexAffineLift (affineComplex m (Z y)))) x v)
    (fderiv ℝ (fun y => complexCartesian (complexAffineLift (affineComplex m (Z y)))) x w)+
    d*hopfCurvaturePullback c (fun y => homogeneousPolynomial a t
      (complexAffineLift (affineComplex m (Z y)))) x v w=_
  rw [he]
  unfold hopfCurvaturePullback
  rw [hopfForm_affine_pullback hAc,hopfForm_affine_pullback hPc,normalAmbientForm_apply]
  simp only [affineComplex_cartesian]
  have hD (u : E) : fderiv ℝ (fun y => affinePhase m (Z y)) x u=
      affinePhase m (fderiv ℝ Z x u) := by
    exact congrArg (fun L => L u) ((affinePhase m).hasFDerivAt.comp x hZ.hasFDerivAt).fderiv
  have hP (u : E) : fderiv ℝ (fun y => complexCartesian (normalPolynomial a t (Z y))) x u=
      fderiv ℝ (fun y => complexCartesian (normalPolynomial a t y)) (Z x) (fderiv ℝ Z x u) :=
    congrArg (fun L => L u) (fderiv_comp x
      ((normalPolynomialCartesian_smooth a t).differentiable (by simp) _) hZ)
  rw [hD,hD,hP,hP]

theorem mixedHopf_affine (a : Fin m → ℂ) (c d t : ℝ) (x v w : Affine m) :
    mixedHopfCurvaturePullback (homogeneousPolynomial a t) c d
      (fun y => complexAffineLift (affineComplex m y)) x v w=
      normalAmbientForm a c d t x v w := by
  simpa only [fderiv_id,ContinuousLinearMap.id_apply,id_eq] using
    mixedHopf_affine_pullback a c d t (Z := id) differentiableAt_id v w

theorem exists_quadric_global_affine_moser (a : Fin m → ℂ) (t : ℝ)
    {c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdhalf : d<1/2) :
    ∃ f g : Affine m → Affine m,
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧ LeftInverse g f ∧ RightInverse g f ∧
      (∀ x v w, normalAmbientForm a c d t (f x)
        (fderiv ℝ f x v) (fderiv ℝ f x w)=normalAmbientForm a c 0 t x v w) ∧
      (∀ x v w, normalAmbientForm a c 0 t (g x)
        (fderiv ℝ g x v) (fderiv ℝ g x w)=normalAmbientForm a c d t x v w) := by
  obtain ⟨f,g,hf,hg,hgf,hfg,hfr,hgr,hfζ,hgζ,hfinf,hginf,hω⟩ :=
    exists_quadric_relative_shell_map_bp240 a t hc hd hdhalf
  obtain ⟨hfC,hgC,hgfC,hfgC⟩ :=
    sphereCartesianDescend_equiv hf hg hgf hfg hfr hgr hfinf hginf hfζ hgζ
  let fC := sphereAffineDescend (complexConjugate f)
  let gC := sphereAffineDescend (complexConjugate g)
  let A := affineComplexEquiv m
  let fA : Affine m → Affine m := fun z => A.symm (fC (A z))
  let gA : Affine m → Affine m := fun z => A.symm (gC (A z))
  have hfA : ContDiff ℝ ∞ fA := A.symm.contDiff.comp (hfC.comp A.contDiff)
  have hgA : ContDiff ℝ ∞ gA := A.symm.contDiff.comp (hgC.comp A.contDiff)
  have hgfA : LeftInverse gA fA := by
    intro z
    simp only [fA,gA,ContinuousLinearEquiv.apply_symm_apply]
    have he : gC (fC (A z))=A z := hgfC (A z)
    rw [he,ContinuousLinearEquiv.symm_apply_apply]
  have hfgA : RightInverse gA fA := by
    intro z
    simp only [fA,gA,ContinuousLinearEquiv.apply_symm_apply]
    have he : fC (gC (A z))=A z := hfgC (A z)
    rw [he,ContinuousLinearEquiv.symm_apply_apply]
  have hP : ContDiff ℝ ∞ (homogeneousPolynomial a t) :=
    (homogeneousPolynomial_smooth a t).restrict_scalars ℝ
  have hωsphere (z) (hz : phaseSq z=1) (v w) :
      euclideanExteriorOneForm (homogeneousConePrimitive
        (cartesianConjugate (homogeneousPolynomial a t)) c d) (f z)
          (fderiv ℝ f z v) (fderiv ℝ f z w)=
        euclideanExteriorOneForm (homogeneousConePrimitive
          (cartesianConjugate (homogeneousPolynomial a t)) c 0) z v w := by
    apply hω z
    change (1/2:ℝ)≤phaseSq z ∧ phaseSq z≤2
    rw [hz]
    norm_num
  have hωC (x v w : Option (Fin m) → ℂ) :
      mixedHopfCurvaturePullback (homogeneousPolynomial a t) c d
        (fun y => complexAffineLift (fC y)) x v w=
      mixedHopfCurvaturePullback (homogeneousPolynomial a t) c 0 complexAffineLift x v w :=
    sphereAffineDescend_curvature hP (fun _ hz => homogeneousPolynomial_nonzero a t hz)
      (homogeneousPolynomial_homogeneous a t) hf hfr hfinf c d hωsphere x v w
  have hωA (x v w : Affine m) : normalAmbientForm a c d t (fA x)
      (fderiv ℝ fA x v) (fderiv ℝ fA x w)=normalAmbientForm a c 0 t x v w := by
    rw [←mixedHopf_affine_pullback a c d t (hfA.differentiable (by simp) x),
      ←mixedHopf_affine a c 0 t]
    have he : (fun y => complexAffineLift (affineComplex m (fA y)))=
        (fun y => complexAffineLift (fC (A y))) := by
      funext y
      rw [←affineComplexEquiv_apply]
      change complexAffineLift (A (A.symm (fC (A y))))=_
      rw [ContinuousLinearEquiv.apply_symm_apply]
    rw [he]
    have hA : (fun y : Affine m => complexAffineLift (affineComplex m y))=
        (fun y => complexAffineLift (A y)) := by
      simp only [A,affineComplexEquiv_apply]
    rw [hA]
    change mixedHopfCurvaturePullback (homogeneousPolynomial a t) c d
      (fun y => complexAffineLift (fC (A y))) x v w=
      mixedHopfCurvaturePullback (homogeneousPolynomial a t) c 0
        (fun y => complexAffineLift (A y)) x v w
    have h₁ := mixedHopfCurvaturePullback_comp hP
      (G := fun y => complexAffineLift (fC y))
      ((complexAffineLift_smooth.comp hfC).differentiable (by simp) (A x))
      A.differentiableAt (c := c) (d := d) v w
    have h₂ := mixedHopfCurvaturePullback_comp hP
      (G := complexAffineLift)
      (complexAffineLift_smooth.differentiable (by simp) (A x))
      A.differentiableAt (c := c) (d := 0) v w
    rw [h₁,h₂]
    exact hωC (A x) (fderiv ℝ A x v) (fderiv ℝ A x w)

  exact ⟨fA,gA,hfA,hgA,hgfA,hfgA,hωA,
    diffeomorphicFormPullback_inverse hfA hgA hfgA
      (normalAmbientForm a c 0 t) (normalAmbientForm a c d t) hωA⟩

end

 theorem affineRadialTarget_smooth (m : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (affineRadialTarget m c) :=
  (optionPhaseAmbient m).contDiff.comp ((fsBallMap_smooth c).comp (affinePhaseEquiv m).contDiff)

 theorem affineRadialTarget_isEmbedding (m : ℕ) {c : ℝ} (hc : 0 < c) :
    Topology.IsEmbedding (affineRadialTarget m c) :=
  (optionPhaseAmbient m).toHomeomorph.isEmbedding.comp
    ((fsBallMap_isEmbedding hc).comp (affinePhaseEquiv m).toHomeomorph.isEmbedding)

 theorem affineRadialTarget_mem (m : ℕ) {c : ℝ} (hc : 0 < c) (z : Affine m) :
    affineRadialTarget m c z ∈ openBall (m+1) (Real.pi*c) := by
  change capacity (optionPhaseAmbient m (fsBallMap c (affinePhaseEquiv m z)))<Real.pi*c
  rw [optionPhaseAmbient_capacity]
  exact mul_lt_mul_of_pos_left (fsBallMap_mem hc _) Real.pi_pos

 theorem affineRadialTarget_pullback {m : ℕ} (a : Fin m → ℂ) (t : ℝ)
    {c : ℝ} (hc : 0 ≤ c) (z v w : Affine m) :
    standardForm (fderiv ℝ (affineRadialTarget m c) z v)
      (fderiv ℝ (affineRadialTarget m c) z w)=normalAmbientForm a c 0 t z v w := by
  have hs := (fsBallMap_smooth (ι := Option (Fin m)) c).differentiable (by simp)
  have hD (u : Affine m) : fderiv ℝ (affineRadialTarget m c) z u=
      optionPhaseAmbient m (fderiv ℝ (fsBallMap c) (affinePhaseEquiv m z)
        (affinePhaseEquiv m u)) := by
    exact congrArg (fun L => L u) (((optionPhaseAmbient m).hasFDerivAt.comp z
      ((hs _).hasFDerivAt.comp z (affinePhaseEquiv m).hasFDerivAt)).fderiv)
  rw [hD,hD,optionPhaseAmbient_form,fsBallMap_pullback hc,normalAmbientForm_apply]
  simp only [affinePhaseEquiv_apply,mul_zero,sub_zero,one_mul,zero_mul,add_zero]

 theorem exists_polynomial_target_embedding_bp240_oai {m : ℕ} (a : Fin m → ℂ) (t : ℝ)
    {c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdhalf : d<1/2) :
    ∃ g : Affine m → Ambient (m+1),ContDiff ℝ ∞ g ∧ Topology.IsEmbedding g ∧
      (∀ x,g x∈openBall (m+1) (Real.pi*c)) ∧
      ∀ x v w,standardForm (fderiv ℝ g x v) (fderiv ℝ g x w)=
        normalAmbientForm a c d t x v w := by
  obtain ⟨f,g,hf,hg,hgf,hfg,_hωf,hωg⟩ := exists_quadric_global_affine_moser a t hc hd hdhalf
  let e : Affine m ≃ₜ Affine m :=
    { toEquiv := ⟨g,f,hfg,hgf⟩
      continuous_toFun := hg.continuous
      continuous_invFun := hf.continuous }
  refine ⟨affineRadialTarget m c ∘ g,(affineRadialTarget_smooth m c).comp hg,
    (affineRadialTarget_isEmbedding m hc).comp e.isEmbedding,
    fun x => affineRadialTarget_mem m hc (g x),?_⟩
  intro x v w
  rw [fderiv_comp x ((affineRadialTarget_smooth m c).differentiable (by simp) (g x))
    (hg.differentiable (by simp) x)]
  change standardForm (fderiv ℝ (affineRadialTarget m c) (g x) (fderiv ℝ g x v))
    (fderiv ℝ (affineRadialTarget m c) (g x) (fderiv ℝ g x w))=_
  rw [affineRadialTarget_pullback a t hc.le,hωg]

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_polynomial_target_embedding_bp240_oai := @OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_polynomial_target_embedding_bp240_oai
