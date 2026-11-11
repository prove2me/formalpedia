-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.CubicModel.cubic_bubble_target_packing_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:29.99802+00:00
-- url     : https://prove2.me/submissions/54c36611-a264-44e7-936f-1f9cb57b5dca

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_exists_cubic_bubble_separated_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_degree_relative_shell_maps_bp240

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
variable {ι : Type*} [Fintype ι]

theorem standardLiouville_smooth : ContDiff ℝ ∞ (standardLiouville (ι := ι)) :=
  (phaseArea (ι := ι)).contDiff.const_smul _

theorem standardLiouville_exterior (z : PlanePhase ι) :
    euclideanExteriorOneForm standardLiouville z=phaseArea := by
  have hd : fderiv ℝ (standardLiouville (ι := ι)) z=(1/2:ℝ) • phaseArea :=
    ((phaseArea (ι := ι)).hasFDerivAt.const_smul (1/2:ℝ)).fderiv
  ext u v
  simp only [euclideanExteriorOneForm,hd,sub_apply,
    ContinuousLinearMap.flip_apply,smul_apply,smul_eq_mul]
  rw [phaseArea_skew v u]
  ring

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
-- module Solutions.OAIQ240_BP.BallPacking_Layers_LayerBallEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology BigOperators
open Set Function

theorem complexSplitPhase_form (m : ℕ) (v w : Ambient (m+1)) :
    productForm phaseArea (complexSplitPhase m v) (complexSplitPhase m w)=standardForm v w := by
  simp only [productForm_apply,phaseArea_apply,complexSplitPhase_apply,standardForm,Fin.sum_univ_succ]
  rfl


end

open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_NonautonomousManifoldFlow
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply
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

@[simp] theorem successorStandardForm_apply (m : ℕ) (v w : Ambient (m+1)) :
    successorStandardForm m v w = standardForm v w := complexSplitPhase_form m v w

 theorem isBallEmbedding_iff_formNeighborhoodEmbedding {m : ℕ} {r : ℝ}
    {f : Ambient (m+1) → Ambient (m+1)} :
    IsBallEmbedding r f ↔ FormNeighborhoodEmbedding (closedBall (m+1) r)
      (fun _ => successorStandardForm m) (fun _ => successorStandardForm m) f := by
  constructor
  · rintro ⟨U,hU,hBU,hs,he,hform⟩
    refine ⟨U,hU,hBU,hs.contMDiffOn,he,?_⟩
    intro x hx v w
    rw [mfderiv_eq_fderiv]
    change successorStandardForm m (fderiv ℝ f x v) (fderiv ℝ f x w) = successorStandardForm m v w
    erw [successorStandardForm_apply, successorStandardForm_apply]
    exact hform x hx v w
  · rintro ⟨U,hU,hBU,hs,he,hform⟩
    refine ⟨U,hU,hBU,hs.contDiffOn,he,?_⟩
    intro x hx v w
    have hh := hform x hx v w
    rw [mfderiv_eq_fderiv] at hh
    change successorStandardForm m (fderiv ℝ f x v) (fderiv ℝ f x w) = successorStandardForm m v w at hh
    erw [successorStandardForm_apply, successorStandardForm_apply] at hh
    exact hh

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

 theorem quadricLiftMonomial_homogeneous {n J K : ℕ} (hJ : J≤n) (hK : K≤n)
    (ζ : ℂ) (x : Fin 4 → ℂ) :
    quadricLiftMonomial n J K (ζ • x)=ζ^n*quadricLiftMonomial n J K x := by
  have he := (lift_exponents hJ hK).2.2.2
  unfold quadricLiftMonomial
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow]
  calc
    _=ζ^(liftAlpha n J K+liftBeta n J K+liftGamma n J K+liftDelta n J K)*
      (x 0^liftAlpha n J K*x 1^liftBeta n J K*x 2^liftGamma n J K*x 3^liftDelta n J K) := by
        simp only [pow_add] <;> ring
    _=_ := by rw [he]

 theorem quadricLiftPolynomial_smooth (n : ℕ) (q : MvPolynomial (Fin 2) ℂ) :
    ContDiff ℂ ∞ (quadricLiftPolynomial n q) := by
  unfold quadricLiftPolynomial
  exact ContDiff.sum (fun _ _ => contDiff_const.mul (quadricLiftMonomial_smooth _ _ _))

 theorem quadricLiftPolynomial_homogeneous {n : ℕ} (q : MvPolynomial (Fin 2) ℂ)
    (h0 : q.degreeOf 0≤n) (h1 : q.degreeOf 1≤n) (ζ : ℂ) (x : Fin 4 → ℂ) :
    quadricLiftPolynomial n q (ζ • x)=ζ^n*quadricLiftPolynomial n q x := by
  unfold quadricLiftPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [quadricLiftMonomial_homogeneous ((MvPolynomial.monomial_le_degreeOf 0 hd).trans h0)
    ((MvPolynomial.monomial_le_degreeOf 1 hd).trans h1)]
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

 theorem coefficientPolynomial_degreeOf {D m : ℕ} (hm : 2*m≤D)
    (i : WeightedHomogeneousIndex) (j : Fin 2) : (coefficientPolynomial D m i).degreeOf j≤D-m := by
  have h := degreeOf_mul_le j (X 0^(coefficientPowers D m i).1 : MvPolynomial (Fin 2) ℂ)
    (X 1^(coefficientPowers D m i).2)
  have hb := coefficientPowers_bounds hm i
  fin_cases j <;> simp [degreeOf_X_pow_of_ne] at h
  · exact h.trans hb.1
  · exact h.trans hb.2.1

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

 theorem firstQuadric_homogeneous (ζ : ℂ) (x : Fin 4 → ℂ) :
    firstQuadric (ζ • x)=ζ^2*firstQuadric x := by
  simp only [firstQuadric,Pi.smul_apply,smul_eq_mul]
  ring

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

 theorem liftedSection_homogeneous {L S A B : ℕ} (hAS : A<S) (hS : 2*S<L)
    (hB : 3*B<L+S) (k : TrapezoidWeight A B) (i : WeightedHomogeneousIndex)
    (ζ : ℂ) (x : Fin 4 → ℂ) : liftedSection L S k i (ζ • x)=ζ^L*liftedSection L S k i x := by
  obtain ⟨hm,hdeg,_,_⟩ := inner_lattice_bounds hAS hS hB k
  have hd (j : Fin 2) := (cubicNormalSection_degreeOf hm (latticeIndex k).2 i j).trans hdeg
  have he : 2*(latticeIndex k).1+(L-2*(latticeIndex k).1)=L := by
    have h := k.property.1
    dsimp [Radial.latticeIndex]
    omega
  rw [liftedSection,firstQuadric_homogeneous,quadricLiftPolynomial_homogeneous _ (hd 0) (hd 1)]
  simp only [mul_pow,←pow_mul]
  rw [show ζ^L=ζ^(2*(latticeIndex k).1)*ζ^(L-2*(latticeIndex k).1) by rw [←pow_add,he]]
  unfold liftedSection
  ring

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

 theorem radialSymplectization_apply (z : PlanePhase ι) (α : PlanePhase ι →L[ℝ] ℝ)
    (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ) (v w : PlanePhase ι) :
    radialSymplectization z α C v w=
      2*(phaseDot z v*α w-α v*phaseDot z w)+phaseSq z*C v w := by
  simp only [radialSymplectization,add_apply,smul_apply,sub_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cartesianConjugate_smooth {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (cartesianConjugate P) :=
  (complexCartesian (ι := κ)).contDiff.comp (hP.comp (complexCartesian (ι := ι)).symm.contDiff)

end
section

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem homogeneousDegree_euler {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℂ ∞ P)
    {ℓ : ℕ} (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z) (z : ι → ℂ) :
    fderiv ℂ P z z=(ℓ:ℂ)•P z := by
  have hf := (hP.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)
  have hf' : HasFDerivAt P (fderiv ℂ P z) ((1:ℂ)•z) := by simpa only [one_smul] using hf.hasFDerivAt
  have hd := hf'.comp_hasDerivAt (1:ℂ) ((hasDerivAt_id (1:ℂ)).smul_const z)
  have he : (fun b : ℂ => P (b•z))=(fun b : ℂ => b^ℓ•P z) := funext fun b => hPs b z
  have hd' : HasDerivAt (fun b : ℂ => b^ℓ•P z) ((ℓ:ℂ)•P z) 1 := by
    convert! (((hasDerivAt_id (1:ℂ)).pow ℓ).smul_const (P z)) using 1; simp
  simp only [Function.comp_def,id_eq] at hd
  rw [he] at hd
  simpa only [one_smul] using hd.unique hd'

 theorem cartesianConjugate_fderiv {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℂ ∞ P)
    (z v : PlanePhase ι) : fderiv ℝ (cartesianConjugate P) z v=
      complexCartesian (fderiv ℂ P (complexCartesian.symm z) (complexCartesian.symm v)) := by
  have hh := (hP.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (complexCartesian.symm z)).hasFDerivAt.restrictScalars ℝ
  have hd := complexCartesian.toContinuousLinearMap.hasFDerivAt.comp z
    (hh.comp z (complexCartesian (ι := ι)).symm.hasFDerivAt)
  exact congrArg (fun L => L v) hd.fderiv

 theorem cartesianConjugate_euler {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℂ ∞ P)
    {ℓ : ℕ} (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z) (z : PlanePhase ι) :
    fderiv ℝ (cartesianConjugate P) z z=(ℓ:ℝ)•cartesianConjugate P z := by
  rw [cartesianConjugate_fderiv hP,homogeneousDegree_euler hP hPs]
  rw [show (ℓ:ℂ)•P (complexCartesian.symm z)=(ℓ:ℝ)•P (complexCartesian.symm z) by
    ext i; simp [Pi.smul_apply,Complex.real_smul]]
  exact map_smul _ _ _

 theorem cartesianConjugate_J {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℂ ∞ P)
    (z v : PlanePhase ι) : fderiv ℝ (cartesianConjugate P) z (phaseJ v)=
      phaseJ (fderiv ℝ (cartesianConjugate P) z v) := by
  have hJ : complexCartesian.symm (phaseJ v)=Complex.I•complexCartesian.symm v := by
    apply complexCartesian.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply,complexCartesian_I]
  rw [cartesianConjugate_fderiv hP,cartesianConjugate_fderiv hP,hJ,map_smul,complexCartesian_I]

 theorem cartesianConjugate_nonzero {P : (ι → ℂ) → (κ → ℂ)}
    (hPn : ∀ z,z≠0 → P z≠0) {z : PlanePhase ι} (hz : z≠0) : cartesianConjugate P z≠0 := by
  intro he
  have hn : complexCartesian.symm z≠0 := by
    intro hh
    exact hz (by simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero] using congrArg complexCartesian hh)
  exact hPn _ hn (complexCartesian.injective (he.trans (map_zero _).symm))

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

omit [Fintype ι] in
 theorem homogeneousVeronese_nonzero (m : ℕ) {z : ι → ℂ} (hz : z≠0) :
    homogeneousVeronese m z≠0 := by
  classical
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hz
  intro h
  have hh := congrFun h (fun _ => i)
  simp only [homogeneousVeronese,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Pi.zero_apply] at hh
  exact pow_ne_zero m hi hh

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
 theorem bubbleCoordinates_smul (ε ζ : ℂ) (x : Option ι → ℂ) :
    bubbleCoordinates ε (ζ•x)=ζ•bubbleCoordinates ε x := by
  ext i
  cases i <;> simp [bubbleCoordinates,Pi.smul_apply,smul_eq_mul,mul_left_comm]

omit [Fintype ι] in
 theorem homogeneousBubble_homogeneous {L m : ℕ} (hm : m≤L) (p : ℕ)
    (ε ζ : ℂ) (x : Option ι → ℂ) :
    homogeneousBubble L m p ε (ζ•x)=ζ^L•homogeneousBubble L m p ε x := by
  ext j
  simp only [homogeneousBubble,Pi.smul_apply,smul_eq_mul,mul_pow,bubbleCoordinates_smul,
    homogeneousVeronese_homogeneous]
  rw [show ζ^L=ζ^(L-m)*ζ^m by rw [←pow_add,Nat.sub_add_cancel hm]]
  ring

variable {κ : Type} [Fintype κ]

 theorem bubblePolynomial_joint_smooth (L m p N : ℕ) {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℂ ∞ P) :
    ContDiff ℂ ∞ (fun a : ℂ×(Option ι → ℂ) => bubblePolynomial L m p N P a.1 a.2) := by
  apply contDiff_pi.mpr
  rintro (i|(j|k))
  · exact (contDiff_apply ℂ ℂ i).comp (hP.comp contDiff_snd)
  · exact (contDiff_apply ℂ ℂ j).comp (homogeneousBubble_joint_smooth L m p)
  · exact (contDiff_fst.pow N).mul ((contDiff_apply ℂ ℂ k).comp ((homogeneousVeronese_smooth L).comp contDiff_snd))

omit [Fintype ι] [Fintype κ] in
 theorem bubblePolynomial_homogeneous {L m : ℕ} (hm : m≤L) (p N : ℕ)
    {P : (Option ι → ℂ) → (κ → ℂ)} (hP : ∀ (ζ : ℂ) x,P (ζ•x)=ζ^L•P x)
    (ε ζ : ℂ) (x : Option ι → ℂ) :
    bubblePolynomial L m p N P ε (ζ•x)=ζ^L•bubblePolynomial L m p N P ε x := by
  ext i
  rcases i with (i|(j|k))
  · exact congrFun (hP ζ x) i
  · exact congrFun (homogeneousBubble_homogeneous hm p ε ζ x) j
  · simp only [bubblePolynomial,Sum.elim_inr,homogeneousVeronese_homogeneous,Pi.smul_apply,smul_eq_mul]
    ring

omit [Fintype ι] [Fintype κ] in
 theorem bubblePolynomial_nonzero (L m p N : ℕ) (P : (Option ι → ℂ) → (κ → ℂ))
    {ε : ℂ} (hε : ε≠0) {x : Option ι → ℂ} (hx : x≠0) :
    bubblePolynomial L m p N P ε x≠0 := by
  intro h
  apply homogeneousVeronese_nonzero L hx
  funext j
  have hh := congrFun h (Sum.inr (Sum.inr j))
  change ε^N*homogeneousVeronese L x j=0 at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero N hε)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff BigOperators
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem distinguishedHomogeneousCoordinates_smooth :
     ContDiff ℂ ∞ distinguishedHomogeneousCoordinates := by
   apply contDiff_pi.mpr
   intro i
   fin_cases i <;> exact contDiff_apply ℂ ℂ _

 theorem distinguishedHomogeneousCoordinates_smul (ζ : ℂ) (x : Option (Fin 3) → ℂ) :
     distinguishedHomogeneousCoordinates (ζ•x)=ζ•distinguishedHomogeneousCoordinates x := by
   ext i
   fin_cases i <;> rfl

 theorem cubicBubblePolynomial_joint_smooth {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ) :
     ContDiff ℂ ∞ (fun a : ℂ×(Option (Fin 3) → ℂ) =>
       cubicBubblePolynomial (A := A) (B := B) L S m p N t δ a.1 a.2) := by
   exact bubblePolynomial_joint_smooth L m p N
     ((outerPolynomial_smooth L S t δ).comp distinguishedHomogeneousCoordinates_smooth)

 theorem cubicBubblePolynomial_homogeneous {L S A B m : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hm : m≤L)
     (p N : ℕ) (t δ : ℝ) (ε ζ : ℂ) (x : Option (Fin 3) → ℂ) :
     cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε (ζ•x)=
       ζ^L•cubicBubblePolynomial L S m p N t δ ε x := by
   apply bubblePolynomial_homogeneous hm
   intro ζ x
   simp only [Function.comp_def,distinguishedHomogeneousCoordinates_smul]
   ext ki
   simp only [outerPolynomial,Pi.smul_apply,smul_eq_mul,
     liftedSection_homogeneous hAS hS hB]
   ring

 theorem cubicBubblePolynomial_nonzero {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ)
     {ε : ℂ} (hε : ε≠0) {x : Option (Fin 3) → ℂ} (hx : x≠0) :
     cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε x≠0 := by
   exact bubblePolynomial_nonzero L m p N _ hε hx

end PackingSufficiencySupport.CubicModel

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

 theorem degreeHopfPrimitive_smoothAt {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (q c d : ℝ) :
    ContDiffAt ℝ ∞ (degreeHopfPrimitive q F c d) z :=
  ((hopfPrimitive_smoothAt c hz).const_smul (1-q*d)).add
    ((primitivePullback_smoothAt (hopfPrimitive_smoothAt c hFz) hF).const_smul d)

 theorem degreeHopfForm_eq {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (q c d : ℝ) :
    degreeHopfForm q F c d z=(1-q*d)•hopfForm c z+
      d•(hopfForm c (F z)).bilinearComp (fderiv ℝ F z) (fderiv ℝ F z) := by
  have h₀ := (hopfPrimitive_smoothAt c hz).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h₁ := (primitivePullback_smoothAt (hopfPrimitive_smoothAt c hFz) hF).differentiableAt (by simp)
  rw [degreeHopfForm,degreeHopfPrimitive,euclideanExteriorOneForm_add (h₀.const_smul _) (h₁.const_smul _),
    euclideanExteriorOneForm_smul _ h₀,euclideanExteriorOneForm_smul _ h₁,
    primitivePullback_exteriorAt (hopfPrimitive_smoothAt c hFz) hF]
  rfl

 theorem degreeConePrimitive_exterior {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (q c d : ℝ) :
    euclideanExteriorOneForm (degreeConePrimitive q F c d) z=
      radialSymplectization z (degreeHopfPrimitive q F c d z) (degreeHopfForm q F c d z) := by
  have ha := (degreeHopfPrimitive_smoothAt hF hz hFz q c d).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := (phaseSq_hasFDerivAt z).smul ha.hasFDerivAt
  rw [euclideanExteriorOneForm,show fderiv ℝ (degreeConePrimitive q F c d) z=_ from he.fderiv]
  ext v w
  simp only [sub_apply,ContinuousLinearMap.flip_apply,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,radialSymplectization_apply,
    degreeHopfForm,euclideanExteriorOneForm]
  ring

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {q : ℝ} {ℓ : ℕ}

theorem degreeHopfCurvaturePullback_gauge {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z)
    {S : E → ℂ} {G : E → (ι → ℂ)} {x : E}
    (hS : DifferentiableAt ℝ S x) (hG : DifferentiableAt ℝ G x)
    (hSx : S x≠0) (hGx : G x≠0) (c d : ℝ) (v w : E) :
    degreeHopfCurvaturePullback q P c d (fun y => S y•G y) x v w=
      degreeHopfCurvaturePullback q P c d G x v w := by
  have hGxc : complexCartesian (G x)≠0 := by
    intro h; exact hGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have hPGxc : complexCartesian (P (G x))≠0 := by
    intro h; exact hPn (G x) hGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have he : (fun y => P (S y•G y))=(fun y => (S y)^ℓ•P (G y)) := funext fun y => hPs _ _
  unfold degreeHopfCurvaturePullback
  change (1-q*d)*hopfCurvaturePullback c (fun y => S y•G y) x v w+
    d*hopfCurvaturePullback c (fun y => P (S y•G y)) x v w=_
  rw [he]
  unfold hopfCurvaturePullback
  rw [hopfForm_variable_gauge hS hG hSx hGxc]
  have h₂ := hopfForm_variable_gauge (S := fun y => S y^ℓ) (G := fun y => P (G y))
    (hS.pow ℓ) ((hP.differentiable (by simp) (G x)).comp x hG)
      (pow_ne_zero ℓ hSx) hPGxc c v w
  exact congrArg (fun u : ℝ => (1-q*d)*hopfCurvaturePullback c G x v w+d*u) h₂

theorem degreeHopfCurvaturePullback_eq {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) {G : E → (ι → ℂ)} {x : E}
    (hG : DifferentiableAt ℝ G x) (hGx : G x≠0) (hPGx : P (G x)≠0)
    (c d : ℝ) (v w : E) :
    degreeHopfCurvaturePullback q P c d G x v w=
      degreeHopfForm q (cartesianConjugate P) c d (complexCartesian (G x))
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
  rw [degreeHopfForm_eq (cartesianConjugate_smooth hP).contDiffAt hz hPz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,
    cartesianConjugate_cartesian,degreeHopfCurvaturePullback,hopfCurvaturePullback,hD]

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

 theorem degreeAffineForm_zero (q : ℝ) (P : (Option ι → ℂ) → (κ → ℂ)) (c : ℝ)
    (x v w : ι → ℂ) : degreeAffineForm q P c 0 x v w=
      affineFSForm c (complexCartesian x) (complexCartesian v) (complexCartesian w) := by
  rw [degreeAffineForm_apply]
  simp only [degreeHopfCurvaturePullback,mul_zero,sub_zero,one_mul,zero_mul,add_zero]
  simpa only [hopfCurvaturePullback,fderiv_id,ContinuousLinearMap.id_apply,Function.id_def,ContinuousLinearEquiv.fderiv,
    ContinuousLinearEquiv.coe_coe] using hopfForm_affine_pullback (ι := ι) (Z := id)
      (x := x) differentiableAt_id c v w

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldExteriorNaturality
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
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

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem degreeConePrimitive_zero (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c : ℝ)
    (z : PlanePhase ι) : degreeConePrimitive q F c 0 z=c•standardLiouville z := by
  by_cases hz : z=0
  · subst z
    simp [degreeConePrimitive,degreeHopfPrimitive,hopfPrimitive,standardLiouville,phaseSq]
  · ext v
    simp only [degreeConePrimitive,degreeHopfPrimitive,mul_zero,sub_zero,one_smul,
      zero_smul,add_zero,hopfPrimitive,standardLiouville,smul_apply,smul_eq_mul]
    field_simp [(phaseSq_pos hz).ne']

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
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
 theorem splitInclusion_isSmoothEmbedding (L : (F × G) ≃L[ℝ] E) :
    IsSmoothEmbedding 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (splitInclusion L) := by
  have hi : IsImmersionOfComplement G 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (splitInclusion L) := by
    intro x
    apply IsImmersionAtOfComplement.mk_of_continuousAt (splitInclusion L).continuous.continuousAt L
      (chartAt F x) (chartAt E (splitInclusion L x)) (mem_chart_source F x)
      (mem_chart_source E (splitInclusion L x))
      (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (splitInclusion L x))
    intro y _
    simp [splitInclusion,chartAt_self_eq]
  refine ⟨hi.isImmersion,?_⟩
  exact L.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkLeft (0:G))

end

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

variable {ι : Type} [Fintype ι]

 theorem phaseInfinity_left : (phaseInfinityProjection (ι := ι)).comp phaseInfinityInclusion=ContinuousLinearMap.id ℝ _ := rfl
 theorem phaseInfinity_embedding : IsSmoothEmbedding 𝓘(ℝ,PlanePhase ι) 𝓘(ℝ,PlanePhase (Option ι)) ∞ (phaseInfinityInclusion (ι := ι)) := by
  unfold phaseInfinityInclusion
  exact splitInclusion_isSmoothEmbedding (phaseOptionSplit (ι := ι))
 theorem phaseInfinity_dot (z v : PlanePhase ι) :
    phaseDot (phaseInfinityInclusion z) (phaseInfinityInclusion v)=phaseDot z v := by
  simp only [phaseDot_apply,Fintype.sum_option,phaseInfinityInclusion_none,phaseInfinityInclusion_some,
    Prod.fst_zero,Prod.snd_zero,mul_zero,zero_add]
 theorem phaseInfinity_area (z v : PlanePhase ι) :
    phaseArea (phaseInfinityInclusion z) (phaseInfinityInclusion v)=phaseArea z v := by
  simp only [phaseArea_apply,Fintype.sum_option,phaseInfinityInclusion_none,phaseInfinityInclusion_some,
    Prod.fst_zero,Prod.snd_zero,mul_zero,sub_zero,zero_add]
 theorem phaseInfinity_J (z : PlanePhase ι) : phaseInfinityInclusion (phaseJ z)=phaseJ (phaseInfinityInclusion z) := by
  ext j <;> cases j <;> simp only [phaseInfinityInclusion_none,phaseInfinityInclusion_some,phaseJ_apply,
    Prod.fst_zero,Prod.snd_zero,neg_zero]
 theorem phaseInfinity_range (z : PlanePhase (Option ι)) : z∈range (phaseInfinityInclusion (ι := ι)) ↔ z none=0 := by
  constructor
  · rintro ⟨x,rfl⟩; rfl
  · intro hz
    refine ⟨fun i => z (some i),?_⟩
    funext j
    cases j with
    | none => exact hz.symm
    | some i => rfl
 theorem phaseInfinity_complex_range (z : PlanePhase (Option ι)) :
    z∈range (phaseInfinityInclusion (ι := ι)) ↔ complexCartesian.symm z none=0 := by
  rw [phaseInfinity_range]
  change z none=0 ↔ (⟨(z none).1,(z none).2⟩ : ℂ)=0
  constructor
  · intro hz; simp only [hz,Prod.fst_zero,Prod.snd_zero]; rfl
  · intro hz
    have hr := congrArg Complex.re hz
    have hi := congrArg Complex.im hz
    exact Prod.ext hr hi

 theorem phaseUnitDiagonal_eq_rotate {ζ : ℂ} (hζ : Complex.normSq ζ=1) (z : PlanePhase ι) :
    phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z=phaseRotate ζ.arg z := by
  have hn : ‖ζ‖=1 := by
    have hh := Complex.sq_norm ζ
    rw [hζ] at hh
    nlinarith [norm_nonneg ζ]
  have hne : ζ≠0 := by intro hh; simp [hh] at hn
  ext i <;> simp only [phaseUnitDiagonal_apply,phaseDiagonal,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,complexCartesian_apply,complexDiagonal_apply,
    Complex.mul_re,Complex.mul_im,phaseRotate_apply,Pi.add_apply,Pi.smul_apply,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,phaseJ_apply,
    Complex.cos_arg hne,Complex.sin_arg,hn,div_one]
  · change ζ.re*(z i).1-ζ.im*(z i).2=ζ.re*(z i).1+ζ.im*(-(z i).2); ring
  · change ζ.re*(z i).2+ζ.im*(z i).1=ζ.re*(z i).2+ζ.im*(z i).1; rfl

end

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

variable {q : ℝ} {ℓ : ℕ}

theorem degreeHopfCurvaturePullback_sphereLift {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z)
    {Z : E → (ι → ℂ)} {x : E} (hZ : DifferentiableAt ℝ Z x)
    (c d : ℝ) (v w : E) :
    degreeHopfCurvaturePullback q P c d (fun y => complexSphereLift (Z y)) x v w=
      degreeHopfCurvaturePullback q P c d (fun y => complexAffineLift (Z y)) x v w := by
  have hS : DifferentiableAt ℝ (fun y => (affineSphereScale (Z y) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((affineSphereScale_smooth.differentiable (by simp) (Z x)).comp x hZ)
  have hG : DifferentiableAt ℝ (fun y => complexAffineLift (Z y)) x :=
    (complexAffineLift_smooth.differentiable (by simp) (Z x)).comp x hZ
  have hGx : complexAffineLift (Z x)≠0 := by
    intro he
    have hh := congrFun he none
    exact one_ne_zero (by simpa only [complexAffineLift_none,Pi.zero_apply] using hh)
  exact degreeHopfCurvaturePullback_gauge hP hPn hPs hS hG
    (Complex.ofReal_ne_zero.mpr (affineSphereScale_pos _).ne') hGx c d v w

theorem degreeHopfCurvaturePullback_chart_normalize {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z)
    {G : E → (Option ι → ℂ)} {x : E}
    (hG : DifferentiableAt ℝ G x) (hGn : ∀ y,G y none≠0)
    (c d : ℝ) (v w : E) :
    degreeHopfCurvaturePullback q P c d (fun y => complexSphereLift (complexAffineQuotient (G y))) x v w=
      degreeHopfCurvaturePullback q P c d G x v w := by
  have he : (fun y => complexSphereLift (complexAffineQuotient (G y)))=
      (fun y => complexQuotientGauge (G y)•G y) :=
    funext fun y => complexSphereLift_quotient_gauge (hGn y)
  rw [he]
  exact degreeHopfCurvaturePullback_gauge hP hPn hPs
    (((complexQuotientGauge_smoothAt (hGn x)).differentiableAt (by simp)).comp x hG)
    hG (complexQuotientGauge_ne (hGn x))
    (fun he => hGn x (by simpa only [Pi.zero_apply] using congrFun he none)) c d v w

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

theorem degreeCone_sphere_tangent {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : phaseSq z=1) (hFz : F z≠0)
    (c d : ℝ) {v w : PlanePhase ι} (hv : phaseDot z v=0) (hw : phaseDot z w=0) :
    euclideanExteriorOneForm (degreeConePrimitive q F c d) z v w=degreeHopfForm q F c d z v w := by
  have hzn : z≠0 := by intro he; simp [he,phaseSq] at hz
  rw [degreeConePrimitive_exterior hF hzn hFz,radialSymplectization_apply,hv,hw,hz]
  ring

theorem degree_cone_flow_sphere_pullback {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hFn : ∀ z,z≠0 → F z≠0)
    {f : PlanePhase ι → PlanePhase ι} (hf : ContDiff ℝ ∞ f)
    (hfr : ∀ z,phaseSq (f z)=phaseSq z) (c d : ℝ)
    (hfω : ∀ z,phaseSq z=1 → ∀ v w,
      euclideanExteriorOneForm (degreeConePrimitive q F c d) (f z)
        (fderiv ℝ f z v) (fderiv ℝ f z w)=
      euclideanExteriorOneForm (degreeConePrimitive q F c 0) z v w)
    {N : E → PlanePhase ι} {x : E} (hN : DifferentiableAt ℝ N x)
    (hNs : ∀ y,phaseSq (N y)=1) (v w : E) :
    degreeHopfForm q F c d (f (N x))
      (fderiv ℝ (fun y => f (N y)) x v) (fderiv ℝ (fun y => f (N y)) x w)=
    degreeHopfForm q F c 0 (N x) (fderiv ℝ N x v) (fderiv ℝ N x w) := by
  have hNz : N x≠0 := by intro he; have hh := hNs x; simp [he,phaseSq] at hh
  have hfNs : ∀ y,phaseSq (f (N y))=1 := fun y => (hfr _).trans (hNs y)
  have hfNz : f (N x)≠0 := by intro he; have hh := hfNs x; simp [he,phaseSq] at hh
  have hfN : DifferentiableAt ℝ (fun y => f (N y)) x :=
    (hf.differentiable (by simp) (N x)).comp x hN
  rw [←degreeCone_sphere_tangent hF.contDiffAt (hfNs x) (hFn _ hfNz) c d
    (sphere_map_fderiv_tangent hfN hfNs v) (sphere_map_fderiv_tangent hfN hfNs w),
    ←degreeCone_sphere_tangent hF.contDiffAt (hNs x) (hFn _ hNz) c 0
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

end

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {q : ℝ} {ℓ : ℕ}

theorem sphereAffineDescend_degree_curvature {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z)
    {f : PlanePhase (Option ι) → PlanePhase (Option ι)} (hf : ContDiff ℝ ∞ f)
    (hfr : ∀ z,phaseSq (f z)=phaseSq z)
    (hfinf : ∀ z,phaseSq z=1 →
      (complexCartesian.symm (f z) none=0 ↔ complexCartesian.symm z none=0))
    (c d : ℝ)
    (hfω : ∀ z,phaseSq z=1 → ∀ v w,
      euclideanExteriorOneForm (degreeConePrimitive q (cartesianConjugate P) c d) (f z)
        (fderiv ℝ f z v) (fderiv ℝ f z w)=
      euclideanExteriorOneForm (degreeConePrimitive q (cartesianConjugate P) c 0) z v w)
    (x v w : ι → ℂ) :
    degreeHopfCurvaturePullback q P c d
        (fun y => complexAffineLift (sphereAffineDescend (complexConjugate f) y)) x v w=
      degreeHopfCurvaturePullback q P c 0 complexAffineLift x v w := by
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
  have hω : degreeHopfCurvaturePullback q P c d G x v w=
      degreeHopfCurvaturePullback q P c 0 complexSphereLift x v w := by
    rw [degreeHopfCurvaturePullback_eq hP (hG.differentiable (by simp) x) (hGpc x) (hPn _ (hGpc x)),
      degreeHopfCurvaturePullback_eq hP (complexSphereLift_smooth.differentiable (by simp) x)
        (hNpc x) (hPn _ (hNpc x))]
    simpa only [G,ContinuousLinearEquiv.apply_symm_apply,Function.comp_def] using
      degree_cone_flow_sphere_pullback (cartesianConjugate_smooth hP) hFn hf hfr c d hfω
        (((complexCartesian (ι := Option ι)).contDiff.comp complexSphereLift_smooth).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)
        complexSphereLift_sq v w
  calc
    _=degreeHopfCurvaturePullback q P c d
        (fun y => complexSphereLift (sphereAffineDescend (complexConjugate f) y)) x v w :=
      (degreeHopfCurvaturePullback_sphereLift hP hPn hPs (hD.differentiable (by simp) x) c d v w).symm
    _=degreeHopfCurvaturePullback q P c d G x v w :=
      degreeHopfCurvaturePullback_chart_normalize hP hPn hPs (hG.differentiable (by simp) x) hGn c d v w
    _=degreeHopfCurvaturePullback q P c 0 complexSphereLift x v w := hω
    _=_ := degreeHopfCurvaturePullback_sphereLift hP hPn hPs differentiableAt_id c 0 v w

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_SphereCartesianDescent
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply
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

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem exists_degree_global_affine_moser {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℂ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    {ℓ : ℕ} (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z)
    {c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdℓ : (ℓ:ℝ)*d<1) :
    ∃ f g : (ι → ℂ) → (ι → ℂ),
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧ LeftInverse g f ∧ RightInverse g f ∧
      (∀ x v w,degreeAffineForm (ℓ:ℝ) P c d (f x) (fderiv ℝ f x v) (fderiv ℝ f x w)=
        degreeAffineForm (ℓ:ℝ) P c 0 x v w) ∧
      (∀ x v w,degreeAffineForm (ℓ:ℝ) P c 0 (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)=
        degreeAffineForm (ℓ:ℝ) P c d x v w) := by
  have hPr := hP.restrict_scalars ℝ
  have hF := cartesianConjugate_smooth hPr
  obtain ⟨f,g,hf,hg,hgf,hfg,hfr,hgr,hfe,hge,hfc,hgc,hω⟩ := exists_degree_relative_shell_maps_bp240
    hF (fun z hz => cartesianConjugate_nonzero hPn hz)
    (cartesianConjugate_euler hP hPs) (cartesianConjugate_J hP)
    phaseInfinityInclusion phaseInfinityProjection phaseInfinity_left phaseInfinity_embedding
    phaseInfinity_dot phaseInfinity_area phaseInfinity_J (b := 2) (by norm_num : 0<(1/2:ℝ))
    hc hd (Nat.cast_nonneg ℓ) hdℓ
  have hK (z : PlanePhase (Option ι)) (hz : phaseSq z=1) : z∈phaseShell (1/2:ℝ) 2 := by
    change (1/2:ℝ)≤phaseSq z ∧ phaseSq z≤2
    rw [hz]; norm_num
  have hfinf (z : PlanePhase (Option ι)) (_hz : phaseSq z=1) :
      complexCartesian.symm (f z) none=0 ↔ complexCartesian.symm z none=0 := by
    simpa only [phaseInfinity_complex_range] using hfe z
  have hginf (z : PlanePhase (Option ι)) (_hz : phaseSq z=1) :
      complexCartesian.symm (g z) none=0 ↔ complexCartesian.symm z none=0 := by
    simpa only [phaseInfinity_complex_range] using hge z
  have hfζ (ζ : ℂ) (hζ : Complex.normSq ζ=1) (z : PlanePhase (Option ι)) (hz : phaseSq z=1) :
      f (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (f z) := by
    simp only [phaseUnitDiagonal_eq_rotate]
    exact hfc ζ.arg z (hK z hz)
  have hgζ (ζ : ℂ) (hζ : Complex.normSq ζ=1) (z : PlanePhase (Option ι)) (hz : phaseSq z=1) :
      g (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (g z) := by
    simp only [phaseUnitDiagonal_eq_rotate]
    exact hgc ζ.arg z (hK z hz)
  obtain ⟨hfC,hgC,hgfC,hfgC⟩ := sphereCartesianDescend_equiv hf hg hgf hfg hfr hgr hfinf hginf hfζ hgζ
  let fC := sphereAffineDescend (complexConjugate f)
  let gC := sphereAffineDescend (complexConjugate g)
  have hzero : degreeConePrimitive (ℓ:ℝ) (cartesianConjugate P) c 0=c•standardLiouville :=
    funext (degreeConePrimitive_zero (ℓ:ℝ) (cartesianConjugate P) c)
  have hωs (z) (hz : phaseSq z=1) (v w) :
      euclideanExteriorOneForm (degreeConePrimitive (ℓ:ℝ) (cartesianConjugate P) c d) (f z)
        (fderiv ℝ f z v) (fderiv ℝ f z w)=
      euclideanExteriorOneForm (degreeConePrimitive (ℓ:ℝ) (cartesianConjugate P) c 0) z v w := by
    rw [hzero,euclideanExteriorOneForm_smul c
      ((standardLiouville_smooth (ι := Option ι)).contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),standardLiouville_exterior]
    exact hω z (hK z hz) v w
  have hωC (x v w : ι → ℂ) :
      degreeAffineForm (ℓ:ℝ) P c d (fC x) (fderiv ℝ fC x v) (fderiv ℝ fC x w)=
      degreeAffineForm (ℓ:ℝ) P c 0 x v w := by
    rw [degreeAffineForm_pullback hPr (hfC.differentiable (by simp) x),degreeAffineForm_apply]
    exact sphereAffineDescend_degree_curvature hPr hPn hPs hf hfr hfinf c d hωs x v w
  exact ⟨fC,gC,hfC,hgC,hgfC,hfgC,hωC,
    diffeomorphicFormPullback_inverse hfC hgC hfgC (degreeAffineForm (ℓ:ℝ) P c 0)
      (degreeAffineForm (ℓ:ℝ) P c d) hωC⟩

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
section

variable {ι : Type*} [Fintype ι]

theorem fsBallMap_isEmbedding {a : ℝ} (ha : 0<a) :
    Topology.IsEmbedding (fsBallMap (ι := ι) a) :=
  Topology.IsEmbedding.subtypeVal.comp (fsBallHomeomorph (ι := ι) ha).isEmbedding

end

 theorem complexCartesian_standardForm {n : ℕ} (v w : Ambient n) :
    standardForm v w=phaseArea (complexCartesian v) (complexCartesian w) := by
  simp only [standardForm,phaseArea_apply,complexCartesian]
  rfl

 theorem complexRadialTarget_mem {n : ℕ} {c : ℝ} (hc : 0 < c) (x : Ambient n) :
    complexCartesian.symm (fsBallMap c (complexCartesian x)) ∈ openBall n (Real.pi*c) := by
  change Real.pi*(∑ i,Complex.normSq (complexCartesian.symm (fsBallMap c (complexCartesian x)) i))<Real.pi*c
  rw [←complexCartesian_sq,ContinuousLinearEquiv.apply_symm_apply]
  exact mul_lt_mul_of_pos_left (fsBallMap_mem hc _) Real.pi_pos

 theorem exists_degree_polynomial_target_embedding {n : ℕ} {κ : Type} [Fintype κ]
    {P : (Option (Fin n) → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℂ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    {ℓ : ℕ} (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z)
    {c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdℓ : (ℓ:ℝ)*d<1) :
    ∃ g : Ambient n → Ambient n,ContDiff ℝ ∞ g ∧ Topology.IsEmbedding g ∧
      (∀ x,g x∈openBall n (Real.pi*c)) ∧
      ∀ x v w,standardForm (fderiv ℝ g x v) (fderiv ℝ g x w)=
        degreeAffineForm (ℓ:ℝ) P c d x v w := by
  obtain ⟨f,g,hf,hg,hgf,hfg,_hfω,hgω⟩ := exists_degree_global_affine_moser hP hPn hPs hc hd hdℓ
  let e : Ambient n ≃ₜ Ambient n :=
    { toEquiv := ⟨g,f,hfg,hgf⟩
      continuous_toFun := hg.continuous
      continuous_invFun := hf.continuous }
  let h : Ambient n → Ambient n := fun x => complexCartesian.symm (fsBallMap c (complexCartesian (g x)))
  have hh : ContDiff ℝ ∞ h := (complexCartesian (ι := Fin n)).symm.contDiff.comp
    ((fsBallMap_smooth c).comp ((complexCartesian (ι := Fin n)).contDiff.comp hg))
  refine ⟨h,hh,complexCartesian.symm.toHomeomorph.isEmbedding.comp
    ((fsBallMap_isEmbedding hc).comp (complexCartesian.toHomeomorph.isEmbedding.comp e.isEmbedding)),
    fun x => complexRadialTarget_mem hc (g x),?_⟩
  intro x v w
  have hD (u : Ambient n) : fderiv ℝ h x u=complexCartesian.symm
      (fderiv ℝ (fsBallMap c) (complexCartesian (g x)) (complexCartesian (fderiv ℝ g x u))) := by
    exact congrArg (fun L => L u) ((complexCartesian.symm.hasFDerivAt.comp x
      (((fsBallMap_smooth c).differentiable (by simp) _).hasFDerivAt.comp x
        (complexCartesian.hasFDerivAt.comp x (hg.differentiable (by simp) x).hasFDerivAt))).fderiv)
  rw [hD,hD,complexCartesian_standardForm]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [fsBallMap_pullback hc.le,←degreeAffineForm_zero (ℓ:ℝ) P c,hgω]

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_CubicBubbleSeparated
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
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial
open MomentPolytope

 theorem cubicBubblePolynomial_complex_smooth {L S A B m p N : ℕ} (t δ : ℝ) (ε : ℂ) :
     ContDiff ℂ ∞ (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) := by
   exact (cubicBubblePolynomial_joint_smooth (A := A) (B := B) L S m p N t δ).comp
     (f := fun z : Option (Fin 3) → ℂ => (ε,z)) (contDiff_const.prodMk contDiff_id)

 theorem cubic_bubble_target_packing_bp240_oai {A B L S m p N k : ℕ}
     (hL : 0<L) (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (hm : m+1<p) (t δ : ℝ) {r₀ : ℝ} (hr₀ : r₀<(m+1:ℕ)/(L:ℝ))
     (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient)
     (hf : ∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
       (outerAmbientForm (A := A) (B := B) L S (1/((L:ℝ)*Real.pi)) t δ) (f i))
     (hinto : ∀ i,∀ x∈closedBall 3 (r i),(f i x).2≠0)
     (hd : Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r i)) (f j '' closedBall 3 (r j)))) :
     HasPacking 3 (k+1) 1 (Fin.cons r₀ r) := by
   have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
   let D : ℝ → ℝ := fun ε => (1-ε)/L
   have hD : ContDiff ℝ ∞ D := (contDiff_const.sub contDiff_id).div_const _
   have hD0 : D 0=1/L := by simp [D]
   have hnorm : D 0*(1/Real.pi)=1/((L:ℝ)*Real.pi) := by rw [hD0]; ring
   have hcap : Real.pi*(D 0*((m+1:ℕ)*(1/Real.pi)))=(m+1:ℕ)/(L:ℝ) := by
     rw [hD0]
     field_simp
   obtain ⟨ε,hε,g₀,g,hg₀,hg,hd₀,hdg⟩ := exists_cubic_bubble_separated_bp240 hAS hS hB hp hN hm t δ
     (one_div_pos.mpr Real.pi_pos) hD (by rw [hD0]; positivity)
     (by rw [hD0]; field_simp) (by rwa [hcap]) r f (by simpa only [hnorm] using hf) hinto hd
     (show (0:ℝ)<1/2 by norm_num)
   let P := cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε
   have hP : ContDiff ℂ ∞ P := cubicBubblePolynomial_complex_smooth t δ ε
   have hPn : ∀ z,z≠0 → P z≠0 := fun z hz =>
     cubicBubblePolynomial_nonzero L S (m+1) p N t δ (Complex.ofReal_ne_zero.mpr hε.1.ne') hz
   have hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^L•P z :=
     cubicBubblePolynomial_homogeneous hAS hS hB (by omega) p N t δ ε
   obtain ⟨G,hG,hGe,hGin,hGω⟩ := exists_degree_polynomial_target_embedding hP hPn hPs
     (one_div_pos.mpr Real.pi_pos) (show 0≤D ε by dsimp [D]; apply div_nonneg <;> linarith [hε.2])
     (show (L:ℝ)*D ε<1 by dsimp [D]; rw [mul_div_cancel₀ _ hLr.ne']; linarith [hε.1])
   let F : Fin (k+1) → Ambient 3 → Ambient 3 := Fin.cons g₀ g
   have hF : ∀ i : Fin (k+1),FormNeighborhoodEmbedding (closedBall 3 ((Fin.cons r₀ r : Fin (k+1) → ℝ) i))
       (fun _ => successorStandardForm 2) (degreeAffineForm (L:ℝ) P (1/Real.pi) (D ε)) (F i) := by
     intro i
     exact Fin.cases hg₀ hg i
   have hFd : Pairwise (fun i j => Disjoint (F i '' closedBall 3 ((Fin.cons r₀ r : Fin (k+1) → ℝ) i))
       (F j '' closedBall 3 ((Fin.cons r₀ r : Fin (k+1) → ℝ) j))) := by
     intro i
     refine Fin.cases ?_ (fun i => ?_) i
     · intro j
       refine Fin.cases (fun hij => False.elim (hij rfl)) (fun j _ => hd₀ j) j
     · intro j
       refine Fin.cases (fun _ => (hd₀ i).symm) (fun j hij => ?_) j
       exact hdg (fun he => hij (congrArg Fin.succ he))
   obtain ⟨hcomp,hdcomp⟩ := postcompose_form_packing (fun i => closedBall 3 ((Fin.cons r₀ r : Fin (k+1) → ℝ) i))
     (fun _ => successorStandardForm 2) (degreeAffineForm (L:ℝ) P (1/Real.pi) (D ε))
     (fun _ => successorStandardForm 2) isOpen_univ G hG.contMDiff.contMDiffOn
     (hGe.comp Topology.IsEmbedding.subtypeVal) (by
       intro x _hx v w
       rw [mfderiv_eq_fderiv]
       exact (successorStandardForm_apply 2 (fderiv ℝ G x v) (fderiv ℝ G x w)).trans
         (hGω x v w)) F hF (fun _ _ _ => mem_univ _) hFd
   refine ⟨fun i => G ∘ F i,fun i => isBallEmbedding_iff_formNeighborhoodEmbedding.mpr (hcomp i),?_,?_⟩
   · intro i y hy
     obtain ⟨x,_hx,rfl⟩ := hy
     simpa only [mul_one_div_cancel Real.pi_ne_zero,Function.comp_apply] using hGin (F i x)
   · intro i j hij
     exact hdcomp hij

end PackingSufficiencySupport.CubicModel

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.CubicModel.cubic_bubble_target_packing_bp240_oai := @OAI.PackingSufficiencySupport.CubicModel.cubic_bubble_target_packing_bp240_oai
