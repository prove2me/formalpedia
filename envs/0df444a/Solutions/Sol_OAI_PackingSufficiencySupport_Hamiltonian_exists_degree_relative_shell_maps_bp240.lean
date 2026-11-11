-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.exists_degree_relative_shell_maps_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:17.64703+00:00
-- url     : https://prove2.me/submissions/0363ef7f-2808-45d4-840c-ccfb2456ba68

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_circle_relative_radial_moser_bp240

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
-- module Solutions.OAIQ240_BP.BallPacking_Forms_HorizontalCoupling
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_evaluation_const {P F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : P → F →L[ℝ] G} {p : P} (hg : DifferentiableAt ℝ g p) (u : P) (v : F) :
    fderiv ℝ (fun q => g q v) p u = fderiv ℝ g p u v := by
  rw [(hg.hasFDerivAt.clm_apply (hasFDerivAt_const v p)).fderiv]
  simp

theorem pathSpatialExterior_fderivAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) (u : ℝ × E) (v w : E) :
    fderiv ℝ (pathSpatialExterior Γ) p u v w =
      fderiv ℝ (fderiv ℝ Γ) p u (0,v) w - fderiv ℝ (fderiv ℝ Γ) p u (0,w) v := by
  have hD := (hΓ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hΩ := (pathSpatialExterior_smoothAt hΓ).differentiableAt (by simp)
  rw [←fderiv_evaluation_const hΩ u v,
    ←fderiv_evaluation_const (hΩ.clm_apply (differentiableAt_const v)) u w]
  simp only [pathSpatialExterior_apply]
  change fderiv ℝ ((fun q => fderiv ℝ Γ q (0,v) w)-(fun q => fderiv ℝ Γ q (0,w) v)) p u = _
  rw [fderiv_sub (hD.clm_apply (differentiableAt_const (0,v)) |>.clm_apply (differentiableAt_const w))
    (hD.clm_apply (differentiableAt_const (0,w)) |>.clm_apply (differentiableAt_const v))]
  simp only [sub_apply,fderiv_evaluation_const (hD.clm_apply (differentiableAt_const (0,v))),
    fderiv_evaluation_const (hD.clm_apply (differentiableAt_const (0,w))),fderiv_evaluation_const hD]

theorem pathTimePrimitive_fderivAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) (u : ℝ × E) (v : E) :
    fderiv ℝ (pathTimePrimitive Γ) p u v = fderiv ℝ (fderiv ℝ Γ) p u (1,0) v := by
  have hD := (hΓ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [←fderiv_evaluation_const ((pathTimePrimitive_smoothAt hΓ).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  simp only [pathTimePrimitive,fderiv_evaluation_const (hD.clm_apply (differentiableAt_const (1,0))),
    fderiv_evaluation_const hD]

theorem exact_path_time_equationAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) (v w : E) :
    fderiv ℝ (pathSpatialExterior Γ) p (1,0) v w =
      fderiv ℝ (pathTimePrimitive Γ) p (0,v) w -
        fderiv ℝ (pathTimePrimitive Γ) p (0,w) v := by
  have hs := hΓ.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [pathSpatialExterior_fderivAt hΓ,pathTimePrimitive_fderivAt hΓ]
  rw [hs.eq (1,0) (0,v),hs.eq (1,0) (0,w)]

theorem exact_path_closedAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) (u v w : E) :
    fderiv ℝ (pathSpatialExterior Γ) p (0,u) v w -
      fderiv ℝ (pathSpatialExterior Γ) p (0,v) u w +
      fderiv ℝ (pathSpatialExterior Γ) p (0,w) u v = 0 := by
  have hs := hΓ.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [pathSpatialExterior_fderivAt hΓ]
  rw [hs.eq (0,u) (0,v),hs.eq (0,u) (0,w),hs.eq (0,v) (0,w)]
  ring


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

theorem manifoldTimePrimitive_chart {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {c : M} {t : ℝ} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartOneForm (manifoldTimePrimitive Γ t) c y =
      pathTimePrimitive (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) (t,y) := by
  let F : ℝ × E → E →L[ℝ] ℝ := fun q => chartOneForm (Γ q.1) c q.2
  let x := (extChartAt 𝓘(ℝ,E) c).symm y
  have hF : ContDiffAt ℝ ∞ F (t,y) := (hΓ c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds
    (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ t,hy⟩))
  have hdf : HasFDerivAt F (fderiv ℝ F (t,y)) (t,y) :=
    (hF.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hinc : HasDerivAt (fun s : ℝ => (s,y)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have hd : HasDerivAt (fun s => F (s,y)) (pathTimePrimitive F (t,y)) t := by
    have hh := hdf.comp_hasDerivAt t hinc
    simpa only [Function.comp_def,pathTimePrimitive] using hh
  have he : (fun s => (F (s,y)).comp (chartDifferential c x)) = fun s => Γ s x := by
    funext s
    exact chartOneForm_reconstruct_target hy
  have hdn := hd.clm_comp (hasDerivAt_const t (chartDifferential c x))
  rw [he] at hdn
  have hC : (chartDifferential (E := E) c x).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) ((extChartAt 𝓘(ℝ,E) c).map_target hy) using 1
    all_goals try with_reducible_and_instances rfl
  have hdne : deriv (fun s => Γ s x) t = (pathTimePrimitive F (t,y)).comp (chartDifferential c x) := by
    simpa only [ContinuousLinearMap.comp_zero,add_zero] using hdn.deriv
  unfold chartOneForm manifoldTimePrimitive
  change (deriv (fun s => Γ s x) t).comp (chartDifferential c x).inverse = _
  rw [hdne]
  apply ContinuousLinearMap.ext
  intro v
  change pathTimePrimitive F (t,y) ((chartDifferential c x) ((chartDifferential c x).inverse v)) =
    pathTimePrimitive F (t,y) v
  exact congrArg (pathTimePrimitive F (t,y)) (hC.self_apply_inverse v)

theorem pathSpatialExterior_eq_slice {Γ : ℝ × E → E →L[ℝ] ℝ} {p : ℝ × E}
    (hΓ : DifferentiableAt ℝ Γ p) :
    pathSpatialExterior Γ p = euclideanExteriorOneForm (fun y => Γ (p.1,y)) p.2 := by
  have hi : HasFDerivAt (fun y : E => (p.1,y))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hh : HasFDerivAt Γ (fderiv ℝ Γ p) (p.1,p.2) := hΓ.hasFDerivAt
  have hd := (hh.comp p.2 hi).fderiv
  change fderiv ℝ (fun y => Γ (p.1,y)) p.2 = _ at hd
  unfold euclideanExteriorOneForm
  rw [hd]
  rfl

theorem manifoldExteriorOneForm_path_chart {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {c : M} {t : ℝ} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartTwoForm (manifoldExteriorOneForm (Γ t)) c y =
      pathSpatialExterior (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) (t,y) := by
  rw [manifoldExteriorOneForm_chart (fun b z hz => (hΓ.spatial_smooth t b hz).contDiffWithinAt) hy]
  exact (pathSpatialExterior_eq_slice ((hΓ c).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ t,hy⟩))
      |>.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).symm

theorem manifoldExteriorOneForm_path_smooth {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) : SmoothTwoFormFamily (fun t => manifoldExteriorOneForm (Γ t)) := by
  intro c p hp
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hp
  apply ((pathSpatialExterior_smoothAt ((hΓ c).contDiffAt hn)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with q hq
  exact manifoldExteriorOneForm_path_chart hΓ hq.2

theorem manifoldTimePrimitive_smooth {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) : SmoothOneFormFamily (manifoldTimePrimitive Γ) := by
  intro c p hp
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hp
  apply ((pathTimePrimitive_smoothAt ((hΓ c).contDiffAt hn)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with q hq
  exact manifoldTimePrimitive_chart hΓ hq.2


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



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

 theorem hopfPrimitive_circle (c : ℝ) {z : PlanePhase ι} (hz : z≠0) :
    hopfPrimitive c z (phaseJ z)=c/2 := by
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,phaseArea_J_right,phaseSq]
  calc
    c/(2*phaseDot z z)*phaseDot z z=c/2*(phaseDot z z/phaseDot z z) := by ring
    _=c/2 := by rw [div_self (show phaseDot z z≠0 from (phaseSq_pos hz).ne'),mul_one]

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

 theorem hopfForm_complex_diagonal (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v : PlanePhase ι) :
    hopfForm c z v (phaseJ v)=c/(phaseSq z)^2*
      (phaseSq z*phaseSq v-((phaseDot z v)^2+(phaseArea z v)^2)) := by
  rw [hopfForm_apply c hz]
  simp only [phaseArea_J_right,phaseDot_J_right,phaseSq]
  field_simp [show phaseDot z z≠0 from (phaseSq_pos hz).ne']
  ring

 theorem hopfForm_semipositive {c : ℝ} (hc : 0 ≤ c) {z : PlanePhase ι} (hz : z≠0)
    (v : PlanePhase ι) : 0≤hopfForm c z v (phaseJ v) := by
  rw [hopfForm_complex_diagonal c hz]
  exact mul_nonneg (div_nonneg hc (sq_nonneg _)) (sub_nonneg.mpr (phase_complex_cauchy z v))

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem manifoldExteriorOneForm_path_closed {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (t : ℝ) (c : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) (u v w : E) :
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) (t,y) (0,u) v w -
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) (t,y) (0,v) u w +
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) (t,y) (0,w) u v=0 := by
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
    (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ _,hy⟩)
  have he : (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) =ᶠ[𝓝 (t,y)]
      pathSpatialExterior (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) := by
    filter_upwards [hn] with q hq
    exact manifoldExteriorOneForm_path_chart hΓ hq.2
  rw [he.fderiv_eq]
  exact exact_path_closedAt ((hΓ c).contDiffAt hn) u v w

theorem manifoldExteriorOneForm_path_time {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (t : ℝ) (c : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) (v w : E) :
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) (t,y) (1,0) v w =
      fderiv ℝ (fun q : ℝ × E => chartOneForm (manifoldTimePrimitive Γ q.1) c q.2) (t,y) (0,v) w -
      fderiv ℝ (fun q : ℝ × E => chartOneForm (manifoldTimePrimitive Γ q.1) c q.2) (t,y) (0,w) v := by
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
    (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ _,hy⟩)
  have he : (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) =ᶠ[𝓝 (t,y)]
      pathSpatialExterior (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) := by
    filter_upwards [hn] with q hq
    exact manifoldExteriorOneForm_path_chart hΓ hq.2
  have ha : (fun q : ℝ × E => chartOneForm (manifoldTimePrimitive Γ q.1) c q.2) =ᶠ[𝓝 (t,y)]
      pathTimePrimitive (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) := by
    filter_upwards [hn] with q hq
    exact manifoldTimePrimitive_chart hΓ hq.2
  rw [he.fderiv_eq,ha.fderiv_eq]
  exact exact_path_time_equationAt ((hΓ c).contDiffAt hn) v w

theorem SmoothOneFormFamily.time_contDiffAt {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (t : ℝ) (x : M) : ContDiffAt ℝ ∞ (fun s => Γ s x) t := by
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) x).source := mem_extChartAt_source x
  have hxt := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hcam := ((hΓ x).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x)).mem_nhds
      (show (t,extChartAt 𝓘(ℝ,E) x x) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) x).target from ⟨mem_univ t,hxt⟩))).comp t (contDiffAt_id.prodMk contDiffAt_const)
  have hsm := hcam.clm_comp (contDiffAt_const (c := chartDifferential x x))
  apply hsm.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => by
    simpa only [(extChartAt 𝓘(ℝ,E) x).left_inv hx,Function.comp_def,id_eq] using (chartOneForm_reconstruct_target
      (α := Γ s) hxt).symm)

theorem manifoldTimePrimitive_eval_constant {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {x : M} {Z : E}
    (hz : ∀ t, Γ t x Z=Γ 0 x Z) (t : ℝ) : manifoldTimePrimitive Γ t x Z=0 := by
  have hd := (((hΓ.time_contDiffAt t x).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt).clm_apply
    (hasDerivAt_const t Z)
  have he : (fun s => Γ s x Z) = fun _ : ℝ => Γ 0 x Z := funext hz
  change HasDerivAt (fun s => Γ s x Z) _ t at hd
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_const t (Γ 0 x Z))
  simpa only [manifoldTimePrimitive,ContinuousLinearMap.map_zero,add_zero] using hh

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_skew (α : ManifoldOneForm E M) (x : M) (v w : E) :
    manifoldExteriorOneForm α x v w = -manifoldExteriorOneForm α x w v := by
  change fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x v) (chartDifferential x x w) -
    fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x w) (chartDifferential x x v) = -_
  change _ = -(fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x w) (chartDifferential x x v) -
    fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x v) (chartDifferential x x w))
  ring

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

 theorem radialSymplectization_nondegenerate {z : PlanePhase ι} (hz : z≠0)
    (α : PlanePhase ι →L[ℝ] ℝ) (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (hαJ : α (phaseJ z)=c)
    (hCr : ∀ v,C v z=0) (hCJr : ∀ v,C v (phaseJ z)=0)
    (hCJl : ∀ v,C (phaseJ z) v=0)
    (hpos : ∀ v,phaseDot z v=0 → phaseArea z v=0 → v≠0 → 0<C v (phaseJ v)) :
    (radialSymplectization z α C).IsInvertible := by
  let Ω := radialSymplectization z α C
  have hq := phaseSq_pos hz
  have hinj : Injective Ω := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    change Ω v=0 at hv
    have hval (w : PlanePhase ι) : Ω v w=0 := by rw [hv]; rfl
    have hdz : phaseDot z v=0 := by
      have h := hval (phaseJ z)
      change radialSymplectization z α C v (phaseJ z)=0 at h
      rw [radialSymplectization_apply,hαJ,hCJr,phaseDot_J_right,phaseArea_self] at h
      nlinarith
    have hαv : α v=0 := by
      have h := hval z
      change radialSymplectization z α C v z=0 at h
      rw [radialSymplectization_apply,hdz,hCr] at h
      change 2*(0*α z-α v*phaseSq z)+phaseSq z*0=0 at h
      nlinarith
    let b := phaseArea z v/phaseSq z
    let w := v-b•phaseJ z
    have hwd : phaseDot z w=0 := by
      simp only [w,map_sub,map_smul,phaseDot_J_right,phaseArea_self,neg_zero,smul_eq_mul,
        mul_zero,sub_zero,hdz]
    have hwa : phaseArea z w=0 := by
      simp only [w,map_sub,map_smul,smul_eq_mul,phaseArea_J_right]
      change phaseArea z v-(phaseArea z v/phaseSq z)*phaseSq z=0
      field_simp [hq.ne']
      ring
    have hCw : C w (phaseJ w)=0 := by
      have h := hval (phaseJ w)
      change radialSymplectization z α C v (phaseJ w)=0 at h
      rw [radialSymplectization_apply,hdz,hαv] at h
      have he : C w (phaseJ w)=C v (phaseJ w) := by
        simp only [w,map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul,hCJl,mul_zero,sub_zero]
      rw [he]
      nlinarith
    have hw : w=0 := by
      by_contra hn
      have hh := hpos w hwd hwa hn
      linarith
    have hvw : v=b•phaseJ z := sub_eq_zero.mp hw
    have hb : b=0 := by
      rw [hvw,map_smul,hαJ,smul_eq_mul] at hαv
      exact (mul_eq_zero.mp hαv).resolve_right hc.ne'
    rw [hvw,hb,zero_smul]
  have hsurj : Surjective Ω :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_continuous_dual (E := PlanePhase ι)).symm).mp hinj
  exact ⟨(LinearEquiv.ofBijective Ω.toLinearMap ⟨hinj,hsurj⟩).toContinuousLinearEquiv,rfl⟩

 theorem radialSymplectization_circle (z : PlanePhase ι) (α : PlanePhase ι →L[ℝ] ℝ)
    (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ) {c : ℝ}
    (hα : α (phaseJ z)=c) (hC : ∀ v,C v (phaseJ z)=0) (v : PlanePhase ι) :
    radialSymplectization z α C v (phaseJ z)=2*c*phaseDot z v := by
  rw [radialSymplectization_apply,hα,hC,phaseDot_J_right,phaseArea_self]
  ring

end

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

 theorem degreeHopfPrimitive_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    {q : ℝ} (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z)) (c d : ℝ) :
    degreeHopfPrimitive q F c d z (phaseJ z)=c/2 := by
  simp only [degreeHopfPrimitive,Pi.add_apply,Pi.smul_apply,add_apply,smul_apply,
    smul_eq_mul,primitivePullback,ContinuousLinearMap.comp_apply,hD,map_smul,
    hopfPrimitive_circle c hz,hopfPrimitive_circle c hFz]
  ring

 theorem degreeHopfForm_radial {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    {q : ℝ} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z z=q•F z) (c d : ℝ) (v : PlanePhase ι) :
    degreeHopfForm q F c d z z v=0 := by
  rw [degreeHopfForm_eq hF hz hFz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hD,
    map_smul,hopfForm_radial c hz,hopfForm_radial c hFz,mul_zero,add_zero]

 theorem degreeHopfForm_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    {q : ℝ} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z)) (c d : ℝ) (v : PlanePhase ι) :
    degreeHopfForm q F c d z (phaseJ z) v=0 := by
  rw [degreeHopfForm_eq hF hz hFz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hD,
    map_smul,hopfForm_circle c hz,hopfForm_circle c hFz,mul_zero,add_zero]

 theorem degreeHopfForm_skew (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    (z v w : PlanePhase ι) : degreeHopfForm q F c d z v w= -degreeHopfForm q F c d z w v := by
  simp only [degreeHopfForm,euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply]
  ring

 theorem degreeHopfForm_horizontal_positive {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hJ : ∀ v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {q c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdq : q*d<1)
    {v : PlanePhase ι} (hdv : phaseDot z v=0) (hav : phaseArea z v=0) (hv : v≠0) :
    0 < degreeHopfForm q F c d z v (phaseJ v) := by
  rw [degreeHopfForm_eq hF hz hFz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hJ]
  have hp : 0<hopfForm c z v (phaseJ v) := by
    rw [hopfForm_complex_diagonal c hz,hdv,hav]
    simp only [zero_pow (by norm_num : 2≠0),zero_add,sub_zero]
    exact mul_pos (div_pos hc (sq_pos_of_pos (phaseSq_pos hz)))
      (mul_pos (phaseSq_pos hz) (phaseSq_pos hv))
  exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hp)
    (mul_nonneg hd (hopfForm_semipositive hc.le hFz _))

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

 theorem degreeConePrimitive_smoothAt {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (q c d : ℝ) :
    ContDiffAt ℝ ∞ (degreeConePrimitive q F c d) z :=
  phaseSq_smooth.contDiffAt.smul (degreeHopfPrimitive_smoothAt hF hz hFz q c d)

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_CompactUniformCentral
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
open scoped Manifold Topology
open Manifold
section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 theorem degreeConePrimitive_split (q : ℝ) (F : PlanePhase ι → PlanePhase κ)
    (c d : ℝ) (z : PlanePhase ι) :
    degreeConePrimitive q F c d z=degreeConePrimitive q F c 0 z+
      d•(phaseSq z•degreeHopfDifference q F c z) := by
  ext v
  simp only [degreeConePrimitive,degreeHopfPrimitive,degreeHopfDifference,
    Pi.add_apply,Pi.smul_apply,Pi.sub_apply,add_apply,smul_apply,sub_apply,smul_eq_mul]
  ring

 theorem degreeHopfDifference_smoothAt {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (q c : ℝ) :
    ContDiffAt ℝ ∞ (degreeHopfDifference q F c) z :=
  (primitivePullback_smoothAt (hopfPrimitive_smoothAt c hFz) hF).sub
    ((hopfPrimitive_smoothAt c hz).const_smul q)

 theorem degreeHopfDifference_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    {q : ℝ} (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z)) (c : ℝ) :
    degreeHopfDifference q F c z (phaseJ z)=0 := by
  simp only [degreeHopfDifference,Pi.sub_apply,Pi.smul_apply,sub_apply,smul_apply,
    smul_eq_mul,primitivePullback,ContinuousLinearMap.comp_apply,hD,map_smul,
    hopfPrimitive_circle c hz,hopfPrimitive_circle c hFz]
  ring

 theorem radialDegreeConePrimitive_exterior {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} {d : ℝ → ℝ} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hd : DifferentiableAt ℝ d (phaseSq z)) (q c : ℝ) :
    euclideanExteriorOneForm (radialDegreeConePrimitive q F c d) z=
      radialSymplectization z
        (degreeHopfPrimitive q F c (d (phaseSq z)) z+
          (phaseSq z*deriv d (phaseSq z))•degreeHopfDifference q F c z)
        (degreeHopfForm q F c (d (phaseSq z)) z) := by
  let ξ : PlanePhase ι → PlanePhase ι →L[ℝ] ℝ := fun y => phaseSq y•degreeHopfDifference q F c y
  have hξ : DifferentiableAt ℝ ξ z :=
    (phaseSq_smooth.contDiffAt.smul (degreeHopfDifference_smoothAt hF hz hFz q c)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h₀ := (degreeConePrimitive_smoothAt hF hz hFz q c 0).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hds := hd.hasDerivAt.comp_hasFDerivAt z (phaseSq_hasFDerivAt z)
  have hr := h₀.hasFDerivAt.add (hds.smul hξ.hasFDerivAt)
  have hs := h₀.hasFDerivAt.add (hξ.hasFDerivAt.const_smul (d (phaseSq z)))
  have her : (fun y => degreeConePrimitive q F c 0 y+d (phaseSq y)•ξ y)=
      radialDegreeConePrimitive q F c d :=
    funext fun y => (degreeConePrimitive_split q F c (d (phaseSq y)) y).symm
  have hes : (fun y => degreeConePrimitive q F c 0 y+d (phaseSq z)•ξ y)=
      degreeConePrimitive q F c (d (phaseSq z)) :=
    funext fun y => (degreeConePrimitive_split q F c (d (phaseSq z)) y).symm
  change HasFDerivAt (fun y => degreeConePrimitive q F c 0 y+d (phaseSq y)•ξ y) _ z at hr
  change HasFDerivAt (fun y => degreeConePrimitive q F c 0 y+d (phaseSq z)•ξ y) _ z at hs
  rw [her] at hr
  rw [hes] at hs
  have he := degreeConePrimitive_exterior hF hz hFz q c (d (phaseSq z))
  ext v w
  have hh := congrArg (fun L : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ => L v w) he
  rw [euclideanExteriorOneForm,hs.fderiv] at hh
  rw [euclideanExteriorOneForm,hr.fderiv]
  simp only [sub_apply,ContinuousLinearMap.flip_apply,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,radialSymplectization_apply,
    Function.comp_apply,ξ] at hh ⊢
  nlinarith only [hh]

 theorem radialDegreeConePrimitive_nondegenerate {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} {d : ℝ → ℝ} {q : ℝ}
    (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z z=q•F z)
    (hJ : ∀ v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    (hd : DifferentiableAt ℝ d (phaseSq z)) {c : ℝ} (hc : 0 < c)
    (hd0 : 0≤d (phaseSq z)) (hdq : q*d (phaseSq z)<1) :
    (euclideanExteriorOneForm (radialDegreeConePrimitive q F c d) z).IsInvertible := by
  have hDJ : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z) := by rw [hJ,hD,map_smul]
  rw [radialDegreeConePrimitive_exterior hF hz hFz hd]
  apply radialSymplectization_nondegenerate hz _ _ (half_pos hc)
  · simp only [add_apply,smul_apply,smul_eq_mul,degreeHopfPrimitive_circle hz hFz hDJ,
      degreeHopfDifference_circle hz hFz hDJ,mul_zero,add_zero]
  · intro v
    rw [degreeHopfForm_skew,degreeHopfForm_radial hF hz hFz hD,neg_zero]
  · intro v
    rw [degreeHopfForm_skew,degreeHopfForm_circle hF hz hFz hDJ,neg_zero]
  · exact degreeHopfForm_circle hF hz hFz hDJ c _
  · intro v hdv hav hv
    exact degreeHopfForm_horizontal_positive hF hz hFz hJ hc hd0 hdq hdv hav hv

 theorem radialDegreeConePrimitive_circle_contraction {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} {d : ℝ → ℝ} {q : ℝ}
    (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hDJ : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z))
    (hd : DifferentiableAt ℝ d (phaseSq z)) (c : ℝ) (v : PlanePhase ι) :
    euclideanExteriorOneForm (radialDegreeConePrimitive q F c d) z v (phaseJ z)=c*phaseDot z v := by
  rw [radialDegreeConePrimitive_exterior hF hz hFz hd]
  have hα : (degreeHopfPrimitive q F c (d (phaseSq z)) z+
      (phaseSq z*deriv d (phaseSq z))•degreeHopfDifference q F c z) (phaseJ z)=c/2 := by
    simp only [add_apply,smul_apply,smul_eq_mul,degreeHopfPrimitive_circle hz hFz hDJ,
      degreeHopfDifference_circle hz hFz hDJ,mul_zero,add_zero]
  rw [radialSymplectization_circle z _ _ hα
    (fun v => by rw [degreeHopfForm_skew,degreeHopfForm_circle hF hz hFz hDJ,neg_zero])]
  ring

end

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

 theorem cutoffDegreePrimitive_eq (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    (χ : ℝ → ℝ) (t : ℝ) : cutoffDegreePrimitive q F c d χ t=
      radialDegreeConePrimitive q F c (fun a => t*d*χ a) := by
  funext z
  rw [cutoffDegreePrimitive,radialDegreeConePrimitive,degreeConePrimitive_split,degreeConePrimitive_zero]

 theorem cutoffDegreePrimitive_smooth {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0) (q c d : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => cutoffDegreePrimitive q F c d χ p.1 p.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hz : p.2=0
  · have hn : (fun p : ℝ × PlanePhase ι => χ (phaseSq p.2))=ᶠ[𝓝 p] 0 := by
      have hct : Filter.Tendsto (fun p : ℝ × PlanePhase ι => phaseSq p.2) (𝓝 p) (𝓝 (0:ℝ)) := by
        have hh := ((phaseSq_smooth (ι := ι)).continuous.comp
          (continuous_snd : Continuous (Prod.snd : ℝ × PlanePhase ι → PlanePhase ι))).continuousAt (x := p)
        change Filter.Tendsto (fun p : ℝ × PlanePhase ι => phaseSq p.2) (𝓝 p) (𝓝 (phaseSq p.2)) at hh
        rw [hz,cutoff_phaseSq_zero] at hh
        exact hh
      exact hχ0.comp_tendsto hct
    apply ((((standardLiouville_smooth (ι := ι)).const_smul c).comp contDiff_snd).contDiffAt).congr_of_eventuallyEq
    filter_upwards [hn] with p hp
    simp only [cutoffDegreePrimitive,hp,Pi.zero_apply,mul_zero,zero_smul,add_zero,Function.comp_apply]
  · exact (((standardLiouville_smooth (ι := ι)).const_smul c).comp contDiff_snd).contDiffAt.add
      (((contDiffAt_fst.mul contDiffAt_const).mul
        (hχ.contDiffAt.comp p (phaseSq_smooth.contDiffAt.comp p contDiffAt_snd))).smul
        ((phaseSq_smooth.contDiffAt.comp p contDiffAt_snd).smul
          ((degreeHopfDifference_smoothAt hF.contDiffAt hz (hF0 _ hz) q c).comp p contDiffAt_snd)))

 theorem cutoffDegreePrimitive_nhds_zero (q : ℝ) (F : PlanePhase ι → PlanePhase κ)
    (c d t : ℝ) {χ : ℝ → ℝ} (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0) :
    cutoffDegreePrimitive q F c d χ t=ᶠ[𝓝 (0:PlanePhase ι)] (fun z => c•standardLiouville z) := by
  have hct : Filter.Tendsto (phaseSq (ι := ι)) (𝓝 (0:PlanePhase ι)) (𝓝 (0:ℝ)) := by
    simpa only [ContinuousAt, cutoff_phaseSq_zero] using (phaseSq_smooth (ι := ι)).continuous.continuousAt (x := 0)
  have hn := hχ0.comp_tendsto hct
  filter_upwards [hn] with z hz
  change χ (phaseSq z)=0 at hz
  simp only [cutoffDegreePrimitive,hz,mul_zero,zero_smul,add_zero]

 theorem cutoffDegreePrimitive_slice_smooth {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0) (q c d t : ℝ) :
    ContDiff ℝ ∞ (cutoffDegreePrimitive q F c d χ t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z=0
  · subst z
    exact ((standardLiouville_smooth (ι := ι)).contDiffAt.const_smul c).congr_of_eventuallyEq
      (cutoffDegreePrimitive_nhds_zero q F c d t hχ0)
  · exact ((standardLiouville_smooth (ι := ι)).contDiffAt.const_smul c).add
      ((hχ.contDiffAt.comp z phaseSq_smooth.contDiffAt).const_smul (t*d) |>.smul
        (phaseSq_smooth.contDiffAt.smul (degreeHopfDifference_smoothAt hF.contDiffAt hz (hF0 _ hz) q c)))

 theorem cutoffDegreePrimitive_nondegenerate {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hD : ∀ z,fderiv ℝ F z z=q•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0)
    (hχr : ∀ a,χ a∈Icc (0:ℝ) 1) {c d : ℝ} (hc : 0 < c) (hd : 0≤d)
    (hq : 0≤q) (hdq : q*d<1) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (z : PlanePhase ι) :
    (euclideanExteriorOneForm (cutoffDegreePrimitive q F c d χ t) z).IsInvertible := by
  classical
  by_cases hz : z=0
  · subst z
    have he := (cutoffDegreePrimitive_nhds_zero q F c d t hχ0).fderiv_eq (𝕜 := ℝ)
    have he' : euclideanExteriorOneForm (cutoffDegreePrimitive q F c d χ t) 0=c•(phaseArea (ι := ι)) := by
      rw [euclideanExteriorOneForm,he]
      change euclideanExteriorOneForm (c•(standardLiouville (ι := ι))) 0=_
      rw [euclideanExteriorOneForm_smul c ((standardLiouville_smooth (ι := ι)).contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
        standardLiouville_exterior]
    rw [he']
    exact bilinear_isInvertible_of_taming (J := phaseJ) (fun v hv => by
      simpa only [smul_apply,smul_eq_mul,phaseArea_J_right,phaseSq] using
        mul_pos hc (phaseSq_pos hv))
  · rw [cutoffDegreePrimitive_eq]
    apply radialDegreeConePrimitive_nondegenerate hF.contDiffAt hz (hF0 z hz) (hD z) (hJ z)
      ((hχ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _).const_mul (t*d)) hc
      (mul_nonneg (mul_nonneg ht.1 hd) (hχr _).1)
    calc
      q*(t*d*χ (phaseSq z))≤q*d := by
        nlinarith only [ht.1,ht.2,hd,hq,(hχr (phaseSq z)).1,(hχr (phaseSq z)).2,
          mul_nonneg hq hd,mul_nonneg (mul_nonneg hq hd) ht.1,
          mul_le_mul_of_nonneg_left (hχr (phaseSq z)).2 (mul_nonneg (mul_nonneg hq ht.1) hd)]
      _<1 := hdq

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_CircleAction_CircleRelativeRadialMoser
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped BigOperators
section

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem cutoffDegreePrimitive_smooth_family {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0) (q c d : ℝ) :
    SmoothOneFormFamily (cutoffDegreePrimitive q F c d χ) := by
  intro b
  simpa only [vector_chartOneForm] using
    (cutoffDegreePrimitive_smooth hF hF0 hχ hχ0 q c d).contDiffOn

 theorem cutoffDegreePrimitive_moser_data {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hD : ∀ z,fderiv ℝ F z z=q•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0)
    (hχr : ∀ a,χ a∈Icc (0:ℝ) 1) {c d : ℝ} (hc : 0 < c) (hd : 0≤d)
    (hq : 0≤q) (hdq : q*d<1) :
    ManifoldMoserData (fun t => manifoldExteriorOneForm (cutoffDegreePrimitive q F c d χ t))
      (manifoldTimePrimitive (cutoffDegreePrimitive q F c d χ)) := by
  have hΓ := cutoffDegreePrimitive_smooth_family hF hF0 hχ hχ0 q c d
  refine ⟨manifoldExteriorOneForm_path_smooth hΓ,manifoldTimePrimitive_smooth hΓ,?_,?_,?_,?_⟩
  · intro t ht z
    rw [vector_exteriorOneForm]
    exact cutoffDegreePrimitive_nondegenerate hF hF0 hD hJ hχ hχ0 hχr hc hd hq hdq ht z
  · intro t _ b y _ u v
    simp only [vector_chartTwoForm]
    exact manifoldExteriorOneForm_skew _ _ _ _
  · intro t _ b y hy u v w
    exact manifoldExteriorOneForm_path_closed hΓ t b y hy u v w
  · intro t _ b y hy u v
    exact manifoldExteriorOneForm_path_time hΓ t b y hy u v

 theorem cutoffDegreePrimitive_circle_contraction {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hDJ : ∀ z,fderiv ℝ F z (phaseJ z)=q•phaseJ (F z))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (c d t : ℝ) (z v : PlanePhase ι) :
    manifoldExteriorOneForm (cutoffDegreePrimitive q F c d χ t) z v (phaseJ z)=c*phaseDot z v := by
  rw [vector_exteriorOneForm]
  by_cases hz : z=0
  · subst z
    simp only [map_zero,zero_apply,mul_zero]
  · rw [cutoffDegreePrimitive_eq]
    exact radialDegreeConePrimitive_circle_contraction hF.contDiffAt hz (hF0 _ hz) (hDJ z)
      ((hχ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _).const_mul (t*d)) c v

 theorem cutoffDegreePrimitive_time_circle {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hDJ : ∀ z,fderiv ℝ F z (phaseJ z)=q•phaseJ (F z))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0)
    (c d t : ℝ) (z : PlanePhase ι) :
    manifoldTimePrimitive (cutoffDegreePrimitive q F c d χ) t z (phaseJ z)=0 := by
  apply manifoldTimePrimitive_eval_constant (cutoffDegreePrimitive_smooth_family hF hF0 hχ hχ0 q c d)
  intro s
  by_cases hz : z=0
  · subst z
    simp only [map_zero]
  · simp only [cutoffDegreePrimitive,add_apply,smul_apply,smul_eq_mul,
      degreeHopfDifference_circle hz (hF0 _ hz) (hDJ z),mul_zero,add_zero]

end
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem phaseShell_isCompact (a b : ℝ) : IsCompact (phaseShell (ι := ι) a b) := by
  apply (isCompact_closedBall (0:PlanePhase ι) (max b 0+1)).of_isClosed_subset
    (isClosed_Icc.preimage phaseSq_smooth.continuous)
  intro z hz
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ max b 0+1)).mpr
  intro i
  have hi : (z i).1*(z i).1+(z i).2*(z i).2≤phaseSq z := by
    simpa only [phaseSq,phaseDot_apply] using Finset.single_le_sum (f := fun j => (z j).1*(z j).1+(z j).2*(z j).2)
      (fun j _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (Finset.mem_univ i)
  have hb := hz.2
  change phaseSq z≤b at hb
  rw [Prod.norm_def,max_le_iff]
  constructor
  · rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (z i).2,sq_nonneg (|(z i).1|-1),sq_abs (z i).1,le_max_left b 0,le_max_right b 0]
  · rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (z i).1,sq_nonneg (|(z i).2|-1),sq_abs (z i).2,le_max_left b 0,le_max_right b 0]

theorem phaseShell_radial (a b : ℝ) {x : PlanePhase ι} (hx : x∈phaseShell a b)
    {y : PlanePhase ι} (h : phaseSq y=phaseSq x) : y∈phaseShell a b := by
  change phaseSq y∈Icc a b
  rw [h]
  exact hx

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linear_equivariant_fderiv {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (U : PlanePhase ι →L[ℝ] PlanePhase ι)
    (T : PlanePhase κ →L[ℝ] PlanePhase κ) (hFT : ∀ z,F (U z)=T (F z))
    (z v : PlanePhase ι) : fderiv ℝ F (U z) (U v)=T (fderiv ℝ F z v) := by
  have he : (fun z => F (U z))=(fun z => T (F z)) := funext hFT
  have h₁ := ((hF.differentiable (by simp) (U z)).hasFDerivAt).comp z U.hasFDerivAt
  have h₂ := T.hasFDerivAt.comp z ((hF.differentiable (by simp) z).hasFDerivAt)
  change HasFDerivAt (fun z => F (U z)) _ z at h₁
  rw [he] at h₁
  exact congrArg (fun L => L v) (h₁.unique h₂)

theorem hopfPrimitive_linear_invariant (U : PlanePhase ι →L[ℝ] PlanePhase ι)
    (hD : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
    (hA : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
    (c : ℝ) (z v : PlanePhase ι) : hopfPrimitive c (U z) (U v)=hopfPrimitive c z v := by
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,phaseSq,hD,hA]

theorem exterior_linear_invariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : E → E →L[ℝ] ℝ} (U : E →L[ℝ] E) {z : E}
    (hα : ContDiffAt ℝ ∞ α (U z)) (he : ∀ x v,α (U x) (U v)=α x v) (v w : E) :
    euclideanExteriorOneForm α (U z) (U v) (U w)=euclideanExteriorOneForm α z v w := by
  have he' : primitivePullback α U=α := by
    funext x
    ext v
    simpa only [primitivePullback,ContinuousLinearMap.comp_apply,U.fderiv] using he x v
  have hh := primitivePullback_exteriorAt hα U.contDiff.contDiffAt
  rw [he',U.fderiv] at hh
  exact (congrArg (fun B => B v w) hh).symm

end

variable {ι : Type} [Fintype ι]

 theorem phaseRotate_hasDerivAt (s : ℝ) (z : PlanePhase ι) :
    HasDerivAt (fun t => phaseRotate t z) (phaseJ (phaseRotate s z)) s := by
  have hh := ((Real.hasDerivAt_cos s).smul_const z).add
    ((Real.hasDerivAt_sin s).smul_const (phaseJ z))
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [phaseRotate_apply,map_add,map_smul,phaseJ_sq,smul_neg,neg_smul]
  abel

 theorem phaseCircleAction_generator (z : PlanePhase ι) :
    phaseCircleAction.generator z=(2*Real.pi)•phaseJ z := by
  have hg : HasDerivAt (fun t : ℝ => 2*Real.pi*t) (2*Real.pi) 0 := by
    simpa only [mul_one,Function.id_def] using (hasDerivAt_id (0:ℝ)).const_mul (2*Real.pi)
  have hh := (phaseRotate_hasDerivAt (ι := ι) (2*Real.pi*0) z).scomp 0 hg
  have he : HasDerivAt (fun t : ℝ => phaseRotate (2*Real.pi*t) z)
      ((2*Real.pi)•phaseJ z) 0 := by
    convert! hh using 1; simp
  change manifoldMapDifferential (E := PlanePhase ι) (F := ℝ) (fun t : ℝ => phaseRotate (2*Real.pi*t) z) 0 1=_
  simp only [manifoldMapDifferential,mfderiv_eq_fderiv,he.hasFDerivAt.fderiv,
    ContinuousLinearMap.toSpanSingleton_apply,one_smul]

 theorem phaseSq_rotate (s : ℝ) (z : PlanePhase ι) : phaseSq (phaseRotate s z)=phaseSq z := by
  simp only [phaseRotate_apply,phaseSq,map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,phaseDot_J_left,phaseDot_J_right,phaseArea_J_left,neg_neg,phaseArea_self,neg_zero,mul_zero,
    add_zero,zero_add]
  linear_combination (phaseDot z z) * Real.sin_sq_add_cos_sq s

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_CircleAction_DegreeCircleCovariance
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some
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

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem phaseDot_rotate (s : ℝ) (z v : PlanePhase ι) :
    phaseDot (phaseRotate s z) (phaseRotate s v)=phaseDot z v := by
  simp only [phaseRotate_apply,map_add,map_smul,add_apply,smul_apply,smul_eq_mul,
    phaseDot_J_left,phaseDot_J_right,phaseArea_J_left]
  linear_combination (phaseDot z v)*Real.sin_sq_add_cos_sq s

 theorem phaseArea_rotate (s : ℝ) (z v : PlanePhase ι) :
    phaseArea (phaseRotate s z) (phaseRotate s v)=phaseArea z v := by
  simp only [phaseRotate_apply,map_add,map_smul,add_apply,smul_apply,smul_eq_mul,
    phaseArea_J_left,phaseArea_J_right,phaseDot_J_left]
  linear_combination (phaseArea z v)*Real.sin_sq_add_cos_sq s

 theorem phaseCircleAction_differential (s : ℝ) (z : PlanePhase ι) :
    phaseCircleAction.differential s z=phaseRotate (2*Real.pi*s) := by
  change mfderiv 𝓘(ℝ,PlanePhase ι) 𝓘(ℝ,PlanePhase ι)
    (phaseRotate (2*Real.pi*s)) z=_
  rw [mfderiv_eq_fderiv,(phaseRotate (2*Real.pi*s)).fderiv]

 theorem degreeHopfDifference_rotate {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) {q : ℝ}
    (hrot : ∀ s z,F (phaseRotate s z)=phaseRotate (q*s) (F z)) (c s : ℝ)
    (z v : PlanePhase ι) :
    degreeHopfDifference q F c (phaseRotate s z) (phaseRotate s v)=degreeHopfDifference q F c z v := by
  simp only [degreeHopfDifference,Pi.sub_apply,Pi.smul_apply,sub_apply,smul_apply,
    primitivePullback,ContinuousLinearMap.comp_apply,
    linear_equivariant_fderiv hF (phaseRotate s) (phaseRotate (q*s)) (hrot s),hrot,
    hopfPrimitive_linear_invariant _ (phaseDot_rotate _) (phaseArea_rotate _)]

 theorem cutoffDegreePrimitive_rotate {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) {q : ℝ}
    (hrot : ∀ s z,F (phaseRotate s z)=phaseRotate (q*s) (F z))
    (c d : ℝ) (χ : ℝ → ℝ) (t s : ℝ) (z v : PlanePhase ι) :
    cutoffDegreePrimitive q F c d χ t (phaseRotate s z) (phaseRotate s v)=
      cutoffDegreePrimitive q F c d χ t z v := by
  simp only [cutoffDegreePrimitive,add_apply,smul_apply,phaseSq_rotate,
    degreeHopfDifference_rotate hF hrot,standardLiouville,phaseArea_rotate]

 theorem cutoffDegreeForm_circle_invariant {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hrot : ∀ s z,F (phaseRotate s z)=phaseRotate (q*s) (F z))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0)
    (c d s t : ℝ) (z : PlanePhase ι) :
    (manifoldExteriorOneForm (cutoffDegreePrimitive q F c d χ t) (phaseCircleAction.slice s z)).bilinearComp
      (phaseCircleAction.differential s z) (phaseCircleAction.differential s z)=
      manifoldExteriorOneForm (cutoffDegreePrimitive q F c d χ t) z := by
  have hΓ : ContDiff ℝ ∞ (cutoffDegreePrimitive q F c d χ t) :=
    cutoffDegreePrimitive_slice_smooth hF hF0 hχ hχ0 q c d t
  rw [phaseCircleAction_differential]
  ext v w
  simp only [ContinuousLinearMap.bilinearComp_apply,vector_exteriorOneForm]
  exact exterior_linear_invariant (phaseRotate (2*Real.pi*s)) hΓ.contDiffAt
    (cutoffDegreePrimitive_rotate hF hrot c d χ t (2*Real.pi*s)) v w

end

section

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

 theorem cutoffDegreePrimitive_linear_pullback {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (e : PlanePhase ν →L[ℝ] PlanePhase ι)
    (heD : ∀ z v,phaseDot (e z) (e v)=phaseDot z v)
    (heA : ∀ z v,phaseArea (e z) (e v)=phaseArea z v)
    (q c d t : ℝ) (χ : ℝ → ℝ) :
    primitivePullback (cutoffDegreePrimitive q F c d χ t) e=
      cutoffDegreePrimitive q (F ∘ e) c d χ t := by
  funext z
  ext v
  simp only [cutoffDegreePrimitive,primitivePullback,ContinuousLinearMap.comp_apply,e.fderiv,
    add_apply,smul_apply,smul_eq_mul,degreeHopfDifference,Pi.sub_apply,Pi.smul_apply,sub_apply,
    standardLiouville,hopfPrimitive,phaseSq,heD,heA,
    fderiv_comp z (hF.differentiable (by simp) (e z)) (e.differentiableAt),Function.comp_apply]

 theorem cutoffDegreeForm_subspace_nondegenerate {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hD : ∀ z,fderiv ℝ F z z=q•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    (e : PlanePhase ν →L[ℝ] PlanePhase ι)
    (heD : ∀ z v,phaseDot (e z) (e v)=phaseDot z v)
    (heA : ∀ z v,phaseArea (e z) (e v)=phaseArea z v)
    (heJ : ∀ z,e (phaseJ z)=phaseJ (e z))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0)
    (hχr : ∀ a,χ a∈Icc (0:ℝ) 1) {c d : ℝ} (hc : 0 < c) (hd : 0≤d)
    (hq : 0≤q) (hdq : q*d<1) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (z : PlanePhase ν) :
    ((manifoldExteriorOneForm (cutoffDegreePrimitive q F c d χ t) (e z)).bilinearComp e e).IsInvertible := by
  have hn (z : PlanePhase ν) (hz : z≠0) : e z≠0 := by
    intro he
    have hh := heD z z
    rw [he,map_zero] at hh
    exact (phaseSq_pos hz).ne' hh.symm
  have hcomp : ContDiff ℝ ∞ (F ∘ e) := hF.comp e.contDiff
  have hcompD (z : PlanePhase ν) : fderiv ℝ (F ∘ e) z z=q•(F ∘ e) z := by
    rw [fderiv_comp z (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (e z)) e.differentiableAt,e.fderiv,
      ContinuousLinearMap.comp_apply,hD,Function.comp_apply]
  have hcompJ (z v : PlanePhase ν) :
      fderiv ℝ (F ∘ e) z (phaseJ v)=phaseJ (fderiv ℝ (F ∘ e) z v) := by
    rw [fderiv_comp z (hF.differentiable (by simp) (e z)) e.differentiableAt,e.fderiv]
    simp only [ContinuousLinearMap.comp_apply,heJ,hJ]
  have hh := cutoffDegreePrimitive_nondegenerate hcomp (fun z hz => hF0 _ (hn z hz))
    hcompD hcompJ hχ hχ0 hχr hc hd hq hdq ht z
  have hΓ : ContDiff ℝ ∞ (cutoffDegreePrimitive q F c d χ t) :=
    cutoffDegreePrimitive_slice_smooth hF hF0 hχ hχ0 q c d t
  have hext := primitivePullback_exteriorAt hΓ.contDiffAt e.contDiff.contDiffAt (x := z)
  rw [cutoffDegreePrimitive_linear_pullback hF e heD heA,e.fderiv] at hext
  rw [vector_exteriorOneForm,←hext]
  exact hh

end

section

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem euler_circle_curve_derivative {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) {q : ℝ}
    (hDJ : ∀ z,fderiv ℝ F z (phaseJ z)=q•phaseJ (F z)) (s : ℝ) (z : PlanePhase ι) :
    HasDerivAt (fun t => F (phaseRotate t z)) (q•phaseJ (F (phaseRotate s z))) s := by
  have hh := (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (phaseRotate s z)).hasFDerivAt.comp_hasDerivAt s
    (phaseRotate_hasDerivAt s z)
  simpa only [hDJ,Function.comp_def] using hh

 theorem euler_circle_untwisted_derivative {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) {q : ℝ}
    (hDJ : ∀ z,fderiv ℝ F z (phaseJ z)=q•phaseJ (F z)) (s : ℝ) (z : PlanePhase ι) :
    HasDerivAt (fun t => phaseRotate (-q*t) (F (phaseRotate t z))) 0 s := by
  have hL : HasDerivAt (fun t : ℝ => -q*t) (-q) s := by
    simpa only [mul_one,Function.id_def] using (hasDerivAt_id s).const_mul (-q)
  have hg := euler_circle_curve_derivative hF hDJ s z
  have hJg := (phaseJ (ι := κ)).hasFDerivAt.comp_hasDerivAt s hg
  have hh := (((Real.hasDerivAt_cos (-q*s)).scomp s hL).smul hg).add
    (((Real.hasDerivAt_sin (-q*s)).scomp s hL).smul hJg)
  change HasDerivAt (fun t => phaseRotate (-q*t) (F (phaseRotate t z))) _ s at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Function.comp_apply,map_smul,phaseJ_sq,smul_neg,smul_smul,smul_eq_mul]
  module

 theorem euler_circle_equivariant {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) {q : ℝ}
    (hD : ∀ z,fderiv ℝ F z z=q•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v)) (s : ℝ) (z : PlanePhase ι) :
    F (phaseRotate s z)=phaseRotate (q*s) (F z) := by
  have hDJ (z : PlanePhase ι) : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z) := by rw [hJ,hD,map_smul]
  have hc := is_const_of_deriv_eq_zero
    (fun t => (euler_circle_untwisted_derivative hF hDJ t z).differentiableAt)
    (fun t => (euler_circle_untwisted_derivative hF hDJ t z).deriv) s 0
  simp only [mul_zero,phaseRotate_zero] at hc
  have hh := congrArg (phaseRotate (q*s)) hc
  rw [←phaseRotate_add] at hh
  simpa only [neg_mul,add_neg_cancel,phaseRotate_zero] using hh

end

section

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

 theorem exists_degree_relative_radial_moser
    {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hD : ∀ z,fderiv ℝ F z z=q•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    (e : PlanePhase ν →L[ℝ] PlanePhase ι) (P : PlanePhase ι →L[ℝ] PlanePhase ν)
    (hPe : P.comp e=ContinuousLinearMap.id ℝ (PlanePhase ν))
    (he : IsSmoothEmbedding 𝓘(ℝ,PlanePhase ν) 𝓘(ℝ,PlanePhase ι) ∞ e)
    (heD : ∀ z v,phaseDot (e z) (e v)=phaseDot z v)
    (heA : ∀ z v,phaseArea (e z) (e v)=phaseArea z v)
    (heJ : ∀ z,e (phaseJ z)=phaseJ (e z))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0)
    (hχr : ∀ a,χ a∈Icc (0:ℝ) 1) {c d : ℝ} (hc : 0 < c) (hd : 0≤d)
    (hq : 0≤q) (hdq : q*d<1)
    {K : Set (PlanePhase ι)} (hK : IsCompact K)
    (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K) :
    ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
      (∀ x,Φ (0,x)=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (t,x))=phaseSq x) ∧
      (∀ t∈Icc (0:ℝ) 1,(fun x => Φ (t,x)) '' range e=range e) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈K,∀ v w,
        manifoldPullback Φ (fun s => manifoldExteriorOneForm (cutoffDegreePrimitive q F c d χ s)) t x v w=
          c*phaseArea v w) := by
  have hdata := cutoffDegreePrimitive_moser_data hF hF0 hD hJ hχ hχ0 hχr hc hd hq hdq
  have heq (s : ℝ) (z : PlanePhase ν) :
      e ((phaseCircleAction (ι := ν)).slice s z)=(phaseCircleAction (ι := ι)).slice s (e z) := by
    change e (phaseRotate (2*Real.pi*s) z)=phaseRotate (2*Real.pi*s) (e z)
    simp only [phaseRotate_apply,map_add,map_smul,heJ]
  have hDJ (z : PlanePhase ι) : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z) := by rw [hJ,hD,map_smul]
  obtain ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hr,hepres,hω⟩ := exists_circle_relative_radial_moser_bp240 hdata
    phaseCircleAction phaseCircleAction (by positivity : 2*Real.pi≠0) phaseCircleAction_generator
    e P hPe he heq (fun s t z => cutoffDegreeForm_circle_invariant hF hF0
      (euler_circle_equivariant hF hD hJ) hχ hχ0 c d s t z)
    (fun t ht z => cutoffDegreeForm_subspace_nondegenerate hF hF0 hD hJ e heD heA heJ hχ hχ0 hχr hc hd hq hdq ht z)
    hK isOpen_univ (subset_univ K) hKr hc.ne'
    (fun s z _ v => cutoffDegreePrimitive_circle_contraction hF hF0 hDJ hχ c d s z v)
    (fun s z => cutoffDegreePrimitive_time_circle hF hF0 hDJ hχ hχ0 c d s z)
  refine ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hr,hepres,?_⟩
  intro t ht x hx v w
  rw [hω t ht x hx v w,vector_exteriorOneForm]
  have hezero : cutoffDegreePrimitive q F c d χ 0=c•(standardLiouville (ι := ι)) := by
    funext z
    simp only [cutoffDegreePrimitive,zero_mul,zero_smul,add_zero,Pi.smul_apply]
  rw [hezero,euclideanExteriorOneForm_smul c
    ((standardLiouville_smooth (ι := ι)).contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),standardLiouville_exterior]
  rfl

end

variable {ι : Type} [Fintype ι]

 theorem radius_preserving_fderiv {f : PlanePhase ι → PlanePhase ι}
    (hf : ContDiff ℝ ∞ f) (hr : ∀ z,phaseSq (f z)=phaseSq z) (z v : PlanePhase ι) :
    phaseDot (f z) (fderiv ℝ f z v)=phaseDot z v := by
  have he : (fun x => phaseSq (f x))=phaseSq := funext hr
  have h := (phaseSq_hasFDerivAt (f z)).comp z (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt
  have hd := congrArg (fun L => L v) h.fderiv
  change fderiv ℝ (fun x => phaseSq (f x)) z v=_ at hd
  rw [he,phaseSq_fderiv] at hd
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul] at hd
  linarith

 theorem moment_pullback_generator {f g : PlanePhase ι → PlanePhase ι}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hgf : LeftInverse g f) (hfg : RightInverse g f)
    (hr : ∀ z,phaseSq (f z)=phaseSq z)
    {Ω : PlanePhase ι → PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ}
    {c : ℝ} {z : PlanePhase ι}
    (hsk : ∀ y v w,Ω y v w= -Ω y w v)
    (hnd : (Ω (f z)).IsInvertible)
    (hm : ∀ y v,Ω y v (phaseJ y)=c*phaseDot y v)
    (hω : ∀ v w,Ω (f z) (fderiv ℝ f z v) (fderiv ℝ f z w)=c*phaseArea v w) :
    fderiv ℝ f z (phaseJ z)=phaseJ (f z) := by
  have he : (fun x => f (g x))=id := funext hfg
  have hd := (hf.differentiable (by simp) (g (f z))).hasFDerivAt.comp (f z)
    (hg.differentiable (by simp) (f z)).hasFDerivAt
  have hD (v : PlanePhase ι) : fderiv ℝ f z (fderiv ℝ g (f z) v)=v := by
    have hh := congrArg (fun L => L v) hd.fderiv
    change fderiv ℝ (fun x => f (g x)) (f z) v=_ at hh
    rw [he,fderiv_id,hgf z] at hh
    exact hh.symm
  rcases hnd with ⟨L,hL⟩
  apply L.injective
  change L.toContinuousLinearMap _=L.toContinuousLinearMap _
  rw [hL]
  ext v
  calc
    _= -Ω (f z) v (fderiv ℝ f z (phaseJ z)) := hsk _ _ _
    _= -Ω (f z) v (phaseJ (f z)) := by
      congr 1
      rw [←hD v,hω,phaseArea_J_right,hm,radius_preserving_fderiv hf hr,phaseDot_symm]
    _=_ := (hsk _ _ _).symm

 theorem circle_equivariant_on_radius {f : PlanePhase ι → PlanePhase ι}
    (hf : ContDiff ℝ ∞ f) {K : Set (PlanePhase ι)}
    (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K)
    (hJ : ∀ z∈K,fderiv ℝ f z (phaseJ z)=phaseJ (f z))
    (s : ℝ) {z : PlanePhase ι} (hz : z∈K) :
    f (phaseRotate s z)=phaseRotate s (f z) := by
  have hd (t : ℝ) : HasDerivAt (fun u => f (phaseRotate u z)) (phaseJ (f (phaseRotate t z))) t := by
    have hh := (hf.differentiable (by simp) (phaseRotate t z)).hasFDerivAt.comp_hasDerivAt t
      (phaseRotate_hasDerivAt t z)
    simpa only [Function.comp_def,hJ _ (hKr z hz _ (phaseSq_rotate t z))] using hh
  have hu (t : ℝ) : HasDerivAt (fun u => phaseRotate (-u) (f (phaseRotate u z))) 0 t := by
    have hL := (hasDerivAt_id t).neg
    have hJg := (phaseJ (ι := ι)).hasFDerivAt.comp_hasDerivAt t (hd t)
    have hh := (((Real.hasDerivAt_cos (-t)).scomp t hL).smul (hd t)).add
      (((Real.hasDerivAt_sin (-t)).scomp t hL).smul hJg)
    change HasDerivAt (fun u => phaseRotate (-u) (f (phaseRotate u z))) _ t at hh
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Function.comp_apply,phaseJ_sq,smul_neg,smul_eq_mul]
    module
  have hc := is_const_of_deriv_eq_zero (fun t => (hu t).differentiableAt) (fun t => (hu t).deriv) s 0
  simp only [neg_zero,phaseRotate_zero] at hc
  have hh := congrArg (phaseRotate s) hc
  rw [←phaseRotate_add,add_neg_cancel,phaseRotate_zero] at hh
  exact hh

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

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

 theorem exists_shell_profile {a b : ℝ} (ha : 0<a) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ χ=ᶠ[𝓝 (0:ℝ)] 0 ∧
      (∀ x,χ x∈Icc (0:ℝ) 1) ∧ ∀ x∈Icc a b,χ=ᶠ[𝓝 x] 1 := by
  obtain ⟨χ,hχ,_,hχU,hχ1,hχr⟩ := exists_smooth_cutoff (isCompact_Icc (a := a) (b := b))
    isOpen_Ioi (fun x hx => lt_of_lt_of_le ha hx.1)
  have hn : (0:ℝ)∉tsupport χ := by
    intro h
    exact (lt_irrefl (0:ℝ)) (hχU h)
  refine ⟨χ,hχ,?_,hχr,?_⟩
  · exact (notMem_tsupport_iff_eventuallyEq.mp hn)
  · intro x hx
    exact hχ1.filter_mono (nhds_le_nhdsSet hx)

 theorem cutoffDegreeForm_shell {F : PlanePhase ι → PlanePhase κ}
    {χ : ℝ → ℝ} {z : PlanePhase ι} (hχz : χ=ᶠ[𝓝 (phaseSq z)] 1)
    (q c d : ℝ) :
    euclideanExteriorOneForm (cutoffDegreePrimitive q F c d χ 1) z=
      euclideanExteriorOneForm (degreeConePrimitive q F c d) z := by
  have he : cutoffDegreePrimitive q F c d χ 1=ᶠ[𝓝 z] degreeConePrimitive q F c d := by
    filter_upwards [hχz.comp_tendsto phaseSq_smooth.continuous.continuousAt] with y hy
    change χ (phaseSq y)=1 at hy
    rw [cutoffDegreePrimitive_eq,radialDegreeConePrimitive,hy,one_mul,mul_one]
  simp only [euclideanExteriorOneForm,he.fderiv_eq]

 theorem exists_degree_relative_shell_maps_bp240_oai
    {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hD : ∀ z,fderiv ℝ F z z=q•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    (e : PlanePhase ν →L[ℝ] PlanePhase ι) (P : PlanePhase ι →L[ℝ] PlanePhase ν)
    (hPe : P.comp e=ContinuousLinearMap.id ℝ (PlanePhase ν))
    (he : IsSmoothEmbedding 𝓘(ℝ,PlanePhase ν) 𝓘(ℝ,PlanePhase ι) ∞ e)
    (heD : ∀ z v,phaseDot (e z) (e v)=phaseDot z v)
    (heA : ∀ z v,phaseArea (e z) (e v)=phaseArea z v)
    (heJ : ∀ z,e (phaseJ z)=phaseJ (e z))
    {a b c d : ℝ} (ha : 0<a) (hc : 0 < c) (hd : 0≤d) (hq : 0≤q) (hdq : q*d<1) :
    ∃ f g : PlanePhase ι → PlanePhase ι,
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧ LeftInverse g f ∧ RightInverse g f ∧
      (∀ z,phaseSq (f z)=phaseSq z) ∧ (∀ z,phaseSq (g z)=phaseSq z) ∧
      (∀ z,f z∈range e ↔ z∈range e) ∧ (∀ z,g z∈range e ↔ z∈range e) ∧
      (∀ s z,z∈phaseShell a b → f (phaseRotate s z)=phaseRotate s (f z)) ∧
      (∀ s z,z∈phaseShell a b → g (phaseRotate s z)=phaseRotate s (g z)) ∧
      (∀ z∈phaseShell a b,∀ v w,
        euclideanExteriorOneForm (degreeConePrimitive q F c d) (f z)
          (fderiv ℝ f z v) (fderiv ℝ f z w)=c*phaseArea v w) := by
  obtain ⟨χ,hχ,hχ0,hχr,hχ1⟩ := exists_shell_profile (b := b) ha
  have hKr (x : PlanePhase ι) (hx : x∈phaseShell a b) (y : PlanePhase ι)
      (hy : phaseSq y=phaseSq x) : y∈phaseShell a b := phaseShell_radial a b hx hy
  obtain ⟨Φ,Ψ,hΦ,hΨ,_,hi,hr,hepres,hω⟩ := exists_degree_relative_radial_moser
    hF hF0 hD hJ e P hPe he heD heA heJ hχ hχ0 hχr hc hd hq hdq (phaseShell_isCompact a b) hKr
  have h1 : (1:ℝ)∈Icc (0:ℝ) 1 := by simp
  let f := fun z => Φ (1,z)
  let g := fun z => Ψ (1,z)
  have hf : ContDiff ℝ ∞ f := hΦ.comp (contDiff_const.prodMk contDiff_id)
  have hg : ContDiff ℝ ∞ g := hΨ.comp (contDiff_const.prodMk contDiff_id)
  have hgf : LeftInverse g f := fun z => (hi 1 h1 z).1
  have hfg : RightInverse g f := fun z => (hi 1 h1 z).2
  have hfr : ∀ z,phaseSq (f z)=phaseSq z := hr 1 h1
  have hgr (z) : phaseSq (g z)=phaseSq z := by
    have hh := hfr (g z)
    rw [hfg z] at hh
    exact hh.symm
  have hfe (z) : f z∈range e ↔ z∈range e := by
    constructor
    · intro hz
      rw [←hepres 1 h1] at hz
      rcases hz with ⟨x,hx,hfx⟩
      exact hgf.injective hfx ▸ hx
    · intro hz
      have hh := mem_image_of_mem f hz
      rwa [hepres 1 h1] at hh
  have hge (z) : g z∈range e ↔ z∈range e := by
    have hh := hfe (g z)
    rw [hfg z] at hh
    exact hh.symm
  let Ω := fun z => euclideanExteriorOneForm (cutoffDegreePrimitive q F c d χ 1) z
  have hω' (z) (hz : z∈phaseShell a b) (v w) :
      Ω (f z) (fderiv ℝ f z v) (fderiv ℝ f z w)=c*phaseArea v w := by
    simpa only [manifoldPullback,vector_exteriorOneForm,preferredDifferential,mfderiv_eq_fderiv,ContinuousLinearMap.bilinearComp_apply] using hω 1 h1 z hz v w
  have hDJ (z : PlanePhase ι) : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z) := by rw [hJ,hD,map_smul]
  have hfJ (z) (hz : z∈phaseShell a b) : fderiv ℝ f z (phaseJ z)=phaseJ (f z) := by
    apply moment_pullback_generator hf hg hgf hfg hfr
      (fun y v w => by simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply] <;> ring)
      (cutoffDegreePrimitive_nondegenerate hF hF0 hD hJ hχ hχ0 hχr hc hd hq hdq h1 (f z))
      (fun y v => ?_) (hω' z hz)
    simpa only [vector_exteriorOneForm] using cutoffDegreePrimitive_circle_contraction hF hF0 hDJ hχ c d 1 y v
  have hfc (s z) (hz : z∈phaseShell a b) : f (phaseRotate s z)=phaseRotate s (f z) :=
    circle_equivariant_on_radius hf hKr hfJ s hz
  refine ⟨f,g,hf,hg,hgf,hfg,hfr,hgr,hfe,hge,hfc,?_,?_⟩
  · intro s z hz
    apply hgf.injective
    rw [hfg,hfc s (g z) (hKr z hz _ (hgr z)),hfg]
  · intro z hz v w
    rw [←cutoffDegreeForm_shell (hχ1 (phaseSq (f z)) (hKr z hz _ (hfr z))) q c d]
    exact hω' z hz v w

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.exists_degree_relative_shell_maps_bp240_oai := @OAI.PackingSufficiencySupport.Hamiltonian.exists_degree_relative_shell_maps_bp240_oai
