-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.CubicModel.tendsto_radial_cubic_cutoff_mass_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:44.592418+00:00
-- url     : https://prove2.me/submissions/c7a0c9d1-81aa-40c4-a7ae-542afe384c5a

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_radialEndResidue_error_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_tendsto_curveCutoff_bounded_residue_bp240

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

theorem staticPullbackOneForm_smoothAt {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (staticPullbackOneForm α g) x :=
  (ha.comp x hg).clm_comp (hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

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

end
section

variable {ι : Type*} [Fintype ι]

theorem phaseArea_self (z : PlanePhase ι) : phaseArea z z = 0 := by
  have h := phaseArea_skew z z
  linarith

end
section

variable {ι : Type*} [Fintype ι]

theorem affineFSPrimitive_smooth (a : ℝ) :
    ContDiff ℝ ∞ (affineFSPrimitive a : PlanePhase ι → _) := by
  have hc : ContDiff ℝ ∞ (fun z : PlanePhase ι => a/(2*(1+phaseSq z))) :=
    contDiff_const.div (contDiff_const.mul (contDiff_const.add phaseSq_smooth))
      (fun z => mul_ne_zero (by norm_num) (fs_den_pos z).ne')
  exact hc.smul (phaseArea (ι := ι)).contDiff

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vector_chartOneForm (α : E → E →L[ℝ] ℝ) (c y : E) :
    chartOneForm α c y=α y := by
  simp only [chartOneForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,ContinuousLinearMap.comp_id,id_eq]

theorem vector_oneForm_smooth {α : E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α) :
    SmoothOneFormFamily (fun _ : ℝ => α) := by
  intro c
  simpa only [vector_chartOneForm,Function.comp_def] using
    (hα.comp contDiff_snd).contDiffOn

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

 theorem projection_contDiff : ContDiff ℂ ∞ projection := by
  exact (((contDiff_apply ℂ ℂ 0).comp contDiff_snd).sub contDiff_fst).prodMk
    (((contDiff_apply ℂ ℂ 1).comp contDiff_snd).sub contDiff_fst)

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_CubicFubiniStudy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
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

 theorem weightedPhaseInclusion_smooth (D m : ℕ) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin 3))) ∞ (weightedPhaseInclusion D m) :=
  (affinePhase 3).contDiff.contMDiff.comp
    (((weightedProjection_contDiff D m).restrict_scalars ℝ).contMDiff.comp
      ((projection_contDiff.restrict_scalars ℝ).contMDiff.comp
        (real_inclusion_contMDiff (parameters 0))))

 theorem weightedFSPrimitive_smooth (D m : ℕ) (c : ℝ) :
    SmoothOneFormFamily (fun _ : ℝ => weightedFSPrimitive D m c) := by
  have hα : SmoothOneFormFamily (fun _ : ℝ =>
      (affineFSPrimitive c : PlanePhase (Option (Fin 3)) → _)) :=
    vector_oneForm_smooth (affineFSPrimitive_smooth c)
  intro b
  exact manifoldPullbackOneForm_smooth (α := fun _ : ℝ =>
    (affineFSPrimitive c : PlanePhase (Option (Fin 3)) → _)) (weightedPhaseInclusion_smooth D m) hα b

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function
open Hamiltonian
open scoped BigOperators ComplexConjugate

 theorem complexArea_apply (z v : ℂ) : complexArea z v=z.re*v.im-z.im*v.re := by
  simp only [complexArea,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

 theorem complex_div_im (s u : ℂ) : (u/s).im=complexArea s u/Complex.normSq s := by
  rw [Complex.div_im,complexArea_apply]
  ring

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped Manifold ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N] [TopologicalSpace P] [ChartedSpace G P]

 theorem manifoldMapDifferential_comp {g : N → M} {f : P → N} {x : P}
    (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g (f x))
    (hf : MDifferentiableAt 𝓘(ℝ,G) 𝓘(ℝ,F) f x) :
    manifoldMapDifferential (E := E) (F := G) (g ∘ f) x=
      (manifoldMapDifferential (E := E) (F := F) g (f x)).comp (manifoldMapDifferential (E := F) (F := G) f x) :=
  (hg.hasMFDerivAt.comp x hf.hasMFDerivAt).mfderiv

 theorem euclideanPullbackOneForm_comp {g : N → M} {f : G → N} {x : G}
    (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g (f x))
    (hf : MDifferentiableAt 𝓘(ℝ,G) 𝓘(ℝ,F) f x)
    (α : ManifoldOneForm E M) :
    euclideanPullbackOneForm (E := F) (F := G) (fun _ => manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) f (0,x)=
      euclideanPullbackOneForm (E := E) (F := G) (fun _ => α) (g ∘ f) (0,x) := by
  change (α (g (f x))).comp
    ((manifoldMapDifferential (E := E) (F := F) g (f x)).comp
      (manifoldMapDifferential (E := F) (F := G) f x))=
    (α (g (f x))).comp (manifoldMapDifferential (E := E) (F := G) (g ∘ f) x)
  rw [manifoldMapDifferential_comp hg hf]

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

theorem complexCartesian_complex_smul_sq (ζ : ℂ) (y : ι → ℂ) :
    phaseSq (complexCartesian (ζ•y))=Complex.normSq ζ*phaseSq (complexCartesian y) := by
  simp only [complexCartesian_sq,Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum]

end
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

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_ExponentialMoment
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem partition_pos {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (x : E) :
    0<partition w a x := by
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (ha i) (Real.exp_pos _)
  · exact Finset.univ_nonempty

 omit [Nonempty ι] in
 theorem partition_contDiff (w : ι → E) (a : ι → ℝ) : ContDiff ℝ ∞ (partition w a) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (((innerSL ℝ (w i)).contDiff).exp)

 omit [Nonempty ι] in
 theorem partition_hasFDerivAt (w : ι → E) (a : ι → ℝ) (x : E) :
    HasFDerivAt (partition w a) (innerSL ℝ (gradient w a x)) x := by
  have h := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((innerSL ℝ (w i)).hasFDerivAt (x := x)).exp).const_mul (a i))
  convert! h using 1
  · ext y
    simp [partition]
  · simp only [gradient,map_sum,map_smul,smul_smul,innerSL_apply_apply]

 theorem partition_coercive [ProperSpace E] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {δ : ℝ} (hδ : 0<δ)
    (hw : ∀ x : E,∃ i,δ*‖x‖≤ inner ℝ (w i) x) :
    Tendsto (partition w a) (cocompact E) atTop := by
  classical
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  have hb (x : E) : a j*Real.exp (δ*‖x‖)≤partition w a x := by
    obtain ⟨i,hi⟩ := hw x
    calc
      a j*Real.exp (δ*‖x‖)≤a i*Real.exp (inner ℝ (w i) x) :=
        mul_le_mul (hj i (Finset.mem_univ i)) (Real.exp_le_exp.mpr hi)
          (Real.exp_pos _).le (ha i).le
      _≤partition w a x := by
        exact Finset.single_le_sum
          (fun k _ => (mul_pos (ha k) (Real.exp_pos (inner ℝ (w k) x))).le) (Finset.mem_univ i)
  exact tendsto_atTop_mono hb ((Real.tendsto_exp_atTop.comp
    (tendsto_norm_cocompact_atTop.const_mul_atTop hδ)).const_mul_atTop (ha j))

 theorem exists_gradient_zero [ProperSpace E] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {δ : ℝ} (hδ : 0<δ)
    (hw : ∀ x : E,∃ i,δ*‖x‖≤ inner ℝ (w i) x) :
    ∃ x : E,gradient w a x=0 := by
  obtain ⟨x,hx⟩ := (partition_contDiff w a).continuous.exists_forall_le
    (partition_coercive ha hδ hw)
  refine ⟨x,?_⟩
  have hm : IsLocalMin (partition w a) x := Filter.Eventually.of_forall hx
  have hz := hm.hasFDerivAt_eq_zero (partition_hasFDerivAt w a x)
  have he := congrArg (fun L : E →L[ℝ] ℝ => L (gradient w a x)) hz
  change inner ℝ (gradient w a x) (gradient w a x)=0 at he
  exact inner_self_eq_zero.mp he

 theorem exp_difference_nonneg (u v : ℝ) :
    0≤(Real.exp u-Real.exp v)*(u-v) := by
  rcases le_total v u with h|h
  · exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)) (sub_nonneg.mpr h)
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h))
      (sub_nonpos.mpr h)

 theorem exp_difference_pos {u v : ℝ} (h : v<u) :
    0<(Real.exp u-Real.exp v)*(u-v) :=
  mul_pos (sub_pos.mpr (Real.exp_lt_exp.mpr h)) (sub_pos.mpr h)

 omit [Nonempty ι] in
 theorem gradient_zero_unique {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {δ : ℝ} (hδ : 0<δ)
    (hw : ∀ x : E,∃ i,δ*‖x‖≤ inner ℝ (w i) x) {x y : E}
    (hx : gradient w a x=0) (hy : gradient w a y=0) : x=y := by
  classical
  by_contra hxy
  have hd : 0<δ*‖x-y‖ := mul_pos hδ (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
  obtain ⟨j,hj⟩ := hw (x-y)
  have hjp : inner ℝ (w j) y< inner ℝ (w j) x := by
    rw [inner_sub_right] at hj
    linarith
  have hs : 0< ∑ i,a i*((Real.exp (inner ℝ (w i) x)-Real.exp (inner ℝ (w i) y))*
      (inner ℝ (w i) x-inner ℝ (w i) y)) := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (ha i).le (exp_difference_nonneg _ _)
    · exact ⟨j,Finset.mem_univ j,mul_pos (ha j) (exp_difference_pos hjp)⟩
  have he : ∑ i,a i*((Real.exp (inner ℝ (w i) x)-Real.exp (inner ℝ (w i) y))*
      (inner ℝ (w i) x-inner ℝ (w i) y))=
      inner ℝ (gradient w a x-gradient w a y) (x-y) := by
    simp only [gradient,inner_sub_left,sum_inner,real_inner_smul_left,inner_sub_right,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,hx,hy,sub_self,inner_zero_left] at hs
  exact (lt_irrefl (0:ℝ)) hs

 omit [Nonempty ι] in
 theorem gradient_center (w : ι → E) (a : ι → ℝ) (p x : E) :
    gradient (fun i => w i-p) a x = Real.exp (-inner ℝ p x) •
      (gradient w a x-partition w a x • p) := by
  have he (i : ι) : (a i * Real.exp (inner ℝ (w i-p) x)) • (w i-p) =
      Real.exp (-inner ℝ p x) • ((a i*Real.exp (inner ℝ (w i) x)) • w i-
        (a i*Real.exp (inner ℝ (w i) x)) • p) := by
    rw [inner_sub_left,sub_eq_add_neg (inner ℝ (w i) x),Real.exp_add]
    simp only [smul_sub,smul_smul]
    congr 1 <;> congr 1 <;> ring
  simp only [gradient,he,←Finset.smul_sum,Finset.sum_sub_distrib,←Finset.sum_smul,partition]

 theorem moment_eq_iff_gradient_center_zero {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (p x : E) :
    moment w a x=p ↔ gradient (fun i => w i-p) a x=0 := by
  rw [gradient_center,smul_eq_zero]
  simp only [Real.exp_ne_zero,false_or,sub_eq_zero]
  dsimp [moment]
  rw [inv_smul_eq_iff₀ (partition_pos ha x).ne']

 theorem exists_unique_moment [ProperSpace E] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {p : E} (hp : Surrounds w p) : ∃! x,moment w a x=p := by
  obtain ⟨δ,hδ,hw⟩ := hp
  obtain ⟨x,hx⟩ := exists_gradient_zero ha hδ hw
  refine ⟨x,(moment_eq_iff_gradient_center_zero ha p x).mpr hx,?_⟩
  intro y hy
  exact gradient_zero_unique ha hδ hw ((moment_eq_iff_gradient_center_zero ha p y).mp hy) hx

 omit [Fintype ι] in
 theorem surrounds_of_interior {w : ι → E} {p : E}
    (hp : p∈interior (convexHull ℝ (range w))) : Surrounds w p := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  refine ⟨ε/2,half_pos hε,?_⟩
  intro v
  by_cases hv : v=0
  · subst v
    exact ⟨Classical.ofNonempty,by simp⟩
  have hvp : 0<‖v‖ := norm_pos_iff.mpr hv
  let z := p+((ε/2)/‖v‖) • v
  have hz : z∈convexHull ℝ (range w) := by
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    dsimp [z]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos (half_pos hε) hvp),
      div_mul_cancel₀ _ hvp.ne']
    linarith
  obtain ⟨y,⟨i,rfl⟩,hi⟩ := ((innerSL ℝ v).toLinearMap.convexOn convex_univ).exists_ge_of_mem_convexHull
    (subset_univ (range w)) hz
  refine ⟨i,?_⟩
  change inner ℝ v z≤ inner ℝ v (w i) at hi
  have he : inner ℝ v z=inner ℝ v p+(ε/2)*‖v‖ := by
    dsimp [z]
    rw [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  rw [he] at hi
  rw [inner_sub_left,real_inner_comm v (w i),real_inner_comm v p]
  linarith

 omit [Fintype ι] [Nonempty ι] in
 theorem surrounds_isOpen (w : ι → E) : IsOpen {p | Surrounds w p} := by
  apply Metric.isOpen_iff.mpr
  intro p hp
  obtain ⟨δ,hδ,hw⟩ := hp
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro q hq
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro v
  obtain ⟨i,hi⟩ := hw v
  refine ⟨i,?_⟩
  have hc := real_inner_le_norm (q-p) v
  have hnorm : ‖q-p‖<δ/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hq
  have hmul := mul_le_mul_of_nonneg_right hnorm.le (norm_nonneg v)
  rw [inner_sub_left] at hi hc ⊢
  linarith

end
section

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem hessian_apply (w : ι → E) (a : ι → ℝ) (x v : E) :
    hessian w a x v=∑ i, (a i*Real.exp (inner ℝ (w i) x)*inner ℝ (w i) v) • w i := by
  simp [hessian]

 theorem gradient_hasFDerivAt (w : ι → E) (a : ι → ℝ) (x : E) :
    HasFDerivAt (gradient w a) (hessian w a x) x := by
  have h := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    ((((innerSL ℝ (w i)).hasFDerivAt (x := x)).exp).const_mul (a i)).smul_const (w i))
  convert! h using 1
  · ext y
    simp [gradient]
  · simp only [hessian,smul_smul,innerSL_apply_apply]

 theorem hessian_inner (w : ι → E) (a : ι → ℝ) (x v : E) :
    inner ℝ (hessian w a x v) v=
      ∑ i,(a i*Real.exp (inner ℝ (w i) x))*(inner ℝ (w i) v)^2 := by
  rw [hessian_apply,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left]
  ring

 theorem hessian_positive {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (hw : ∀ v : E,v≠0 → ∃ i,inner ℝ (w i) v≠0) (x : E) {v : E} (hv : v≠0) :
    0< inner ℝ (hessian w a x v) v := by
  classical
  rw [hessian_inner]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_pos (ha i) (Real.exp_pos _)).le (sq_nonneg _)
  · obtain ⟨i,hi⟩ := hw v hv
    exact ⟨i,Finset.mem_univ i,mul_pos (mul_pos (ha i) (Real.exp_pos _)) (sq_pos_of_ne_zero hi)⟩

 theorem hessian_isInvertible [FiniteDimensional ℝ E] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hw : ∀ v : E,v≠0 → ∃ i,inner ℝ (w i) v≠0) (x : E) :
    (hessian w a x).IsInvertible := by
  have hi : Injective (hessian w a x) := by
    intro v u h
    by_contra hn
    have hp := hessian_positive ha hw x (sub_ne_zero.mpr hn)
    rw [map_sub,h,sub_self,inner_zero_left] at hp
    exact (lt_irrefl (0:ℝ)) hp
  let L := ContinuousLinearEquiv.ofBijective (hessian w a x)
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi))
  exact ⟨L,rfl⟩

 omit [Fintype ι] in
 theorem surrounds_separates {w : ι → E} {p : E} (hp : Surrounds w p)
    {v : E} (hv : v≠0) : ∃ i,inner ℝ (w i-p) v≠0 := by
  obtain ⟨δ,hδ,hw⟩ := hp
  obtain ⟨i,hi⟩ := hw v
  exact ⟨i,(lt_of_lt_of_le (mul_pos hδ (norm_pos_iff.mpr hv)) hi).ne'⟩

 theorem centeredGradient_contDiff (w : ι → E) :
    ContDiff ℝ ∞ (fun q : ((ι → ℝ) × E) × E => gradient (fun i => w i-q.1.2) q.1.1 q.2) := by
  apply ContDiff.sum
  intro i _
  have ha : ContDiff ℝ ∞ (fun q : ((ι → ℝ) × E) × E => q.1.1 i) := by fun_prop
  have hu : ContDiff ℝ ∞ (fun q : ((ι → ℝ) × E) × E => w i-q.1.2) := by fun_prop
  exact (ha.mul ((hu.inner ℝ contDiff_snd).exp)).smul hu

end

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem inverse_spec {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) : moment w a (inverse w a p)=p :=
  invFun_eq (exists_unique_moment ha hp).exists

 theorem inverse_unique {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) {x : E} (hx : moment w a x=p) : x=inverse w a p :=
  (exists_unique_moment ha hp).unique hx (inverse_spec ha hp)

 omit [Nonempty ι] in
 theorem positiveCoefficients_isOpen : IsOpen {a : ι → ℝ | ∀ i,0<a i} := by
  have h : IsOpen (⋂ i : ι,{a : ι → ℝ | 0<a i}) :=
    isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  simp

 theorem inverse_contDiffAt {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × E => inverse w q.1 q.2) (a,p) := by
  let q := (a,p)
  let x := inverse w a p
  let F : ((ι → ℝ) × E) × E → E :=
    fun t => gradient (fun i => w i-t.1.2) t.1.1 t.2
  have hF : ContDiff ℝ ∞ F := centeredGradient_contDiff w
  have hpartial : (fderiv ℝ F (q,x)).comp (ContinuousLinearMap.inr ℝ ((ι → ℝ) × E) E)=
      hessian (fun i => w i-p) a x := by
    have hc := ((hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (q,x)).hasFDerivAt.comp x
      ((hasFDerivAt_const q x).prodMk (hasFDerivAt_id x)))
    exact hc.unique (gradient_hasFDerivAt (fun i => w i-p) a x)
  have hinv : (fderiv ℝ F (q,x) ∘L ContinuousLinearMap.inr ℝ ((ι → ℝ) × E) E).IsInvertible := by
    rw [hpartial]
    exact hessian_isInvertible ha (fun _ hv => surrounds_separates hp hv) x
  have hzero : F (q,x)=0 :=
    (moment_eq_iff_gradient_center_zero ha p x).mp (inverse_spec ha hp)
  have hapos : ∀ᶠ t : (ι → ℝ) × E in 𝓝 q,∀ i,0<t.1 i := by
    apply (positiveCoefficients_isOpen.preimage continuous_fst).mem_nhds
    exact ha
  have htpos : ∀ᶠ t : (ι → ℝ) × E in 𝓝 q,Surrounds w t.2 := by
    apply ((surrounds_isOpen w).preimage continuous_snd).mem_nhds
    exact hp
  have hloc := hF.contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv
  apply hloc.congr_of_eventuallyEq
  filter_upwards [hF.contDiffAt.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv,hapos,htpos]
    with t ht hta htp
  rw [hzero] at ht
  have hm := (moment_eq_iff_gradient_center_zero hta t.2 _).mpr ht
  exact (inverse_unique hta htp hm).symm

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem monomial_nonneg (k : ℕ × ℕ) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    0 ≤ monomial k r := mul_nonneg (pow_nonneg hr.1 _) (pow_nonneg hr.2 _)

theorem polynomial_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (hzero : ∃ i,k i=(0,0)) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    0<polynomial k a r := by
  classical
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (ha i).le (monomial_nonneg _ hr)
  · obtain ⟨i,hi⟩ := hzero
    refine ⟨i,Finset.mem_univ i,?_⟩
    simpa [hi,monomial] using ha i

theorem polynomial_contDiff (k : ι → ℕ × ℕ) :
    ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => polynomial k q.1 q.2) := by
  apply ContDiff.sum
  intro i _
  dsimp [monomial]
  fun_prop

theorem centered_contDiff (k : ι → ℕ × ℕ) :
    ContDiff ℝ ∞ (fun q : ((ι → ℝ) × Plane) × Plane => centered k q.1.1 q.1.2 q.2) := by
  apply ContDiff.prodMk <;> apply ContDiff.sum <;> intro i _ <;> dsimp [monomial] <;> fun_prop

theorem centered_eq (k : ι → ℕ × ℕ) (a : ι → ℝ) (p r : Plane) :
    centered k a p r=numerator k a r-polynomial k a r • p := by
  apply Prod.ext
  · change (∑ i, (((k i).1:ℝ)-p.1)*a i*monomial (k i) r)=
      (∑ i, ((k i).1:ℝ)*a i*monomial (k i) r)-(∑ i,a i*monomial (k i) r)*p.1
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · change (∑ i, (((k i).2:ℝ)-p.2)*a i*monomial (k i) r)=
      (∑ i, ((k i).2:ℝ)*a i*monomial (k i) r)-(∑ i,a i*monomial (k i) r)*p.2
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem centered_moment {k : ι → ℕ × ℕ} {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) : centered k a (moment k a r) r=0 := by
  rw [centered_eq,moment,smul_smul,mul_inv_cancel₀ hP,one_smul,sub_self]

theorem monomial_hasFDerivAt (k : ℕ × ℕ) (r : Plane) :
    HasFDerivAt (monomial k) (monomialDerivative k r) r := by
  have h := (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x:=r)).pow k.1).mul
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x:=r)).pow k.2)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro v
  simp [monomialDerivative]
  ring

theorem centered_hasFDerivAt (k : ι → ℕ × ℕ) (a : ι → ℝ) (p r : Plane) :
    HasFDerivAt (centered k a p) (centeredDerivative k a p r) r := by
  convert! (HasFDerivAt.sum (u := Finset.univ) (fun i _ => (monomial_hasFDerivAt (k i) r).const_mul
    ((((k i).1:ℝ)-p.1)*a i))).prodMk
    (HasFDerivAt.sum (u := Finset.univ) (fun i _ => (monomial_hasFDerivAt (k i) r).const_mul
    ((((k i).2:ℝ)-p.2)*a i))) using 1
  all_goals try with_reducible_and_instances rfl
  ext v <;> simp [centered]

theorem zero_power_derivative (n : ℕ) :
    (n:ℝ)*(0:ℝ)^(n-1)=if n=1 then 1 else 0 := by
  rcases n with _|n
  · simp
  · rcases n with _|n
    · simp
    · simp

theorem monomial_axis (k : ℕ × ℕ) (t : ℝ) :
    monomial k (0,t)=if k.1=0 then t^k.2 else 0 := by
  by_cases h : k.1=0
  · simp [monomial,h]
  · simp [monomial,h,zero_pow h]

theorem monomialDerivative_axis (k : ℕ × ℕ) (t : ℝ) (v : Plane) :
    monomialDerivative k (0,t) v=
      (if k.1=1 then t^k.2 else 0)*v.1+
      (if k.1=0 then (k.2:ℝ)*t^(k.2-1) else 0)*v.2 := by
  simp only [monomialDerivative,add_apply,
    smul_apply,
    smul_eq_mul,zero_power_derivative]
  by_cases h0 : k.1=0
  · simp [h0]
  · by_cases h1 : k.1=1
    · simp [h1]
    · simp [h0,h1,zero_pow h0]

theorem centered_axis_snd (k : ι → ℕ × ℕ) (a : ι → ℝ) (p : Plane) (t : ℝ) :
    (centered k a p (0,t)).2=∑ i,(((k i).2:ℝ)-p.2)*faceMass (k i) (a i) t := by
  apply Finset.sum_congr rfl
  intro i _
  rw [monomial_axis]
  by_cases h : (k i).1=0 <;> simp [faceMass,h,mul_assoc]

theorem centeredDerivative_axis_fst (k : ι → ℕ × ℕ) (a : ι → ℝ) (p t : ℝ) (v : Plane) :
    (centeredDerivative k a (0,p) (0,t) v).1=transverse k a t*v.1 := by
  simp only [centeredDerivative,ContinuousLinearMap.prod_apply,
    sum_apply,smul_apply,smul_eq_mul,
    monomialDerivative_axis,sub_zero,transverse,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h0 : (k i).1=0
  · simp [h0]
  · by_cases h1 : (k i).1=1
    · simp [h1,mul_assoc]
    · simp [h0,h1]

theorem centeredDerivative_axis_snd (k : ι → ℕ × ℕ) (a : ι → ℝ) (p t u : ℝ) :
    (centeredDerivative k a (0,p) (0,t) (0,u)).2=active k a p t*u := by
  simp only [centeredDerivative,ContinuousLinearMap.prod_apply,
    sum_apply,smul_apply,smul_eq_mul,
    monomialDerivative_axis,mul_zero,zero_add,active,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (k i).1=0 <;> simp [h,mul_assoc]

theorem transverse_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (he : ∃ i,k i=(1,0)) {t : ℝ} (ht : 0≤t) : 0<transverse k a t := by
  classical
  apply Finset.sum_pos'
  · intro i _
    split_ifs
    · exact mul_nonneg (ha i).le (pow_nonneg ht _)
    · rfl
  · obtain ⟨i,hi⟩ := he
    exact ⟨i,Finset.mem_univ i,by simpa [hi] using ha i⟩

theorem nat_mul_power (n : ℕ) (t : ℝ) :
    (n:ℝ)*t^(n-1)*t=(n:ℝ)*t^n := by
  rcases n with _|n
  · simp
  · simp only [Nat.succ_sub_one,pow_succ]
    ring

theorem active_variance (k : ι → ℕ × ℕ) (a : ι → ℝ) (p t : ℝ)
    (hz : (centered k a (0,p) (0,t)).2=0) :
    active k a p t*t=∑ i,(((k i).2:ℝ)-p)^2*faceMass (k i) (a i) t := by
  rw [centered_axis_snd] at hz
  have he : active k a p t*t =
      (∑ i,(((k i).2:ℝ)-p)^2*faceMass (k i) (a i) t)+
        p*(∑ i,(((k i).2:ℝ)-p)*faceMass (k i) (a i) t) := by
    rw [active,Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (k i).1=0
    · simp only [ite_eq_left h,faceMass]
      calc
        (((k i).2:ℝ)-p)*a i*((k i).2:ℝ)*t^((k i).2-1)*t =
            ((((k i).2:ℝ)-p)*a i)*(((k i).2:ℝ)*t^((k i).2-1)*t) := by ring
        _ = _ := by rw [nat_mul_power]; ring
    · simp [h,faceMass]
  simpa only [hz,mul_zero,add_zero] using he

theorem active_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (hzero : ∃ i,k i=(0,0)) (he : ∃ i,k i=(0,1)) {p t : ℝ} (ht : 0<t)
    (hz : (centered k a (0,p) (0,t)).2=0) : 0<active k a p t := by
  have hV : 0<∑ i,(((k i).2:ℝ)-p)^2*faceMass (k i) (a i) t := by
    classical
    apply Finset.sum_pos'
    · intro i _
      apply mul_nonneg (sq_nonneg _)
      unfold faceMass
      split_ifs
      · exact mul_nonneg (ha i).le (pow_nonneg ht.le _)
      · rfl
    · by_cases hp : p=0
      · obtain ⟨i,hi⟩ := he
        exact ⟨i,Finset.mem_univ i,by simpa [faceMass,hi,hp] using mul_pos (ha i) ht⟩
      · obtain ⟨i,hi⟩ := hzero
        refine ⟨i,Finset.mem_univ i,?_⟩
        simpa [faceMass,hi] using mul_pos (sq_pos_of_ne_zero hp) (ha i)
  rw [← active_variance k a p t hz] at hV
  exact (mul_pos_iff_of_pos_right ht).mp hV

end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RadialSlopes
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem slopeNumerator_contDiff (k : ι → ℕ × ℕ) :
    ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => slopeNumerator k q.1 q.2) := by
  apply ContDiff.prodMk <;> apply ContDiff.sum <;> intro i _ <;> fun_prop

theorem slope_contDiffAt {k : ι → ℕ × ℕ} {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => slope k q.1 q.2) (a,r) :=
  ((polynomial_contDiff k).contDiffAt.inv hP).smul (slopeNumerator_contDiff k).contDiffAt

theorem slopeNumerator_fst_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (he : ∃ i,k i=(1,0)) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    0<(slopeNumerator k a r).1 := by
  classical
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha i).le)
      (pow_nonneg hr.1 _)) (pow_nonneg hr.2 _)
  · obtain ⟨i,hi⟩ := he
    exact ⟨i,Finset.mem_univ i,by simpa [hi] using ha i⟩

theorem slopeNumerator_snd_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (he : ∃ i,k i=(0,1)) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    0<(slopeNumerator k a r).2 := by
  classical
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha i).le)
      (pow_nonneg hr.1 _)) (pow_nonneg hr.2 _)
  · obtain ⟨i,hi⟩ := he
    exact ⟨i,Finset.mem_univ i,by simpa [hi] using ha i⟩

theorem slope_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (hzero : ∃ i,k i=(0,0)) (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) : 0<(slope k a r).1 ∧ 0<(slope k a r).2 := by
  have hP := inv_pos.mpr (polynomial_pos ha hzero hr)
  exact ⟨mul_pos hP (slopeNumerator_fst_pos ha he0 hr),
    mul_pos hP (slopeNumerator_snd_pos ha he1 hr)⟩

theorem moment_eq_radius_slope (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    moment k a r=(r.1*(slope k a r).1,r.2*(slope k a r).2) := by
  have h0 : (numerator k a r).1=r.1*(slopeNumerator k a r).1 := by
    change (∑ i,((k i).1:ℝ)*a i*monomial (k i) r)=
      r.1*(∑ i,((k i).1:ℝ)*a i*r.1^((k i).1-1)*r.2^(k i).2)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold monomial
    calc
      _=a i*r.2^(k i).2*(((k i).1:ℝ)*r.1^(k i).1) := by ring
      _=_ := by rw [← nat_mul_power]; ring
  have h1 : (numerator k a r).2=r.2*(slopeNumerator k a r).2 := by
    change (∑ i,((k i).2:ℝ)*a i*monomial (k i) r)=
      r.2*(∑ i,((k i).2:ℝ)*a i*r.1^(k i).1*r.2^((k i).2-1))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold monomial
    calc
      _=a i*r.1^(k i).1*(((k i).2:ℝ)*r.2^(k i).2) := by ring
      _=_ := by rw [← nat_mul_power]; ring
  apply Prod.ext
  · change (polynomial k a r)⁻¹*(numerator k a r).1=
      r.1*((polynomial k a r)⁻¹*(slopeNumerator k a r).1)
    rw [h0]
    ring
  · change (polynomial k a r)⁻¹*(numerator k a r).2=
      r.2*((polynomial k a r)⁻¹*(slopeNumerator k a r).2)
    rw [h1]
    ring

theorem moment_eq_of_centered {k : ι → ℕ × ℕ} {a : ι → ℝ} {p r : Plane}
    (hP : polynomial k a r≠0) (hz : centered k a p r=0) : moment k a r=p := by
  rw [centered_eq,sub_eq_zero] at hz
  rw [moment,hz,smul_smul,inv_mul_cancel₀ hP,one_smul]

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Function

 theorem openTrapezoid_isOpen (A B : ℝ) : IsOpen (openTrapezoid A B) := by
  have hc (j : Fin 2) : Continuous (fun p : MomentPlane => p j) := by fun_prop
  exact ((isOpen_lt continuous_const (hc 0)).inter
    ((isOpen_lt (hc 0) continuous_const).inter
      ((isOpen_lt continuous_const (hc 1)).inter
        (isOpen_lt ((hc 0).add (hc 1)) continuous_const))))

 theorem trapezoid_mem_convexHull {A B : ℝ} {p : MomentPlane} (hp : p∈openTrapezoid A B) :
    p∈convexHull ℝ (range (trapezoidCorners A B)) := by
  have hA : 0<A := hp.1.trans hp.2.1
  have hB : 0<B-p 0 := by linarith [hp.2.2.1,hp.2.2.2]
  let l := p 0/A
  let t := p 1/(B-p 0)
  have hl0 : 0<l := div_pos hp.1 hA
  have hl1 : l<1 := (div_lt_one hA).mpr hp.2.1
  have ht0 : 0<t := div_pos hp.2.2.1 hB
  have ht1 : t<1 := (div_lt_one hB).mpr (by linarith [hp.2.2.2])
  let c : Fin 4 → ℝ := ![(1-l)*(1-t),l*(1-t),l*t,(1-l)*t]
  apply mem_convexHull_of_exists_fintype c (trapezoidCorners A B)
  · intro i
    fin_cases i <;> dsimp [c] <;> positivity
  · simp only [c,Fin.sum_univ_succ]
    dsimp
    ring
  · intro i
    exact mem_range_self i
  · ext j
    fin_cases j <;>
      simp [c,trapezoidCorners,planeVector,Fin.sum_univ_succ,l,t] <;>
      field_simp <;> ring

 theorem trapezoid_interior {ι : Type*} {w : ι → MomentPlane} {A B : ℝ}
    (hw : range (trapezoidCorners A B)⊆range w) {p : MomentPlane}
    (hp : p∈openTrapezoid A B) : p∈interior (convexHull ℝ (range w)) := by
  have hsub : openTrapezoid A B⊆convexHull ℝ (range w) := by
    intro q hq
    exact convexHull_mono hw (trapezoid_mem_convexHull hq)
  exact interior_maximal hsub (openTrapezoid_isOpen A B) hp

 theorem trapezoidWeight_corners {A B : ℕ} (hAB : A≤B) :
    range (trapezoidCorners A B)⊆range (trapezoidWeight A B) := by
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · refine ⟨⟨(⟨0,by omega⟩,⟨0,by omega⟩),by simp⟩,?_⟩
    simp [trapezoidWeight,trapezoidCorners]
  · refine ⟨⟨(⟨A,by omega⟩,⟨0,by omega⟩),by simp [hAB]⟩,?_⟩
    simp [trapezoidWeight,trapezoidCorners]
  · refine ⟨⟨(⟨A,by omega⟩,⟨B-A,by omega⟩),by simp [Nat.add_sub_of_le hAB]⟩,?_⟩
    simp [trapezoidWeight,trapezoidCorners,Nat.cast_sub hAB]
  · refine ⟨⟨(⟨0,by omega⟩,⟨B,by omega⟩),by simp⟩,?_⟩
    simp [trapezoidWeight,trapezoidCorners]

 theorem trapezoidWeight_surrounds {A B : ℕ} (hAB : A≤B) {p : MomentPlane}
    (hp : p∈openTrapezoid A B) : Surrounds (trapezoidWeight A B) p :=
  surrounds_of_interior (trapezoid_interior (trapezoidWeight_corners hAB) hp)

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem expRadius_logRadius {r : Plane} (hr : 0 < r.1 ∧ 0 < r.2) :
    expRadius (logRadius r)=r := by
  apply Prod.ext <;> simp [expRadius,logRadius,planeVector,Real.exp_log,hr.1,hr.2]

theorem monomial_expRadius (k : ℕ × ℕ) (x : MomentPlane) :
    monomial k (expRadius x)=Real.exp (inner ℝ (planeVector k.1 k.2) x) := by
  simp [monomial,expRadius,planeVector,PiLp.inner_apply,Fin.sum_univ_succ,
    ← Real.exp_nat_mul,← Real.exp_add,mul_comm]

theorem polynomial_expRadius (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : MomentPlane) :
    polynomial k a (expRadius x)=partition (weight k) a x := by
  apply Finset.sum_congr rfl
  intro i _
  rw [monomial_expRadius]
  rfl

theorem moment_expRadius (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : MomentPlane) :
    planeVector (moment k a (expRadius x)).1 (moment k a (expRadius x)).2=
      FiniteMoment.moment (weight k) a x := by
  rw [FiniteMoment.moment,← polynomial_expRadius]
  ext j
  fin_cases j <;>
    simp [moment,numerator,gradient,weight,planeVector,monomial_expRadius,
      mul_assoc,mul_comm,mul_left_comm]

theorem exists_positive_radial_solution [Nonempty ι] {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {p : Plane} (hp : Surrounds (weight k) (planeVector p.1 p.2)) :
    ∃ r : Plane, (0 < r.1 ∧ 0 < r.2) ∧ moment k a r=p := by
  let x := inverse (weight k) a (planeVector p.1 p.2)
  refine ⟨expRadius x,⟨Real.exp_pos _,Real.exp_pos _⟩,?_⟩
  have he := moment_expRadius k a x
  rw [inverse_spec ha hp] at he
  exact Prod.ext (congrArg (fun z : MomentPlane => z 0) he)
    (congrArg (fun z : MomentPlane => z 1) he)

theorem moment_axis_fst (k : ι → ℕ × ℕ) (a : ι → ℝ) (t : ℝ) :
    (moment k a (0,t)).1=0 := by
  change (polynomial k a (0,t))⁻¹*(∑ i,((k i).1:ℝ)*a i*monomial (k i) (0,t))=0
  have h : (∑ i,((k i).1:ℝ)*a i*monomial (k i) (0,t))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [monomial_axis]
    by_cases h : (k i).1=0 <;> simp [h]
  rw [h,mul_zero]

theorem moment_origin (k : ι → ℕ × ℕ) (a : ι → ℝ) : moment k a (0,0)=(0,0) := by
  apply Prod.ext
  · exact moment_axis_fst k a 0
  · change (polynomial k a (0,0))⁻¹*(∑ i,((k i).2:ℝ)*a i*monomial (k i) (0,0))=0
    have h : (∑ i,((k i).2:ℝ)*a i*monomial (k i) (0,0))=0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases h : (k i).2=0
      · simp [monomial,h]
      · simp [monomial,zero_pow h]
    rw [h,mul_zero]

theorem active_origin_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (he : ∃ i,k i=(0,1)) : 0<active k a 0 0 := by
  classical
  have heq : active k a 0 0=∑ i,if (k i).1=0 ∧ (k i).2=1 then a i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (k i).1=0
    · simp only [ite_eq_left h,sub_zero]
      have hmul : ((k i).2:ℝ)*a i*((k i).2:ℝ)*(0:ℝ)^((k i).2-1)=
          ((k i).2:ℝ)*a i*(((k i).2:ℝ)*(0:ℝ)^((k i).2-1)) := by ring
      rw [hmul,zero_power_derivative]
      by_cases h1 : (k i).2=1 <;> simp [h,h1]
    · simp [h]
  rw [heq]
  apply Finset.sum_pos'
  · intro i _
    split_ifs
    · exact (ha i).le
    · rfl
  · obtain ⟨i,hi⟩ := he
    exact ⟨i,Finset.mem_univ i,by simpa [hi] using ha i⟩

theorem centeredDerivative_axis_isInvertible {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    (centeredDerivative k a (moment k a (0,t)) (0,t)).IsInvertible := by
  let p := (moment k a (0,t)).2
  have hm : moment k a (0,t)=(0,p) := Prod.ext (moment_axis_fst k a t) rfl
  rw [hm]
  have hz : (centered k a (0,p) (0,t)).2=0 := by
    have h := centered_moment (polynomial_pos (r := (0,t)) ha hzero ⟨le_rfl,ht⟩).ne'
    rw [hm] at h
    exact congrArg Prod.snd h
  have hA : 0<transverse k a t := transverse_pos ha he0 ht
  have hB : 0<active k a p t := by
    rcases eq_or_lt_of_le ht with ht0|htp
    · have hp : p=0 := by simp [p,← ht0,moment_origin]
      rw [← ht0,hp]
      exact active_origin_pos ha he1
    · exact active_pos ha hzero he1 htp hz
  have hker : ∀ v,centeredDerivative k a (0,p) (0,t) v=0 → v=0 := by
    intro v hv
    have h0 := congrArg Prod.fst hv
    rw [centeredDerivative_axis_fst] at h0
    change transverse k a t*v.1=0 at h0
    have hv0 : v.1=0 := (mul_eq_zero.mp h0).resolve_left hA.ne'
    have heq : v=(0,v.2) := Prod.ext hv0 rfl
    have h1 := congrArg Prod.snd hv
    rw [heq,centeredDerivative_axis_snd] at h1
    change active k a p t*v.2=0 at h1
    exact Prod.ext hv0 ((mul_eq_zero.mp h1).resolve_left hB.ne')
  have hi : Injective (centeredDerivative k a (0,p) (0,t)) := by
    intro v u h
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub,h,sub_self]
  let L := ContinuousLinearEquiv.ofBijective (centeredDerivative k a (0,p) (0,t))
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi))
  exact ⟨L,rfl⟩

theorem exists_smooth_axis_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a (0,t))=(0,t) ∧
      ContDiffAt ℝ ∞ f (a,moment k a (0,t)) ∧
      ∀ᶠ q in 𝓝 (a,moment k a (0,t)),centered k q.1 q.2 (f q)=0 := by
  let q := (a,moment k a (0,t))
  let r : Plane := (0,t)
  let F : ((ι → ℝ) × Plane) × Plane → Plane := fun s => centered k s.1.1 s.1.2 s.2
  have hF : ContDiff ℝ ∞ F := centered_contDiff k
  have hpartial : (fderiv ℝ F (q,r)).comp (ContinuousLinearMap.inr ℝ ((ι → ℝ) × Plane) Plane)=
      centeredDerivative k a (moment k a (0,t)) r := by
    have hc := ((hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (q,r)).hasFDerivAt.comp r
      ((hasFDerivAt_const q r).prodMk (hasFDerivAt_id r)))
    exact hc.unique (centered_hasFDerivAt k a (moment k a (0,t)) r)
  have hinv : (fderiv ℝ F (q,r) ∘L ContinuousLinearMap.inr ℝ ((ι → ℝ) × Plane) Plane).IsInvertible := by
    rw [hpartial]
    exact centeredDerivative_axis_isInvertible ha hzero he0 he1 ht
  have hz : F (q,r)=0 := centered_moment (polynomial_pos (r := (0,t)) ha hzero ⟨le_rfl,ht⟩).ne'
  refine ⟨hF.contDiffAt.implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv,?_,
    hF.contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv,?_⟩
  · exact hF.contDiffAt.implicitFunction_apply_self (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv
  · simpa only [hz] using hF.contDiffAt.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators
open Function

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exp_difference_strict {u v : ℝ} (h : u≠v) :
    0<(Real.exp u-Real.exp v)*(u-v) := by
  rcases lt_or_gt_of_ne h with hlt|hgt
  · have h := exp_difference_pos hlt
    nlinarith
  · exact exp_difference_pos hgt

theorem gradient_zero_unique_of_separates {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hw : ∀ v : E,v≠0 → ∃ i,inner ℝ (w i) v≠0)
    {x y : E} (hx : gradient w a x=0) (hy : gradient w a y=0) : x=y := by
  classical
  by_contra hxy
  obtain ⟨j,hj⟩ := hw (x-y) (sub_ne_zero.mpr hxy)
  have hjn : inner ℝ (w j) x≠inner ℝ (w j) y := by
    rwa [inner_sub_right,sub_ne_zero] at hj
  have hs : 0<∑ i,a i*((Real.exp (inner ℝ (w i) x)-Real.exp (inner ℝ (w i) y))*
      (inner ℝ (w i) x-inner ℝ (w i) y)) := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (ha i).le (exp_difference_nonneg _ _)
    · exact ⟨j,Finset.mem_univ j,mul_pos (ha j) (exp_difference_strict hjn)⟩
  have he : ∑ i,a i*((Real.exp (inner ℝ (w i) x)-Real.exp (inner ℝ (w i) y))*
      (inner ℝ (w i) x-inner ℝ (w i) y))=
      inner ℝ (gradient w a x-gradient w a y) (x-y) := by
    simp only [gradient,inner_sub_left,sum_inner,real_inner_smul_left,inner_sub_right,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,hx,hy,sub_self,inner_zero_left] at hs
  exact (lt_irrefl (0:ℝ)) hs

theorem moment_unique_of_separates [Nonempty ι] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {p : E}
    (hw : ∀ v : E,v≠0 → ∃ i,inner ℝ (w i-p) v≠0)
    {x y : E} (hx : moment w a x=p) (hy : moment w a y=p) : x=y :=
  gradient_zero_unique_of_separates ha hw
    ((moment_eq_iff_gradient_center_zero ha p x).mp hx)
    ((moment_eq_iff_gradient_center_zero ha p y).mp hy)

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem sum_face (k : ι → ℕ × ℕ) (f : ι → ℝ) :
    (∑ i, if (k i).1=0 then f i else 0)=∑ i : Face k,f i.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

theorem polynomial_face_exp (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : ℝ) :
    polynomial k a (0,Real.exp x)=partition (faceWeight k) (fun i => a i.val) x := by
  calc
    _=∑ i,if (k i).1=0 then a i*Real.exp (((k i).2:ℝ)*x) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [monomial_axis]
      by_cases h : (k i).1=0 <;> simp [h,Real.exp_nat_mul]
    _=_ := by
      rw [sum_face]
      apply Finset.sum_congr rfl
      intro i _
      simp [faceWeight,mul_comm]

theorem numerator_face_exp_snd (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : ℝ) :
    (numerator k a (0,Real.exp x)).2=
      gradient (faceWeight k) (fun i => a i.val) x := by
  calc
    _=∑ i,if (k i).1=0 then ((k i).2:ℝ)*a i*Real.exp (((k i).2:ℝ)*x) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [monomial_axis]
      by_cases h : (k i).1=0 <;> simp [h,Real.exp_nat_mul]
    _=_ := by
      rw [sum_face]
      apply Finset.sum_congr rfl
      intro i _
      simp [faceWeight,mul_comm,mul_left_comm,mul_assoc]

theorem moment_face_exp (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : ℝ) :
    moment k a (0,Real.exp x)=
      (0,FiniteMoment.moment (faceWeight k) (fun i => a i.val) x) := by
  apply Prod.ext
  · exact moment_axis_fst k a _
  · change (polynomial k a (0,Real.exp x))⁻¹*(numerator k a (0,Real.exp x)).2=_
    rw [polynomial_face_exp,numerator_face_exp_snd]
    rfl

omit [Fintype ι] in
theorem interval_surrounds {w : ι → ℝ} {B p : ℝ}
    (h0 : ∃ i,w i=0) (hB : ∃ i,w i=B) (hp : 0<p ∧ p<B) : Surrounds w p := by
  refine ⟨min p (B-p),lt_min hp.1 (sub_pos.mpr hp.2),?_⟩
  intro v
  rcases le_total 0 v with hv|hv
  · obtain ⟨i,hi⟩ := hB
    refine ⟨i,?_⟩
    simp only [hi,Real.norm_eq_abs,abs_of_nonneg hv]
    change min p (B-p)*v≤v*(B-p)
    nlinarith [min_le_right p (B-p)]
  · obtain ⟨i,hi⟩ := h0
    refine ⟨i,?_⟩
    simp only [hi,Real.norm_eq_abs,abs_of_nonpos hv,zero_sub]
    change min p (B-p)*(-v)≤v*(-p)
    nlinarith [min_le_left p (B-p)]

omit [Fintype ι] in
theorem interval_separates {w : ι → ℝ} {B : ℝ} (hB : B≠0)
    (h0 : ∃ i,w i=0) (h1 : ∃ i,w i=B) (p : ℝ) {v : ℝ} (hv : v≠0) :
    ∃ i,inner ℝ (w i-p) v≠0 := by
  by_cases hp : p=0
  · obtain ⟨i,hi⟩ := h1
    refine ⟨i,?_⟩
    simpa [hi,hp] using mul_ne_zero hv hB
  · obtain ⟨i,hi⟩ := h0
    refine ⟨i,?_⟩
    simpa [hi] using mul_ne_zero hv (neg_ne_zero.mpr hp)

theorem exists_axis_solution {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) {B : ℕ} (hB : ∃ i,k i=(0,B)) {p : ℝ}
    (hp : 0<p ∧ p<B) : ∃ t : ℝ,0<t ∧ moment k a (0,t)=(0,p) := by
  obtain ⟨i0,hi0⟩ := h0
  obtain ⟨iB,hiB⟩ := hB
  let : Nonempty (Face k) := ⟨⟨i0,by simp [hi0]⟩⟩
  have hw0 : ∃ i : Face k,faceWeight k i=0 := ⟨⟨i0,by simp [hi0]⟩,by simp [faceWeight,hi0]⟩
  have hwB : ∃ i : Face k,faceWeight k i=(B:ℝ) := ⟨⟨iB,by simp [hiB]⟩,by simp [faceWeight,hiB]⟩
  obtain ⟨x,hx,_⟩ := exists_unique_moment (fun i : Face k => ha i.val)
    (interval_surrounds hw0 hwB hp)
  exact ⟨Real.exp x,Real.exp_pos _,by rw [moment_face_exp,hx]⟩

theorem positive_axis_unique {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) (h1 : ∃ i,k i=(0,1)) {t u p : ℝ} (ht : 0<t) (hu : 0<u)
    (htp : moment k a (0,t)=(0,p)) (hup : moment k a (0,u)=(0,p)) : t=u := by
  obtain ⟨i0,hi0⟩ := h0
  obtain ⟨i1,hi1⟩ := h1
  let : Nonempty (Face k) := ⟨⟨i0,by simp [hi0]⟩⟩
  have hw0 : ∃ i : Face k,faceWeight k i=0 := ⟨⟨i0,by simp [hi0]⟩,by simp [faceWeight,hi0]⟩
  have hw1 : ∃ i : Face k,faceWeight k i=(1:ℝ) := ⟨⟨i1,by simp [hi1]⟩,by simp [faceWeight,hi1]⟩
  have hmt : FiniteMoment.moment (faceWeight k) (fun i => a i.val) (Real.log t)=p := by
    have h := moment_face_exp k a (Real.log t)
    rw [Real.exp_log ht,htp] at h
    exact (congrArg Prod.snd h).symm
  have hmu : FiniteMoment.moment (faceWeight k) (fun i => a i.val) (Real.log u)=p := by
    have h := moment_face_exp k a (Real.log u)
    rw [Real.exp_log hu,hup] at h
    exact (congrArg Prod.snd h).symm
  have he := moment_unique_of_separates (fun i : Face k => ha i.val)
    (fun v hv => interval_separates one_ne_zero hw0 hw1 p hv) hmt hmu
  have h := congrArg Real.exp he
  simpa only [Real.exp_log ht,Real.exp_log hu] using h

end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RadialSwap
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
variable {ι : Type*} [Fintype ι]

theorem polynomial_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    polynomial (fun i => (k i).swap) a r.swap=polynomial k a r := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [monomial,Prod.fst_swap,Prod.snd_swap]
  ring

theorem numerator_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    numerator (fun i => (k i).swap) a r.swap=(numerator k a r).swap := by
  apply Prod.ext <;> apply Finset.sum_congr rfl <;> intro i _
  all_goals simp only [monomial,Prod.fst_swap,Prod.snd_swap]; ring

theorem moment_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    moment (fun i => (k i).swap) a r.swap=(moment k a r).swap := by
  unfold moment
  rw [polynomial_swap,numerator_swap]
  rfl

theorem centered_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (p r : Plane) :
    centered (fun i => (k i).swap) a p.swap r.swap=(centered k a p r).swap := by
  apply Prod.ext <;> apply Finset.sum_congr rfl <;> intro i _
  all_goals simp only [monomial,Prod.fst_swap,Prod.snd_swap]; ring

theorem exists_smooth_other_axis_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a (t,0))=(t,0) ∧
      ContDiffAt ℝ ∞ f (a,moment k a (t,0)) ∧
      ∀ᶠ q in 𝓝 (a,moment k a (t,0)),centered k q.1 q.2 (f q)=0 := by
  have hzero' : ∃ i,(k i).swap=(0,0) := by
    obtain ⟨i,hi⟩ := hzero
    exact ⟨i,by simp [hi]⟩
  have he0' : ∃ i,(k i).swap=(1,0) := by
    obtain ⟨i,hi⟩ := he1
    exact ⟨i,by simp [hi]⟩
  have he1' : ∃ i,(k i).swap=(0,1) := by
    obtain ⟨i,hi⟩ := he0
    exact ⟨i,by simp [hi]⟩
  obtain ⟨f,hf,hfs,hfe⟩ := exists_smooth_axis_radial_solution ha hzero' he0' he1' ht
  have hm : moment (fun i => (k i).swap) a (0,t)=(moment k a (t,0)).swap :=
    moment_swap k a (t,0)
  rw [hm] at hf hfs hfe
  let F : (ι → ℝ) × Plane → Plane := fun q => (f (q.1,q.2.swap)).swap
  have hswap : ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,q.2.swap)) := by
    change ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,(q.2.2,q.2.1)))
    fun_prop
  refine ⟨F,?_,?_,?_⟩
  · dsimp [F]
    rw [hf]
    rfl
  · have hc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => f (q.1,q.2.swap))
        (a,moment k a (t,0)) := hfs.comp (a,moment k a (t,0)) hswap.contDiffAt
    exact hc.snd.prodMk hc.fst
  · have htend : Tendsto (fun q : (ι → ℝ) × Plane => (q.1,q.2.swap))
        (𝓝 (a,moment k a (t,0))) (𝓝 (a,(moment k a (t,0)).swap)) :=
      hswap.continuous.continuousAt
    have he := htend.eventually hfe
    filter_upwards [he] with q hq
    have h := congrArg Prod.swap hq
    have hr : centered k q.1 q.2 (F q)=
        (centered (fun i => (k i).swap) q.1 q.2.swap (f (q.1,q.2.swap))).swap := by
      have hh := centered_swap k q.1 q.2 (F q)
      simp only [F,Prod.swap_swap] at hh
      exact (congrArg Prod.swap hh).symm
    rw [hr,h]
    rfl




theorem basis_weights_separate {k : ι → ℕ × ℕ} (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) (p : MomentPlane)
    {v : MomentPlane} (hv : v≠0) : ∃ i,inner ℝ (weight k i-p) v≠0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨i0,hi0⟩ := h0
  obtain ⟨i1,hi1⟩ := he0
  obtain ⟨i2,hi2⟩ := he1
  have hp : inner ℝ p v=0 := by
    have h := hn i0
    have hw : weight k i0=0 := by ext j; fin_cases j <;> simp [weight,hi0,planeVector]
    simpa only [hw,zero_sub,inner_neg_left,neg_eq_zero] using h
  have hv0 : v 0=0 := by
    have h := hn i1
    simpa [inner_sub_left,hp,weight,hi1,planeVector,PiLp.inner_apply,Fin.sum_univ_succ] using h
  have hv1 : v 1=0 := by
    have h := hn i2
    simpa [inner_sub_left,hp,weight,hi2,planeVector,PiLp.inner_apply,Fin.sum_univ_succ] using h
  apply hv
  ext j
  fin_cases j <;> assumption

theorem positive_radial_unique_basis {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    {r s : Plane} (hr : 0 < r.1 ∧ 0 < r.2) (hs : 0 < s.1 ∧ 0 < s.2)
    (he : moment k a r=moment k a s) : r=s := by
  let : Nonempty ι := ⟨h0.choose⟩
  let p := planeVector (moment k a r).1 (moment k a r).2
  have hre : FiniteMoment.moment (weight k) a (logRadius r)=p := by
    rw [← moment_expRadius,expRadius_logRadius hr]
  have hse : FiniteMoment.moment (weight k) a (logRadius s)=p := by
    rw [← moment_expRadius,expRadius_logRadius hs,← he]
  have hh := moment_unique_of_separates ha (fun v hv => basis_weights_separate h0 he0 he1 p hv) hre hse
  have h := congrArg expRadius hh
  simpa only [expRadius_logRadius hr,expRadius_logRadius hs] using h

theorem moment_zero_coordinates {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    ((moment k a r).1=0 ↔ r.1=0) ∧ ((moment k a r).2=0 ↔ r.2=0) := by
  have hs := slope_pos ha h0 he0 he1 hr
  rw [moment_eq_radius_slope]
  exact ⟨mul_eq_zero_iff_right hs.1.ne',mul_eq_zero_iff_right hs.2.ne'⟩

theorem moment_injective_quadrant {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) :
    InjOn (moment k a) {r : Plane | 0 ≤ r.1 ∧ 0 ≤ r.2} := by
  intro r hr s hs he
  have hzr := moment_zero_coordinates ha h0 he0 he1 hr
  have hzs := moment_zero_coordinates ha h0 he0 he1 hs
  have hz0 : r.1=0 ↔ s.1=0 := hzr.1.symm.trans ((congrArg Prod.fst he) ▸ hzs.1)
  have hz1 : r.2=0 ↔ s.2=0 := hzr.2.symm.trans ((congrArg Prod.snd he) ▸ hzs.2)
  by_cases hr0 : r.1=0
  · have hs0 := hz0.mp hr0
    by_cases hr1 : r.2=0
    · exact Prod.ext (hr0.trans hs0.symm) (hr1.trans (hz1.mp hr1).symm)
    · have hrp : 0 < r.2 := lt_of_le_of_ne hr.2 (Ne.symm hr1)
      have hsp : 0 < s.2 := lt_of_le_of_ne hs.2 (Ne.symm (fun h => hr1 (hz1.mpr h)))
      have hrr : r=(0,r.2) := Prod.ext hr0 rfl
      have hss : s=(0,s.2) := Prod.ext hs0 rfl
      have hp : moment k a (0,r.2)=(0,(moment k a (0,r.2)).2) :=
        Prod.ext (moment_axis_fst k a _) rfl
      have hps : moment k a (0,s.2)=(0,(moment k a (0,r.2)).2) := by
        rw [← hss,← he,hrr]
        exact hp
      exact Prod.ext (hr0.trans hs0.symm) (positive_axis_unique ha h0 he1 hrp hsp hp hps)
  · have hs0 : s.1≠0 := fun h => hr0 (hz0.mpr h)
    have hrp : 0 < r.1 := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    have hsp : 0 < s.1 := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    by_cases hr1 : r.2=0
    · have hs1 := hz1.mp hr1
      have h0' : ∃ i,(k i).swap=(0,0) := by obtain ⟨i,hi⟩ := h0; exact ⟨i,by simp [hi]⟩
      have h1' : ∃ i,(k i).swap=(0,1) := by obtain ⟨i,hi⟩ := he0; exact ⟨i,by simp [hi]⟩
      have hrr : r.swap=(0,r.1) := Prod.ext hr1 rfl
      have hss : s.swap=(0,s.1) := Prod.ext hs1 rfl
      have hes : moment (fun i => (k i).swap) a r.swap=moment (fun i => (k i).swap) a s.swap := by
        rw [moment_swap,moment_swap,he]
      rw [hrr,hss] at hes
      have hp : moment (fun i => (k i).swap) a (0,r.1)=
          (0,(moment (fun i => (k i).swap) a (0,r.1)).2) :=
        Prod.ext (moment_axis_fst _ a _) rfl
      exact Prod.ext (positive_axis_unique ha h0' h1' hrp hsp hp (hes.symm.trans hp))
        (hr1.trans hs1.symm)
    · exact positive_radial_unique_basis ha h0 he0 he1
        ⟨hrp,lt_of_le_of_ne hr.2 (Ne.symm hr1)⟩
        ⟨hsp,lt_of_le_of_ne hs.2 (Ne.symm (fun h => hr1 (hz1.mpr h)))⟩ he




theorem exists_smooth_boundary_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=r ∧ ContDiffAt ℝ ∞ f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),centered k q.1 q.2 (f q)=0 := by
  rcases r with ⟨s,t⟩
  rcases hb with hs|ht
  · change s=0 at hs
    subst s
    exact exists_smooth_axis_radial_solution ha hzero he0 he1 hr.2
  · change t=0 at ht
    subst t
    exact exists_smooth_other_axis_radial_solution ha hzero he0 he1 hr.1

theorem exists_smooth_boundary_moment_inverse {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=r ∧ ContDiffAt ℝ ∞ f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),
        moment k q.1 (f q)=q.2 ∧
        (0≤(f q).1 ↔ 0≤q.2.1) ∧ (0≤(f q).2 ↔ 0≤q.2.2) ∧
        (0<(f q).1 ↔ 0<q.2.1) ∧ (0<(f q).2 ↔ 0<q.2.2) := by
  obtain ⟨f,hf,hfs,hfe⟩ := exists_smooth_boundary_radial_solution ha hzero he0 he1 hr hb
  let q0 := (a,moment k a r)
  have hc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,f q)) q0 :=
    contDiffAt_fst.prodMk hfs
  have hP := polynomial_pos ha hzero hr
  have hPc : ContinuousAt (fun q : (ι → ℝ) × Plane => polynomial k q.1 (f q)) q0 :=
    (polynomial_contDiff k).continuous.continuousAt.comp hc.continuousAt
  have hPe : ∀ᶠ q in 𝓝 q0,0<polynomial k q.1 (f q) := by
    apply hPc.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hP)
  have hsc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => slope k q.1 (f q)) q0 := by
    have hs := slope_contDiffAt hP.ne'
    have hh : (a,r)=(q0.1,f q0) := by simp [q0,hf]
    rw [hh] at hs
    exact hs.comp q0 hc
  have hs := slope_pos ha hzero he0 he1 hr
  have hse0 : ∀ᶠ q in 𝓝 q0,0<(slope k q.1 (f q)).1 := by
    apply hsc.continuousAt.fst.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hs.1)
  have hse1 : ∀ᶠ q in 𝓝 q0,0<(slope k q.1 (f q)).2 := by
    apply hsc.continuousAt.snd.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hs.2)
  refine ⟨f,hf,hfs,?_⟩
  filter_upwards [hfe,hPe,hse0,hse1] with q hq hPq hs0 hs1
  have hm := moment_eq_of_centered hPq.ne' hq
  refine ⟨hm,?_,?_,?_,?_⟩
  all_goals
    have he := moment_eq_radius_slope k q.1 (f q)
    rw [hm] at he
  · rw [show q.2.1=(f q).1*(slope k q.1 (f q)).1 from congrArg Prod.fst he]
    exact (mul_nonneg_iff_of_pos_right hs0).symm
  · rw [show q.2.2=(f q).2*(slope k q.1 (f q)).2 from congrArg Prod.snd he]
    exact (mul_nonneg_iff_of_pos_right hs1).symm
  · rw [show q.2.1=(f q).1*(slope k q.1 (f q)).1 from congrArg Prod.fst he]
    exact (mul_pos_iff_of_pos_right hs0).symm
  · rw [show q.2.2=(f q).2*(slope k q.1 (f q)).2 from congrArg Prod.snd he]
    exact (mul_pos_iff_of_pos_right hs1).symm




theorem nonnegativeInverse_nonneg (k : ι → ℕ × ℕ) (a : ι → ℝ) (p : Plane) :
    0≤(nonnegativeInverse k a p).1 ∧ 0≤(nonnegativeInverse k a p).2 :=
  (invFun (fun r : Quadrant => moment k a r.val) p).property

theorem nonnegativeInverse_spec {k : ι → ℕ × ℕ} {a : ι → ℝ} {p : Plane}
    (hp : ∃ r : Plane,(0 ≤ r.1 ∧ 0 ≤ r.2) ∧ moment k a r=p) :
    moment k a (nonnegativeInverse k a p)=p := by
  change (fun r : Quadrant => moment k a r.val)
    (invFun (fun r : Quadrant => moment k a r.val) p)=p
  exact invFun_eq (f := fun r : Quadrant => moment k a r.val)
    (by obtain ⟨r,hr,he⟩ := hp; exact ⟨⟨r,hr⟩,he⟩)

theorem nonnegativeInverse_of_moment {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) : nonnegativeInverse k a (moment k a r)=r := by
  apply moment_injective_quadrant ha h0 he0 he1 (nonnegativeInverse_nonneg _ _ _) hr
  exact nonnegativeInverse_spec ⟨r,hr,rfl⟩

theorem nonnegativeInverse_eq_of_moment {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r p : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (he : moment k a r=p) : nonnegativeInverse k a p=r := by
  rw [← he]
  exact nonnegativeInverse_of_moment ha h0 he0 he1 hr

theorem boundary_inverse_smooth_extension {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=nonnegativeInverse k a (moment k a r) ∧
      ContDiffAt ℝ ∞ f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),
        (∀ i,0<q.1 i) → 0≤q.2.1 → 0≤q.2.2 → nonnegativeInverse k q.1 q.2=f q := by
  obtain ⟨f,hf,hfs,hfe⟩ := exists_smooth_boundary_moment_inverse ha h0 he0 he1 hr hb
  refine ⟨f,hf.trans (nonnegativeInverse_of_moment ha h0 he0 he1 hr).symm,hfs,?_⟩
  filter_upwards [hfe] with q hq hqa hq0 hq1
  exact nonnegativeInverse_eq_of_moment hqa h0 he0 he1
    ⟨hq.2.1.mpr hq0,hq.2.2.1.mpr hq1⟩ hq.1

theorem boundary_inverse_coeff_contDiffAt {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ContDiffAt ℝ ∞ (fun b : ι → ℝ => nonnegativeInverse k b (moment k a r)) a := by
  obtain ⟨f,hf,hfs,hfe⟩ := boundary_inverse_smooth_extension ha h0 he0 he1 hr hb
  have hmap : ContDiff ℝ ∞ (fun b : ι → ℝ => (b,moment k a r)) := by fun_prop
  have hfc : ContDiffAt ℝ ∞ (fun b : ι → ℝ => f (b,moment k a r)) a :=
    hfs.comp a hmap.contDiffAt
  apply hfc.congr_of_eventuallyEq
  have hmapt : Tendsto (fun b : ι → ℝ => (b,moment k a r)) (𝓝 a) (𝓝 (a,moment k a r)) :=
    hmap.continuous.continuousAt
  have hape : ∀ᶠ b in 𝓝 a,∀ i,0<b i := positiveCoefficients_isOpen.mem_nhds ha
  filter_upwards [hmapt.eventually hfe,hape] with b hb hba
  have hsm := slope_pos ha h0 he0 he1 hr
  have hmr : 0≤(moment k a r).1 ∧ 0≤(moment k a r).2 := by
    rw [moment_eq_radius_slope]
    exact ⟨mul_nonneg hr.1 hsm.1.le,mul_nonneg hr.2 hsm.2.le⟩
  exact hb hba hmr.1 hmr.2


end

section

open scoped BigOperators Topology ContDiff
open Set Filter Function

theorem lattice_zero (A B : ℕ) : ∃ i : TrapezoidWeight A B,latticeIndex i=(0,0) :=
  ⟨⟨(⟨0,by omega⟩,⟨0,by omega⟩),by simp⟩,rfl⟩

theorem lattice_unit_fst {A B : ℕ} (hA : 0<A) (hAB : A≤B) :
    ∃ i : TrapezoidWeight A B,latticeIndex i=(1,0) :=
  ⟨⟨(⟨1,by omega⟩,⟨0,by omega⟩),by simp; omega⟩,rfl⟩

theorem lattice_unit_snd {A B : ℕ} (hA : 0<A) (hAB : A≤B) :
    ∃ i : TrapezoidWeight A B,latticeIndex i=(0,1) :=
  ⟨⟨(⟨0,by omega⟩,⟨1,by omega⟩),by simp; omega⟩,rfl⟩

theorem lattice_end_fst {A B : ℕ} (hAB : A≤B) :
    ∃ i : TrapezoidWeight A B,latticeIndex i=(A,0) :=
  ⟨⟨(⟨A,by omega⟩,⟨0,by omega⟩),by simp [hAB]⟩,rfl⟩

theorem lattice_end_snd (A B : ℕ) :
    ∃ i : TrapezoidWeight A B,latticeIndex i=(0,B) :=
  ⟨⟨(⟨0,by omega⟩,⟨B,by omega⟩),by simp⟩,rfl⟩

theorem trapezoid_radial_surjective {A B : ℕ} (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ∃ r : Plane,(0 ≤ r.1 ∧ 0 ≤ r.2) ∧ moment latticeIndex a r=p := by
  by_cases hp0 : p.1=0
  · by_cases hp1 : p.2=0
    · refine ⟨(0,0),⟨le_rfl,le_rfl⟩,?_⟩
      rw [moment_origin]
      exact Prod.ext hp0.symm hp1.symm
    · obtain ⟨t,ht,he⟩ := exists_axis_solution ha (lattice_zero A B) (lattice_end_snd A B)
        (p:=p.2) ⟨lt_of_le_of_ne hp.2.2.1 (Ne.symm hp1),by simpa [hp0] using hp.2.2.2⟩
      exact ⟨(0,t),⟨le_rfl,ht.le⟩,he.trans (Prod.ext hp0.symm rfl)⟩
  · have hp0p : 0<p.1 := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    by_cases hp1 : p.2=0
    · have hzero : ∃ i : TrapezoidWeight A B,(latticeIndex i).swap=(0,0) := by
        obtain ⟨i,hi⟩ := lattice_zero A B
        exact ⟨i,by simp [hi]⟩
      have hend : ∃ i : TrapezoidWeight A B,(latticeIndex i).swap=(0,A) := by
        obtain ⟨i,hi⟩ := lattice_end_fst hAB
        exact ⟨i,by simp [hi]⟩
      obtain ⟨t,ht,he⟩ := exists_axis_solution ha hzero hend ⟨hp0p,hp.2.1⟩
      refine ⟨(t,0),⟨ht.le,le_rfl⟩,?_⟩
      have hh := moment_swap latticeIndex a (t,0)
      change moment (fun i => (latticeIndex i).swap) a (0,t)=
        (moment latticeIndex a (t,0)).swap at hh
      rw [he] at hh
      have hx := congrArg Prod.swap hh
      exact (show moment latticeIndex a (t,0)=(p.1,0) by simpa using hx.symm).trans
        (Prod.ext rfl hp1.symm)
    · obtain ⟨r,hr,he⟩ := exists_positive_radial_solution ha
        (show Surrounds (weight (latticeIndex (A:=A) (B:=B))) (planeVector p.1 p.2) from
          trapezoidWeight_surrounds hAB ⟨hp0p,hp.2.1,lt_of_le_of_ne hp.2.2.1 (Ne.symm hp1),hp.2.2.2⟩)
      exact ⟨r,⟨hr.1.le,hr.2.le⟩,he⟩

theorem trapezoid_inverse_spec {A B : ℕ} (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) : moment latticeIndex a (nonnegativeInverse latticeIndex a p)=p :=
  nonnegativeInverse_spec (trapezoid_radial_surjective hAB ha hp)


end

section

open scoped BigOperators Topology ContDiff
open Set Filter Function
variable {ι : Type*} [Fintype ι]

theorem planeVector_contDiff : ContDiff ℝ ∞ (fun r : Plane => planeVector r.1 r.2) := by
  apply (contDiff_piLp 2).mpr
  intro j
  fin_cases j
  · exact contDiff_fst
  · exact contDiff_snd

theorem expRadius_contDiff : ContDiff ℝ ∞ expRadius := by
  apply ContDiff.prodMk <;> apply ContDiff.exp <;> fun_prop

theorem nonnegativeInverse_exp [Nonempty ι] {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : Surrounds (weight k) (planeVector p.1 p.2)) :
    nonnegativeInverse k a p=expRadius (inverse (weight k) a (planeVector p.1 p.2)) := by
  apply nonnegativeInverse_eq_of_moment ha h0 he0 he1
    ⟨(Real.exp_pos _).le,(Real.exp_pos _).le⟩
  have he := moment_expRadius k a (inverse (weight k) a (planeVector p.1 p.2))
  rw [inverse_spec ha hp] at he
  exact Prod.ext (congrArg (fun z : MomentPlane => z 0) he)
    (congrArg (fun z : MomentPlane => z 1) he)

theorem nonnegativeInverse_interior_contDiffAt [Nonempty ι] {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : Surrounds (weight k) (planeVector p.1 p.2)) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => nonnegativeInverse k q.1 q.2) (a,p) := by
  have hmap : ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,planeVector q.2.1 q.2.2)) :=
    contDiff_fst.prodMk (planeVector_contDiff.comp contDiff_snd)
  have hs := expRadius_contDiff.contDiffAt.comp (a,p)
    ((inverse_contDiffAt ha hp).comp (a,p) hmap.contDiffAt)
  apply hs.congr_of_eventuallyEq
  have hae : ∀ᶠ q : (ι → ℝ) × Plane in 𝓝 (a,p),∀ i,0<q.1 i :=
    (positiveCoefficients_isOpen.preimage continuous_fst).mem_nhds ha
  have hpe : ∀ᶠ q : (ι → ℝ) × Plane in 𝓝 (a,p),Surrounds (weight k) (planeVector q.2.1 q.2.2) :=
    ((surrounds_isOpen (weight k)).preimage (planeVector_contDiff.continuous.comp continuous_snd)).mem_nhds hp
  filter_upwards [hae,hpe] with q hqa hqp
  exact nonnegativeInverse_exp hqa h0 he0 he1 hqp


end


open scoped BigOperators Topology ContDiff
open Set Filter Function

theorem trapezoid_inverse_coeff_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ContDiffAt ℝ ∞ (fun b : TrapezoidWeight A B → ℝ => nonnegativeInverse latticeIndex b p) a := by
  by_cases hb : p.1=0 ∨ p.2=0
  · let r := nonnegativeInverse (latticeIndex (A:=A) (B:=B)) a p
    have hr := nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a p
    have he : moment latticeIndex a r=p := trapezoid_inverse_spec hAB ha hp
    have hz := moment_zero_coordinates ha (lattice_zero A B) (lattice_unit_fst hA hAB)
      (lattice_unit_snd hA hAB) hr
    have hbr : r.1=0 ∨ r.2=0 := by
      rw [he] at hz
      exact hb.elim (fun h => Or.inl (hz.1.mp h)) (fun h => Or.inr (hz.2.mp h))
    have hs := boundary_inverse_coeff_contDiffAt ha (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) hr hbr
    rwa [he] at hs
  · have hp0 : 0<p.1 := lt_of_le_of_ne hp.1 (Ne.symm (fun h => hb (Or.inl h)))
    have hp1 : 0<p.2 := lt_of_le_of_ne hp.2.2.1 (Ne.symm (fun h => hb (Or.inr h)))
    have hs : ContDiffAt ℝ ∞
        (fun q : (TrapezoidWeight A B → ℝ) × Plane => nonnegativeInverse latticeIndex q.1 q.2) (a,p) :=
      nonnegativeInverse_interior_contDiffAt ha (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
      (trapezoidWeight_surrounds hAB ⟨hp0,hp.2.1,hp1,hp.2.2.2⟩)
    have hmap : ContDiffAt ℝ ∞ (fun b : TrapezoidWeight A B → ℝ => (b,p)) a :=
      contDiffAt_id.prodMk contDiffAt_const
    have hc := hs.comp a hmap
    exact hc



end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_AnalyticBoundary
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι : Type*} [Fintype ι]

 theorem probability_weighted_le {q f : ι → ℝ} {M : ℝ}
    (hq : ∀ i,0≤q i) (hs : ∑ i,q i=1) (hf : ∀ i,f i≤M) :
    ∑ i,q i*f i≤M := by
  calc
    _≤∑ i,q i*M := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hq i))
    _=M := by rw [←Finset.sum_mul,hs,one_mul]

end

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι : Type*} [Fintype ι]

theorem probability_nonneg {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (i : ι) :
    0≤probability k a r i := div_nonneg (mul_nonneg (ha i).le (monomial_nonneg _ hr))
      (polynomial_pos ha h0 hr).le

theorem probability_sum {k : ι → ℕ × ℕ} {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) : ∑ i,probability k a r i=1 := by
  simp only [probability,← Finset.sum_div]
  exact div_self hP

theorem probability_contDiffAt (k : ι → ℕ × ℕ) {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) (i : ι) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => probability k q.1 q.2 i) (a,r) := by
  apply ContDiffAt.div _ (polynomial_contDiff k).contDiffAt hP
  dsimp [monomial]
  fun_prop

theorem selected_nonneg {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) (p : Plane) (i : ι) : 0 ≤ selected k a p i :=
  probability_nonneg ha h0 (nonnegativeInverse_nonneg _ _ _) i

theorem selected_sum {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) (p : Plane) : ∑ i,selected k a p i=1 :=
  probability_sum (polynomial_pos ha h0 (nonnegativeInverse_nonneg _ _ _)).ne'

end

theorem trapezoid_selected_coeff_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) (i : TrapezoidWeight A B) :
    ContDiffAt ℝ ∞ (fun b : TrapezoidWeight A B → ℝ => selected latticeIndex b p i) a := by
  have hi := trapezoid_inverse_coeff_contDiffAt hA hAB ha hp
  have hs := probability_contDiffAt latticeIndex
    (polynomial_pos ha (lattice_zero A B) (nonnegativeInverse_nonneg latticeIndex a p)).ne' i
  have hmap := contDiffAt_id.prodMk hi
  have hc := hs.comp a hmap
  exact hc

end PackingSufficiencySupport.FiniteMoment.Radial

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

variable {ι : Type*} [Fintype ι]

 theorem hopfPrimitive_smoothAt (c : ℝ) {z : PlanePhase ι} (hz : z≠0) :
    ContDiffAt ℝ ∞ (hopfPrimitive c) z := by
  exact (contDiffAt_const.div (contDiffAt_const.mul phaseSq_smooth.contDiffAt)
    (mul_ne_zero (by norm_num) (phaseSq_pos hz).ne')).smul (phaseArea (ι := ι)).contDiff.contDiffAt

 theorem hopfPrimitive_radial (c : ℝ) (z : PlanePhase ι) : hopfPrimitive c z z=0 := by
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,phaseArea_self,mul_zero]

 theorem hopfPrimitive_circle (c : ℝ) {z : PlanePhase ι} (hz : z≠0) :
    hopfPrimitive c z (phaseJ z)=c/2 := by
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,phaseArea_J_right,phaseSq]
  calc
    c/(2*phaseDot z z)*phaseDot z z=c/2*(phaseDot z z/phaseDot z z) := by ring
    _=c/2 := by rw [div_self (show phaseDot z z≠0 from (phaseSq_pos hz).ne'),mul_one]

theorem complexCartesian_complex_smul (ζ : ℂ) (z : ι → ℂ) :
    complexCartesian (ζ•z)=ζ.re•complexCartesian z+ζ.im•phaseJ (complexCartesian z) := by
  ext i <;> simp [complexCartesian_apply,Pi.smul_apply,Complex.mul_re,Complex.mul_im,phaseJ] <;> ring

theorem complexPairing_complex_smul (ζ : ℂ) (z v : ι → ℂ) :
    complexPairing (ζ•z) (ζ•v)=(Complex.normSq ζ : ℂ)*complexPairing z v := by
  simp only [complexPairing,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_mul,Complex.star_def,Complex.normSq_eq_conj_mul_self]
  ring

theorem complexCartesian_smul_area (ζ : ℂ) (z v : ι → ℂ) :
    phaseArea (complexCartesian (ζ•z)) (complexCartesian (ζ•v))=
      Complex.normSq ζ*phaseArea (complexCartesian z) (complexCartesian v) := by
  rw [←complexPairing_im,complexPairing_complex_smul,Complex.mul_im]
  simp [complexPairing_im]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem hopfPrimitive_complex_line (c : ℝ) {z : ι → ℂ} (hz : complexCartesian z≠0)
    (ζ : ℂ) : hopfPrimitive c (complexCartesian z) (complexCartesian (ζ•z))=(c/2)*ζ.im := by
  rw [complexCartesian_complex_smul]
  simp only [map_add,map_smul,hopfPrimitive_radial,hopfPrimitive_circle c hz,
    smul_eq_mul,mul_zero,zero_add]
  ring

 theorem hopfPrimitive_complex_scale (c : ℝ) {ζ : ℂ} (hζ : ζ≠0) {z : ι → ℂ}
    (hz : complexCartesian z≠0) (v : ι → ℂ) :
    hopfPrimitive c (complexCartesian (ζ•z)) (complexCartesian (ζ•v))=
      hopfPrimitive c (complexCartesian z) (complexCartesian v) := by
  have hn : Complex.normSq ζ≠0 := (Complex.normSq_pos.mpr hζ).ne'
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,
    complexCartesian_complex_smul_sq,complexCartesian_smul_area]
  field_simp [hn,(phaseSq_pos hz).ne']

 variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 theorem hopfPrimitive_variable_gauge {S : E → ℂ} {G : E → (ι → ℂ)} {x : E}
    (hS : DifferentiableAt ℝ S x) (hG : DifferentiableAt ℝ G x)
    (hSx : S x≠0) (hGx : complexCartesian (G x)≠0) (c : ℝ) (v : E) :
    hopfPrimitive c (complexCartesian (S x•G x))
      (fderiv ℝ (fun y => complexCartesian (S y•G y)) x v)=
    hopfPrimitive c (complexCartesian (G x))
      (fderiv ℝ (fun y => complexCartesian (G y)) x v)+
        c/(2*Complex.normSq (S x))*complexArea (S x) (fderiv ℝ S x v) := by
  have hdG := complexCartesian.hasFDerivAt.comp x hG.hasFDerivAt
  have hd := complexCartesian.hasFDerivAt.comp x (hS.hasFDerivAt.smul hG.hasFDerivAt)
  have hz' : complexCartesian (S x•G x)≠0 := by
    intro h
    have hs := complexCartesian_complex_smul_sq (S x) (G x)
    simp only [h,phaseSq,map_zero] at hs
    exact (mul_ne_zero ((Complex.normSq_pos.mpr hSx).ne') (phaseSq_pos hGx).ne') hs.symm
  have he : fderiv ℝ S x v•G x=(fderiv ℝ S x v/S x)•(S x•G x) := by
    rw [smul_smul,div_mul_cancel₀ _ hSx]
  rw [show fderiv ℝ (fun y => complexCartesian (S y•G y)) x=_ from hd.fderiv,
    show fderiv ℝ (fun y => complexCartesian (G y)) x=_ from hdG.fderiv]
  simp only [ContinuousLinearMap.comp_apply,add_apply,
    ContinuousLinearMap.smulRight_apply,smul_apply,map_add,ContinuousLinearEquiv.coe_coe]
  rw [hopfPrimitive_complex_scale c hSx hGx,he,hopfPrimitive_complex_line c hz',complex_div_im]
  ring

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

 theorem affineFSPrimitive_hopf_pullback {G : E → (ι → ℂ)} {x : E}
    (hG : DifferentiableAt ℝ G x) (c : ℝ) (v : E) :
    hopfPrimitive c (complexCartesian (complexAffineLift (G x)))
      (fderiv ℝ (fun y => complexCartesian (complexAffineLift (G y))) x v)=
    affineFSPrimitive c (complexCartesian (G x))
      (fderiv ℝ (fun y => complexCartesian (G y)) x v) := by
  have hL := complexAffineLift_smooth.differentiable (by simp) (G x)
  have hd := complexCartesian.hasFDerivAt.comp x (hL.hasFDerivAt.comp x hG.hasFDerivAt)
  have hd' := complexCartesian.hasFDerivAt.comp x hG.hasFDerivAt
  rw [show fderiv ℝ (fun y => complexCartesian (complexAffineLift (G y))) x=_ from hd.fderiv,
    show fderiv ℝ (fun y => complexCartesian (G y)) x=_ from hd'.fderiv]
  exact affineFSPrimitive_hopf c (G x) (fderiv ℝ G x v)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_CubicEndCoordinates
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 theorem endRegularRegion_open : IsOpen endRegularRegion := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  have hroot (j : Fin 2) : ContinuousAt
      (fun t => infinityRoot (parameters 0) zeroEnd t j+1) s :=
    ((contDiffAt_pi.mp (infinityRoot_contDiffAt _ zeroEnd hs.1) j).add
      contDiffAt_const).continuousAt
  have he : ∀ᶠ t in 𝓝 s, ∀ j : Fin 2,
      infinityRoot (parameters 0) zeroEnd t j+1≠0 := by
    apply Filter.eventually_all.mpr
    intro j
    exact (hroot j).eventually_ne (hs.2 j)
  filter_upwards [(infinityRegion_open _).mem_nhds hs.1,he] with t ht ht'
  exact ⟨ht,ht'⟩

 theorem endQuotient_contDiffAt (ε : EndIndex) {s : ℂ}
    (hs : s∈infinityDomain (parameters 0)) : ContDiffAt ℂ ∞ (endQuotient ε) s := by
  apply contDiffAt_pi.mpr
  intro j
  cases j with
  | none => exact ((contDiffAt_pi.mp (infinityRoot_contDiffAt _ ε hs.2) 0).sub
      contDiffAt_const).div contDiffAt_id hs.1
  | some _ => exact ((contDiffAt_pi.mp (infinityRoot_contDiffAt _ ε hs.2) 1).sub
      contDiffAt_const).div contDiffAt_id hs.1

 theorem removableCoordinate_eq {s : ℂ} (hs : s≠0) (hR : s∈endRegularRegion) (j : Fin 2) :
    (infinityRoot (parameters 0) zeroEnd s j-1)/s=removableCoordinate s j := by
  have hq := infinityRoot_sq (parameters 0) zeroEnd s j
  dsimp [removableCoordinate]
  apply (div_eq_div_iff hs (hR.2 j)).mpr
  linear_combination hq

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

theorem complexCartesian_affineComplex (z : Affine m) :
    complexCartesian (affineComplex m z)=affinePhase m z := by
  ext i <;> cases i <;> rfl

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 theorem five_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b c d e : E → ℂ} {x : E} (ha : ContDiffAt ℂ ∞ a x) (hb : ContDiffAt ℂ ∞ b x)
    (hc : ContDiffAt ℂ ∞ c x) (hd : ContDiffAt ℂ ∞ d x) (he : ContDiffAt ℂ ∞ e x) :
    ContDiffAt ℂ ∞ (fun y => five (a y) (b y) (c y) (d y) (e y)) x := by
  apply contDiffAt_pi.mpr
  intro j
  cases j with
  | none => exact ha
  | some j =>
    cases j with
    | none => exact hb
    | some j =>
      fin_cases j
      · exact hc
      · exact hd
      · exact he

 theorem endCoefficient_contDiffAt {s : ℂ} (hs : s∈endRegularRegion) (j : Fin 2) :
    ContDiffAt ℂ ∞ (fun t => endCoefficient t j) s :=
  contDiffAt_const.div
    ((contDiffAt_pi.mp (infinityRoot_contDiffAt _ zeroEnd hs.1) j).add contDiffAt_const) (hs.2 j)

 theorem endNumerator_contDiffAt (ε : EndIndex) {s : ℂ} (hs : s∈endRegularRegion) (j : Fin 2) :
    ContDiffAt ℂ ∞ (fun t => endNumerator ε t j) s :=
  (contDiffAt_pi.mp (infinityRoot_contDiffAt _ ε hs.1) j).sub contDiffAt_const

 theorem complexAffineLift_holomorphic {ι : Type*} [Fintype ι] :
    ContDiff ℂ ∞ (complexAffineLift (ι := ι)) := by
  apply contDiff_pi.mpr
  intro j
  cases j with
  | none => exact contDiff_const
  | some j => exact contDiff_apply ℂ ℂ j

 theorem weightedEndRegular_contDiffAt (D m : ℕ) (ε : EndIndex) {s : ℂ} (hs : s∈endRegularRegion) :
    ContDiffAt ℂ ∞ (weightedEndRegular D m ε) s := by
  change ContDiffAt ℂ ∞ (fun t => weightedEndRegular D m ε t) s
  have hp (n : ℕ) := (contDiffAt_id (𝕜 := ℂ) (x := s) (n := ∞)).pow n
  have hA := endNumerator_contDiffAt ε hs
  have hC := endCoefficient_contDiffAt hs
  cases h0 : ε 0 <;> cases h1 : ε 1
  · simp only [weightedEndRegular,h0,h1,Bool.false_eq_true,↓reduceIte]
    exact complexAffineLift_holomorphic.contDiffAt.comp s ((affineComplex 3).contDiff.contDiffAt.comp s
      ((weightedProjection_contDiff D m).contDiffAt.comp s
        ((contDiffAt_id.mul (hC 0)).prodMk (contDiffAt_id.mul (hC 1)))))
  · simp only [weightedEndRegular,h0,h1,Bool.false_eq_true,↓reduceIte]
    exact five_contDiffAt (hp _) ((hp _).mul ((hC 0).pow _)) ((hA 1).pow _)
      (((hp _).mul ((hC 0).pow _)).mul ((hA 1).pow _))
      (((hp _).mul ((hC 0).pow _)).mul ((hA 1).pow _))
  · simp only [weightedEndRegular,h0,h1,Bool.false_eq_true,↓reduceIte]
    exact five_contDiffAt (hp _) ((hA 0).pow _) ((hp _).mul ((hC 1).pow _))
      (((hp _).mul ((hA 0).pow _)).mul ((hC 1).pow _))
      (((hp _).mul ((hA 0).pow _)).mul ((hC 1).pow _))
  · simp only [weightedEndRegular,h0,h1,↓reduceIte]
    exact five_contDiffAt (hp _) ((hp _).mul ((hA 0).pow _)) ((hp _).mul ((hA 1).pow _))
      (((hA 0).pow _).mul ((hA 1).pow _)) (((hA 0).pow _).mul ((hA 1).pow _))

 theorem endCoordinate_false {ε : EndIndex} {j : Fin 2} (hj : ε j=false)
    {s : ℂ} (hs : s≠0) (hR : s∈endRegularRegion) :
    (infinityRoot (parameters 0) ε s j-1)/s=s*endCoefficient s j := by
  have he : infinityRoot (parameters 0) ε s j=infinityRoot (parameters 0) zeroEnd s j := by
    simp only [infinityRoot,endSign,hj,zeroEnd]
    rfl
  rw [he,removableCoordinate_eq hs hR]
  dsimp [removableCoordinate,endCoefficient]
  ring

 theorem weightedEndQuotient_contDiffAt (D m : ℕ) (ε : EndIndex) {s : ℂ}
    (hs : s∈infinityDomain (parameters 0)) : ContDiffAt ℂ ∞ (weightedEndQuotient D m ε) s :=
  (affineComplex 3).contDiff.contDiffAt.comp s ((weightedProjection_contDiff D m).contDiffAt.comp s
    ((contDiffAt_pi.mp (endQuotient_contDiffAt ε hs) none).prodMk
      (contDiffAt_pi.mp (endQuotient_contDiffAt ε hs) (some 0))))

 theorem weightedEndRegular_none (D m : ℕ) (ε : EndIndex) (s : ℂ) :
    weightedEndRegular D m ε s none=s^(weightedEndOrder D m ε) := by
  cases h0 : ε 0 <;> cases h1 : ε 1 <;>
    simp [weightedEndRegular,weightedEndOrder,h0,h1,five]

 theorem weightedEndRegular_ne_zero (D m : ℕ) (ε : EndIndex) (s : ℂ) :
    weightedEndRegular D m ε s≠0 := by
  intro he
  by_cases hs : s=0
  · subst s
    cases h0 : ε 0 <;> cases h1 : ε 1
    · exact (one_ne_zero : (1:ℂ)≠0) (by simpa [weightedEndRegular,h0,h1,complexAffineLift] using congrFun he none)
    · have hz := congrFun he (some (some 0))
      norm_num [weightedEndRegular,h0,h1,five,endNumerator,infinityRoot,endSign] at hz
    · have hz := congrFun he (some none)
      norm_num [weightedEndRegular,h0,h1,five,endNumerator,infinityRoot,endSign] at hz
    · have hz := congrFun he (some (some 1))
      norm_num [weightedEndRegular,h0,h1,five,endNumerator,infinityRoot,endSign] at hz
  · exact (pow_ne_zero _ hs) (by simpa only [weightedEndRegular_none,Pi.zero_apply] using congrFun he none)

 theorem weightedEndRegular_cartesian_ne_zero (D m : ℕ) (ε : EndIndex) (s : ℂ) :
    complexCartesian (weightedEndRegular D m ε s)≠0 := by
  intro h
  exact weightedEndRegular_ne_zero D m ε s (complexCartesian.injective (by simpa only [map_zero] using h))

 theorem scale_div_pow {s : ℂ} (hs : s≠0) (a : ℂ) (L : ℕ) :
    s^L*(a/s)^L=a^L := by
  rw [←mul_pow,mul_div_cancel₀ a hs]

 theorem scale_complement_pow {s : ℂ} (hs : s≠0) (a : ℂ) {D m : ℕ} (hm : m≤D) :
    s^D*(a/s)^(D-m)=s^m*a^(D-m) := by
  have hD : m+(D-m)=D := Nat.add_sub_of_le hm
  have hp : s^D=s^m*s^(D-m) := by rw [←pow_add,hD]
  calc
    _=s^m*(s^(D-m)*(a/s)^(D-m)) := by rw [hp]; ring
    _=_ := by rw [scale_div_pow hs]

 theorem scale_div_mixed {s : ℂ} (hs : s≠0) (a b : ℂ) (L m : ℕ) :
    s^(L+m)*((a/s)^L*(b/s)^m)=a^L*b^m := by
  calc
    _=(s^L*(a/s)^L)*(s^m*(b/s)^m) := by rw [pow_add]; ring
    _=_ := by rw [scale_div_pow hs,scale_div_pow hs]

 theorem scale_regular_pow (s b : ℂ) (L : ℕ) :
    s^L*(s*b)^L=s^(2*L)*b^L := by
  rw [mul_pow,two_mul,pow_add]
  ring

 theorem scale_onepole_mixed {s : ℂ} (hs : s≠0) (a b : ℂ) (L m : ℕ) :
    s^L*((a/s)^L*(s*b)^m)=s^m*a^L*b^m := by
  calc
    _=(s^L*(a/s)^L)*(s^m*b^m) := by rw [mul_pow]; ring
    _=_ := by rw [scale_div_pow hs]; ring

 theorem scale_onepole_cross {s : ℂ} (hs : s≠0) (a b : ℂ) {L m : ℕ} (hm : m≤2*L) :
    s^L*((a/s)^m*(s*b)^L)=s^(2*L-m)*a^m*b^L := by
  rw [pow_sub₀ s hs hm,two_mul,pow_add,div_pow,mul_pow]
  simp only [div_eq_mul_inv]
  ring

 theorem weightedLift_scale_poles {D m : ℕ} (hm : m≤D) {s : ℂ} (hs : s≠0) (a b : ℂ) :
    s^D • weightedLift D m (a/s) (b/s)=
      five (s^D) (s^m*a^(D-m)) (s^m*b^(D-m)) (a^(D-m)*b^m) (a^m*b^(D-m)) := by
  funext j
  cases j with
  | none => change s^D*1=s^D; exact mul_one _
  | some j =>
    cases j with
    | none => exact scale_complement_pow hs a hm
    | some j =>
      fin_cases j
      · exact scale_complement_pow hs b hm
      · change s^D*((a/s)^(D-m)*(b/s)^m)=a^(D-m)*b^m
        simpa only [Nat.sub_add_cancel hm] using scale_div_mixed hs a b (D-m) m
      · change s^D*((a/s)^m*(b/s)^(D-m))=a^m*b^(D-m)
        simpa only [Nat.add_sub_of_le hm] using scale_div_mixed hs a b m (D-m)

 theorem weightedLift_scale_left {D m : ℕ} (hm : m≤2*(D-m)) {s : ℂ} (hs : s≠0) (a b : ℂ) :
    s^(D-m) • weightedLift D m (a/s) (s*b)=
      five (s^(D-m)) (a^(D-m)) (s^(2*(D-m))*b^(D-m))
        (s^m*a^(D-m)*b^m) (s^(2*(D-m)-m)*a^m*b^(D-m)) := by
  funext j
  cases j with
  | none => change s^(D-m)*1=s^(D-m); exact mul_one _
  | some j =>
    cases j with
    | none => exact scale_div_pow hs a (D-m)
    | some j =>
      fin_cases j
      · exact scale_regular_pow s b (D-m)
      · exact scale_onepole_mixed hs a b (D-m) m
      · exact scale_onepole_cross hs a b hm

 theorem weightedLift_scale_right {D m : ℕ} (hm : m≤2*(D-m)) {s : ℂ} (hs : s≠0) (a b : ℂ) :
    s^(D-m) • weightedLift D m (s*a) (b/s)=
      five (s^(D-m)) (s^(2*(D-m))*a^(D-m)) (b^(D-m))
        (s^(2*(D-m)-m)*a^(D-m)*b^m) (s^m*a^m*b^(D-m)) := by
  funext j
  cases j with
  | none => change s^(D-m)*1=s^(D-m); exact mul_one _
  | some j =>
    cases j with
    | none => exact scale_regular_pow s a (D-m)
    | some j =>
      fin_cases j
      · exact scale_div_pow hs b (D-m)
      · change s^(D-m)*((s*a)^(D-m)*(b/s)^m)=s^(2*(D-m)-m)*a^(D-m)*b^m
        calc
          _=s^(D-m)*((b/s)^m*(s*a)^(D-m)) := by ring
          _=s^(2*(D-m)-m)*b^m*a^(D-m) := scale_onepole_cross hs b a hm
          _=_ := by ring
      · change s^(D-m)*((s*a)^m*(b/s)^(D-m))=s^m*a^m*b^(D-m)
        calc
          _=s^(D-m)*((b/s)^(D-m)*(s*a)^m) := by ring
          _=s^m*b^(D-m)*a^m := scale_onepole_mixed hs b a (D-m) m
          _=_ := by ring

 theorem weightedEndRegular_scale {D m : ℕ} (hm : m≤D) (h2 : m≤2*(D-m))
    (ε : EndIndex) {s : ℂ} (hs : s≠0) (hR : s∈endRegularRegion) :
    weightedEndRegular D m ε s=s^(weightedEndOrder D m ε)•complexAffineLift (weightedEndQuotient D m ε s) := by
  cases h0 : ε 0 <;> cases h1 : ε 1
  · have h00 := endCoordinate_false h0 hs hR
    have h11 := endCoordinate_false h1 hs hR
    simp only [weightedEndRegular,weightedEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,
      weightedEndQuotient,endQuotient,h00,h11,pow_zero,one_smul]
  · have h00 := endCoordinate_false h0 hs hR
    simpa only [weightedEndRegular,weightedEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,
      weightedEndQuotient,endQuotient,h00,weightedLift,endNumerator] using
      (weightedLift_scale_right h2 hs (endCoefficient s 0) (endNumerator ε s 1)).symm
  · have h11 := endCoordinate_false h1 hs hR
    simpa only [weightedEndRegular,weightedEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,
      weightedEndQuotient,endQuotient,h11,weightedLift,endNumerator] using
      (weightedLift_scale_left h2 hs (endNumerator ε s 0) (endCoefficient s 1)).symm
  · simpa only [weightedEndRegular,weightedEndOrder,h0,h1,↓reduceIte,
      weightedEndQuotient,endQuotient,weightedLift,endNumerator] using
      (weightedLift_scale_poles hm hs (endNumerator ε s 0) (endNumerator ε s 1)).symm

 theorem weightedEndQuotient_phase (D m : ℕ) (ε : EndIndex) (s : ℂ) :
    complexCartesian (weightedEndQuotient D m ε s)=
      affinePhase 3 (weightedProjection D m (projection (infinityPoint (parameters 0) ε s))) := by
  rw [weightedEndQuotient,complexCartesian_affineComplex]
  congr 2
  apply Prod.ext
  · change (infinityRoot (parameters 0) ε s 0-1)/s=s⁻¹*infinityRoot (parameters 0) ε s 0-s⁻¹
    simp only [div_eq_mul_inv]
    ring
  · change (infinityRoot (parameters 0) ε s 1-1)/s=s⁻¹*infinityRoot (parameters 0) ε s 1-s⁻¹
    simp only [div_eq_mul_inv]
    ring

 theorem weighted_infinityPhase_germ (D m : ℕ) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source) :
    (weightedPhaseInclusion D m ∘ infinityDiffeomorph (parameters 0) ε)=ᶠ[𝓝 y]
      fun z => complexCartesian (weightedEndQuotient D m ε (Complex.equivRealProdCLM.symm z)) := by
  filter_upwards [(infinityDiffeomorph (parameters 0) ε).open_source.mem_nhds hy] with z hz
  have hzD : Complex.equivRealProdCLM.symm z∈infinityDomain (parameters 0) := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hz
  rw [weightedEndQuotient_phase]
  change affinePhase 3 (weightedProjection D m (projection ((infinityInverse (parameters 0) ε
    (Complex.equivRealProdCLM.symm z)).val)))=_
  rw [infinityInverse_val _ ε hzD.1]

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open DiagonalQuadrics

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem logarithmicDerivative_pow {S : E → ℂ} {x : E} (hS : DifferentiableAt ℝ S x)
    (hSx : S x≠0) (l : ℕ) (v : E) :
    fderiv ℝ (fun y => S y^l) x v/(S x)^l=(l:ℂ)*(fderiv ℝ S x v/S x) := by
  rw [(hS.hasFDerivAt.pow l).fderiv]
  cases l with
  | zero => simp
  | succ l =>
    simp only [Nat.succ_sub_one,smul_apply,nsmul_eq_mul,smul_eq_mul,pow_succ]
    field_simp

 theorem hopfPrimitive_variable_power_gauge {S : E → ℂ} {G : E → (ι → ℂ)} {x : E}
    (hS : DifferentiableAt ℝ S x) (hG : DifferentiableAt ℝ G x)
    (hSx : S x≠0) (hGx : complexCartesian (G x)≠0) (l : ℕ) (c : ℝ) (v : E) :
    hopfPrimitive c (complexCartesian (S x^l•G x))
      (fderiv ℝ (fun y => complexCartesian (S y^l•G y)) x v)=
    hopfPrimitive c (complexCartesian (G x))
      (fderiv ℝ (fun y => complexCartesian (G y)) x v)+
        (l:ℝ)*c/(2*Complex.normSq (S x))*complexArea (S x) (fderiv ℝ S x v) := by
  rw [hopfPrimitive_variable_gauge (S := fun y => S y^l) (hS.pow l) hG (pow_ne_zero l hSx) hGx c v]
  congr 1
  have hd := congrArg Complex.im (logarithmicDerivative_pow hS hSx l v)
  rw [complex_div_im] at hd
  simp only [Complex.mul_im,Complex.natCast_re,Complex.natCast_im,zero_mul,add_zero,
    complex_div_im] at hd
  calc
    _=c/2*(complexArea (S x^l) (fderiv ℝ (fun y => S y^l) x v)/Complex.normSq (S x^l)) := by ring
    _=c/2*((l:ℝ)*(complexArea (S x) (fderiv ℝ S x v)/Complex.normSq (S x))) := by rw [hd]
    _=_ := by ring

 theorem planar_power_gauge {G : Plane → (ι → ℂ)} {y : Plane}
    (hG : DifferentiableAt ℝ G y) (hy : Complex.equivRealProdCLM.symm y≠0)
    (hGy : complexCartesian (G y)≠0) (l : ℕ) (c : ℝ) (v : Plane) :
    hopfPrimitive c (complexCartesian ((Complex.equivRealProdCLM.symm y)^l•G y))
      (fderiv ℝ (fun z => complexCartesian ((Complex.equivRealProdCLM.symm z)^l•G z)) y v)=
    hopfPrimitive c (complexCartesian (G y))
      (fderiv ℝ (fun z => complexCartesian (G z)) y v)+
        ((l:ℝ)*c/2)*angularOneForm y v := by
  rw [hopfPrimitive_variable_power_gauge Complex.equivRealProdCLM.symm.differentiableAt
    hG hy hGy l c v,ContinuousLinearEquiv.fderiv]
  simp only [ContinuousLinearEquiv.coe_coe]
  have hns : Complex.normSq (Complex.equivRealProdCLM.symm y)=radiusSq y := by
    change y.1*y.1+y.2*y.2=y.1^2+y.2^2
    ring
  have hca : complexArea (Complex.equivRealProdCLM.symm y)
      (Complex.equivRealProdCLM.symm v)=planarArea y v := by
    rw [complexArea_apply]
    rfl
  rw [hns,hca]
  simp only [angularOneForm,smul_apply,smul_eq_mul]
  ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 theorem weightedRegularEndPhase_contDiffAt (D m : ℕ) (ε : EndIndex) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    ContDiffAt ℝ ∞ (weightedRegularEndPhase D m ε) y :=
  (complexCartesian (ι := WeightedHomogeneousIndex)).contDiff.contDiffAt.comp y
    (((weightedEndRegular_contDiffAt D m ε hy).restrict_scalars ℝ).comp y
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt)

 theorem weightedRegularEndPrimitive_contDiffAt (D m : ℕ) (ε : EndIndex) (c : ℝ) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    ContDiffAt ℝ ∞ (weightedRegularEndPrimitive D m ε c) y :=
  staticPullbackOneForm_smoothAt
    (hopfPrimitive_smoothAt c (weightedEndRegular_cartesian_ne_zero D m ε _))
    (weightedRegularEndPhase_contDiffAt D m ε hy)

 theorem weightedEndQuotientPrimitive_residue {D m : ℕ} (hm : m≤D) (h2 : m≤2*(D-m))
    (ε : EndIndex) (c : ℝ) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈endRegularRegion)
    (h0 : Complex.equivRealProdCLM.symm y≠0) (v : Plane) :
    affineFSPrimitive c (complexCartesian (weightedEndQuotient D m ε (Complex.equivRealProdCLM.symm y)))
      (fderiv ℝ (fun z : Plane => complexCartesian
        (weightedEndQuotient D m ε (Complex.equivRealProdCLM.symm z))) y v)=
      weightedRegularEndPrimitive D m ε c y v-(weightedEndResidue D m ε c/2)*angularOneForm y v := by
  let Q : Plane → WeightedAffineIndex → ℂ := fun z => weightedEndQuotient D m ε (Complex.equivRealProdCLM.symm z)
  have hQ : DifferentiableAt ℝ Q y :=
    (((weightedEndQuotient_contDiffAt D m ε ⟨h0,hy.1⟩).restrict_scalars ℝ).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp y
      Complex.equivRealProdCLM.symm.differentiableAt
  have hp := affineFSPrimitive_hopf_pullback hQ c v
  have hN : complexCartesian (complexAffineLift (Q y))≠0 := by
    intro hz
    have hf : complexAffineLift (Q y)=0 := by
      apply (complexCartesian (ι := WeightedHomogeneousIndex)).injective
      simpa only [map_zero] using hz
    exact one_ne_zero (congrFun hf none)
  have he : weightedRegularEndPhase D m ε=ᶠ[𝓝 y] fun z => complexCartesian
      ((Complex.equivRealProdCLM.symm z)^(weightedEndOrder D m ε)•complexAffineLift (Q z)) := by
    have hR := endRegularRegion_open.preimage Complex.equivRealProdCLM.symm.continuous
    filter_upwards [(isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).mem_nhds h0,
      hR.mem_nhds hy] with z hz hzR
    exact congrArg complexCartesian (weightedEndRegular_scale hm h2 ε hz hzR)
  have hG : DifferentiableAt ℝ (fun z => complexAffineLift (Q z)) y :=
    (complexAffineLift_smooth.differentiable (by simp) _).comp y hQ
  have hg := planar_power_gauge hG h0 hN (weightedEndOrder D m ε) c v
  change _=hopfPrimitive c (weightedRegularEndPhase D m ε y) (fderiv ℝ (weightedRegularEndPhase D m ε) y v)-_
  rw [he.eq_of_nhds,he.fderiv_eq,hg,hp]
  dsimp [weightedEndResidue]
  ring

 theorem weightedFSPrimitive_infinity {D m : ℕ} (hm : m≤D) (h2 : m≤2*(D-m))
    (ε : EndIndex) (c : ℝ) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    euclideanPullbackOneForm (fun _ => weightedFSPrimitive D m c)
      (infinityDiffeomorph (parameters 0) ε) (0,y)=
      weightedRegularEndPrimitive D m ε c y-(weightedEndResidue D m ε c/2) • angularOneForm y := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain (parameters 0) := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hg := weighted_infinityPhase_germ D m ε hy
  change euclideanPullbackOneForm (fun _ => manifoldPullbackOneForm
    (fun _ => affineFSPrimitive c) (weightedPhaseInclusion D m) 0) (infinityDiffeomorph (parameters 0) ε) (0,y)=_
  rw [euclideanPullbackOneForm_comp ((weightedPhaseInclusion_smooth D m).mdifferentiable (by simp) _)
    ((infinityDiffeomorph (parameters 0) ε).mdifferentiableAt (by simp) hy)]
  apply ContinuousLinearMap.ext
  intro v
  change affineFSPrimitive c ((weightedPhaseInclusion D m ∘ infinityDiffeomorph (parameters 0) ε) y)
    (manifoldMapDifferential (E := PlanePhase WeightedAffineIndex) (F := Plane)
      (weightedPhaseInclusion D m ∘ infinityDiffeomorph (parameters 0) ε) y v)=_
  rw [manifoldMapDifferential,mfderiv_eq_fderiv,hg.eq_of_nhds,hg.fderiv_eq]
  exact weightedEndQuotientPrimitive_residue hm h2 ε c hR hD.1 v

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
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

section FormOperations
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem SmoothOneFormFamily.zero :
    SmoothOneFormFamily (fun _ : P => (0 : ManifoldOneForm E M)) := by
  intro c
  simpa only [chartOneForm_zero] using
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : P × E => (0 : E →L[ℝ] ℝ)) _)

theorem SmoothOneFormFamily.sum {I : Type*} (s : Finset I)
    {α : I → P → ManifoldOneForm E M} (hα : ∀ i ∈ s, SmoothOneFormFamily (α i)) :
    SmoothOneFormFamily (fun p => ∑ i ∈ s, α i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using SmoothOneFormFamily.zero (P := P)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hα i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hα j (Finset.mem_insert_of_mem hj)))

end FormOperations

end
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem familySpatialExterior_smoothAt {Γ : P × E → E →L[ℝ] ℝ}
    {p : P × E} (hΓ : ContDiffAt ℝ ∞ Γ p) : ContDiffAt ℝ ∞ (familySpatialExterior Γ) p := by
  have hd : ContDiffAt ℝ ∞ (fun q => (fderiv ℝ Γ q).comp (ContinuousLinearMap.inr ℝ P E)) p :=
    (hΓ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiffAt_const
  have hflip : ContDiff ℝ ∞ (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ)
  exact hd.sub (hflip.contDiffAt.comp p hd)

 theorem familySpatialExterior_eq_slice {Γ : P × E → E →L[ℝ] ℝ}
    {p : P × E} (hΓ : DifferentiableAt ℝ Γ p) :
    familySpatialExterior Γ p=euclideanExteriorOneForm (fun x => Γ (p.1,x)) p.2 := by
  have hi : HasFDerivAt (fun y : E => (p.1,y))
      ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hh : HasFDerivAt Γ (fderiv ℝ Γ p) (p.1,p.2) := hΓ.hasFDerivAt
  have hs := (hh.comp p.2 hi).fderiv
  change fderiv ℝ (fun y => Γ (p.1,y)) p.2 = _ at hs
  unfold familySpatialExterior euclideanExteriorOneForm
  rw [hs]
  rfl

 theorem manifoldExteriorOneForm_family_smooth {Γ : P → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) : SmoothTwoFormFamily (fun p => manifoldExteriorOneForm (Γ p)) := by
  intro c p hp
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hp
  apply ((familySpatialExterior_smoothAt ((hΓ c).contDiffAt hn)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with q hq
  rw [manifoldExteriorOneForm_chart (fun b y hy => (hΓ.spatial_smooth q.1 b hy).contDiffWithinAt) hq.2]
  exact (familySpatialExterior_eq_slice (((hΓ c).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).symm

end
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

 omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem chartOneForm_spatial_smul (ρ : M → ℝ) (α : ManifoldOneForm E M) (c : M) (y : E) :
    chartOneForm (fun x => ρ x • α x) c y=
      ρ ((extChartAt 𝓘(ℝ,E) c).symm y) • chartOneForm α c y := by
  ext u
  rfl

 theorem SmoothOneFormFamily.spatial_smul [IsManifold 𝓘(ℝ,E) ∞ M]
    {α : P → ManifoldOneForm E M} (hα : SmoothOneFormFamily α) {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ ρ) :
    SmoothOneFormFamily (fun p x => ρ x • α p x) := by
  intro c q hq
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hq.2)
  have hrs := (hρ.contMDiffAt.comp q.2 hi).contDiffAt.comp q contDiffAt_snd
  have hfs := (hα c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds hq)
  simpa only [chartOneForm_spatial_smul,Pi.smul_def',Function.comp_apply] using (hrs.smul hfs).contDiffWithinAt

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

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

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem coefficientNorm_pos (D m : ℕ) (x : BaseCurve) : 0 < coefficientNorm D m x := by
  dsimp [coefficientNorm]
  linarith [phaseSq_nonneg (weightedPhaseInclusion D m x)]

 theorem coefficientNorm_smooth (D m : ℕ) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (coefficientNorm D m) :=
  contMDiff_const.add (phaseSq_smooth.contMDiff.comp (weightedPhaseInclusion_smooth D m))

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicCoefficientDifferential
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι]

theorem radialProbability_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) (i : TrapezoidWeight A B) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (fun x => radialProbability Radial.latticeIndex D m p x i) := by
  have ha : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,TrapezoidWeight A B → ℝ) ∞
      (fun x : BaseCurve => fun j => coefficientNorm (D j) (m j) x) :=
    contMDiff_pi_space.mpr (fun j => coefficientNorm_smooth _ _)
  intro x
  have hs := Radial.trapezoid_selected_coeff_contDiffAt hA hAB
    (fun j => coefficientNorm_pos (D j) (m j) x) hp i
  have hc := hs.contMDiffAt.comp x ha.contMDiffAt
  exact hc

theorem radialPrimitive_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) (c : ℝ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) :
    SmoothOneFormFamily (fun _ : ℝ => radialPrimitive Radial.latticeIndex D m c p) := by
  have hs := SmoothOneFormFamily.sum Finset.univ (fun i _ =>
    (weightedFSPrimitive_smooth (D i) (m i) c).spatial_smul (radialProbability_smooth hA hAB D m hp i))
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext t x
  simp only [radialPrimitive,Finset.sum_apply]

theorem radialForm_smooth {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) (c : ℝ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) : SmoothTwoForm (radialForm Radial.latticeIndex D m c p) :=
  (manifoldExteriorOneForm_family_smooth (radialPrimitive_smooth hA hAB D m c hp)).eval 0

theorem radialForm_skew (k : ι → ℕ × ℕ) (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane)
    (x : BaseCurve) (v u : RealModel) : radialForm k D m c p x v u= -radialForm k D m c p x u v :=
  manifoldExteriorOneForm_skew _ _ _ _

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialFamilyExtension
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold Filter

theorem radialAnnulus_compact (r R : ℝ) : IsCompact (radialAnnulus r R) := by
  have hc : IsClosed (radialAnnulus r R) :=
    (isClosed_le continuous_const radiusSq_smooth.continuous).inter
      (isClosed_le radiusSq_smooth.continuous continuous_const)
  apply ((isCompact_Icc : IsCompact (Icc (-(|R|+1)) (|R|+1))).prod
    (isCompact_Icc : IsCompact (Icc (-(|R|+1)) (|R|+1)))).of_isClosed_subset hc
  intro z hz
  have hb : z.1^2+z.2^2≤|R| := hz.2.trans (le_abs_self R)
  constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2,abs_nonneg R]

theorem radialAnnulus_ne_zero {r R : ℝ} (hr : 0 < r) {z : Plane}
    (hz : z∈radialAnnulus r R) : z≠0 := by
  intro h
  subst z
  have : r≤0 := by simpa [radiusSq] using hz.1
  linarith

theorem radiusSq_complex (z : Plane) : Complex.normSq (Complex.equivRealProdCLM.symm z)=radiusSq z := by
  change z.1*z.1+z.2*z.2=z.1^2+z.2^2
  ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι]

 theorem regularCoefficientNorm_pos (D m : ℕ) (ε : EndIndex) (y : Plane) :
    0 < regularCoefficientNorm D m ε y := phaseSq_pos (weightedEndRegular_cartesian_ne_zero D m ε _)

 theorem regularCoefficientNorm_contDiffAt (D m : ℕ) (ε : EndIndex) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    ContDiffAt ℝ ∞ (regularCoefficientNorm D m ε) y :=
  phaseSq_smooth.contDiffAt.comp y (weightedRegularEndPhase_contDiffAt D m ε hy)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold

 theorem totalWeight_le {A B : ℕ} (k : TrapezoidWeight A B) : totalWeight k≤B := k.property.2

 theorem cubicMarked_lt_degree {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    (k : TrapezoidWeight A B) : cubicMarkedOrder S k < cubicDegree D k := by
  have hk := totalWeight_le k
  dsimp [cubicMarkedOrder,cubicDegree]
  omega

 theorem cubicMarked_twice_complement {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    (k : TrapezoidWeight A B) : cubicMarkedOrder S k≤2*(cubicDegree D k-cubicMarkedOrder S k) := by
  have hk := totalWeight_le k
  dsimp [cubicMarkedOrder,cubicDegree]
  omega

variable {ι : Type*} [Fintype ι]

 theorem radialPrimitive_infinity (w : ι → ℕ × ℕ) {D m : ι → ℕ}
    (hm : ∀ i,m i≤D i) (h2 : ∀ i,m i≤2*(D i-m i)) (c : ℝ) (p : Radial.Plane)
    (ε : EndIndex) {y : Plane} (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    euclideanPullbackOneForm (fun _ => radialPrimitive w D m c p)
      (infinityDiffeomorph (parameters 0) ε) (0,y)=
      radialEndRegularPrimitive w D m c p ε y-(radialEndResidue w D m c p ε y/2) • angularOneForm y := by
  have he : euclideanPullbackOneForm (fun _ => radialPrimitive w D m c p)
      (infinityDiffeomorph (parameters 0) ε) (0,y)=
      ∑ i,radialEndProbability w D m p ε y i •
        euclideanPullbackOneForm (fun _ => weightedFSPrimitive (D i) (m i) c)
          (infinityDiffeomorph (parameters 0) ε) (0,y) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sum_apply, smul_apply, smul_eq_mul, radialEndProbability]
    let A : Plane →L[ℝ] RealModel :=
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,RealModel) (infinityDiffeomorph (parameters 0) ε) y
    let z : RealModel := A v
    change (∑ i,radialProbability w D m p (infinityDiffeomorph (parameters 0) ε y) i •
        weightedFSPrimitive (D i) (m i) c (infinityDiffeomorph (parameters 0) ε y)) z =
      ∑ i,radialProbability w D m p (infinityDiffeomorph (parameters 0) ε y) i *
        weightedFSPrimitive (D i) (m i) c (infinityDiffeomorph (parameters 0) ε y) z
    simp only [sum_apply,smul_apply,smul_eq_mul]
  rw [he]
  simp_rw [weightedFSPrimitive_infinity (hm _) (h2 _) ε c hy hR]
  apply ContinuousLinearMap.ext
  intro v
  simp only [radialEndRegularPrimitive,radialEndResidue,sum_apply,
    sub_apply,smul_apply,smul_eq_mul,Finset.sum_mul,Finset.sum_div,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricEndAnnuli
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian
variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem radialAnnulus_in_end {r R : ℝ} (hr : 0 < r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) (ε : Fin m → Bool) :
    radialAnnulus r R⊆(infinityDiffeomorph a ε).source := by
  intro y hy
  rw [infinityDiffeomorph_source]
  refine ⟨?_,hR (by change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R; rw [radiusSq_complex];exact hy.2)⟩
  intro he
  have hey : y=0 := by
    apply Complex.equivRealProdCLM.symm.injective
    simpa only [map_zero] using he
  exact radialAnnulus_ne_zero hr hy hey

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialProbability
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
section
variable {ι : Type*} [Fintype ι]

theorem radialProbability_nonneg {k : ι → ℕ × ℕ} (h0 : ∃ i,k i=(0,0))
    (D m : ι → ℕ) (p : Radial.Plane) (x : BaseCurve) (i : ι) :
    0 ≤ radialProbability k D m p x i :=
  Radial.selected_nonneg (fun j => coefficientNorm_pos (D j) (m j) x) h0 p i

theorem radialProbability_sum {k : ι → ℕ × ℕ} (h0 : ∃ i,k i=(0,0))
    (D m : ι → ℕ) (p : Radial.Plane) (x : BaseCurve) :
    ∑ i,radialProbability k D m p x i=1 :=
  Radial.selected_sum (fun j => coefficientNorm_pos (D j) (m j) x) h0 p

end
section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 omit [Nonempty ι] in
 theorem exists_regularCoefficient_log_bound (D m : ι → ℕ) {R : ℝ}
    (hR : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion) :
    ∃ M : ℝ,0≤M ∧ ∀ (i : ι) (ε : EndIndex) y,y∈radialAnnulus 0 R →
      |Real.log (regularCoefficientNorm (D i) (m i) ε y)|≤M := by
  have hc : ContinuousOn (fun y : Plane => fun j : ι × EndIndex =>
      Real.log (regularCoefficientNorm (D j.1) (m j.1) j.2 y)) (radialAnnulus 0 R) := by
    apply continuousOn_pi.mpr
    intro j y hy
    have hRy : Complex.equivRealProdCLM.symm y∈endRegularRegion := by
      apply hR
      change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R
      rw [radiusSq_complex]
      exact hy.2
    exact ((regularCoefficientNorm_contDiffAt (D j.1) (m j.1) j.2 hRy).continuousAt.log
      (regularCoefficientNorm_pos _ _ _ _).ne').continuousWithinAt
  obtain ⟨M,hM⟩ := (radialAnnulus_compact 0 R).exists_bound_of_continuousOn hc
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro i ε y hy
  exact (show |Real.log (regularCoefficientNorm (D i) (m i) ε y)|≤
      ‖fun j : ι × EndIndex => Real.log (regularCoefficientNorm (D j.1) (m j.1) j.2 y)‖ from
      (norm_le_pi_norm (fun j : ι × EndIndex => Real.log (regularCoefficientNorm (D j.1) (m j.1) j.2 y))
        (i,ε))).trans ((hM y hy).trans (le_max_right _ _))

 omit [Nonempty ι] in
 theorem exists_regularPrimitive_bound (D m : ι → ℕ) (c : ℝ) {R : ℝ}
    (hR : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion) :
    ∃ M : ℝ,0≤M ∧ ∀ (i : ι) (ε : EndIndex) y,y∈radialAnnulus 0 R →
      ‖weightedRegularEndPrimitive (D i) (m i) ε c y‖≤M := by
  have hc : ContinuousOn (fun y : Plane => fun j : ι × EndIndex =>
      weightedRegularEndPrimitive (D j.1) (m j.1) j.2 c y) (radialAnnulus 0 R) := by
    apply continuousOn_pi.mpr
    intro j y hy
    have hRy : Complex.equivRealProdCLM.symm y∈endRegularRegion := by
      apply hR
      change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R
      rw [radiusSq_complex]
      exact hy.2
    exact (weightedRegularEndPrimitive_contDiffAt _ _ _ _ hRy).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := (radialAnnulus_compact 0 R).exists_bound_of_continuousOn hc
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro i ε y hy
  exact (norm_le_pi_norm (fun j : ι × EndIndex =>
      weightedRegularEndPrimitive (D j.1) (m j.1) j.2 c y) (i,ε)).trans
    ((hM y hy).trans (le_max_right _ _))

end
section

variable {ι : Type*} [Fintype ι]

theorem radialEndRegularPrimitive_norm_le {k : ι → ℕ × ℕ} (h0 : ∃ i,k i=(0,0))
    (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane) (ε : EndIndex) (y : Plane) {M : ℝ}
    (hM : ∀ i,‖weightedRegularEndPrimitive (D i) (m i) ε c y‖≤M) :
    ‖radialEndRegularPrimitive k D m c p ε y‖≤M := by
  apply (norm_sum_le _ _).trans
  have hq (i : ι) : 0 ≤ radialEndProbability k D m p ε y i :=
    radialProbability_nonneg h0 D m p _ _
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hq _)]
  exact probability_weighted_le
    (fun i => radialProbability_nonneg h0 D m p (infinityDiffeomorph (parameters 0) ε y) i)
    (radialProbability_sum h0 D m p _) hM

end

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_BoundedPlanarResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open Set Filter
open scoped Topology

 theorem logarithmicError_nonneg {C R : ℝ} (hC : 0≤C) (hR : 0<R) (hR1 : R<1) (n : ℕ) :
    0≤logarithmicError C R n := by
  have hn : 1≤(n:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact div_nonneg hC (neg_pos.mpr (Real.log_neg (div_pos hR (by positivity))
    ((div_le_self hR.le hn).trans_lt hR1))).le

 theorem logarithmicError_bound {C R t : ℝ} (hC : 0≤C) (hR : 0<R) (hR1 : R<1)
    (n : ℕ) (ht : 0<t) (htR : t≤R/((n:ℝ)+1)) :
    C/(-Real.log t)≤logarithmicError C R n := by
  have hn : 1≤(n:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hb : 0< -Real.log (R/((n:ℝ)+1)) := neg_pos.mpr (Real.log_neg
    (div_pos hR (by positivity)) ((div_le_self hR.le hn).trans_lt hR1))
  exact div_le_div_of_nonneg_left hC hb (neg_le_neg (Real.log_le_log ht htR))

 theorem tendsto_logarithmicError {R : ℝ} (hR : 0<R) (C : ℝ) :
    Tendsto (logarithmicError C R) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => R/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_one_div] using
      (tendsto_const_nhds (x := R)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  have htp : Tendsto (fun n : ℕ => R/((n:ℝ)+1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall (fun n => div_pos hR (by positivity))⟩
  exact tendsto_const_nhds.div_atTop (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp htp))

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

 theorem sum_limitingEndOrder (D S : ℝ) (p : MomentPlane) :
    (∑ ε : EndIndex,limitingEndOrder D S p ε)=3*(D-3*(p 0+p 1))-2*markedHeight S p := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp (fun ε => limitingEndOrder D S p ε)]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,limitingEndOrder,
    finTwoArrowEquiv_symm_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Bool.false_eq_true,↓reduceIte]
  ring

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_CubicRadialEndSmooth
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open MeasureTheory

 theorem radialEndProbability_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source) (i : TrapezoidWeight A B) :
    ContDiffAt ℝ ∞ (fun z => radialEndProbability Radial.latticeIndex D m p ε z i) y :=
  ((radialProbability_smooth hA hAB D m hp i).contMDiffAt.comp y
    ((infinityDiffeomorph (parameters 0) ε).contMDiffOn.contMDiffAt
      ((infinityDiffeomorph (parameters 0) ε).open_source.mem_nhds hy))).contDiffAt

 theorem radialEndRegularPrimitive_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ)
    (c : ℝ) {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    ContDiffAt ℝ ∞ (radialEndRegularPrimitive Radial.latticeIndex D m c p ε) y :=
  ContDiffAt.sum (fun i _ => (radialEndProbability_contDiffAt hA hAB D m hp ε hy i).smul
    (weightedRegularEndPrimitive_contDiffAt (D i) (m i) ε c hR))

 theorem radialEndResidue_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ)
    (c : ℝ) {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source) :
    ContDiffAt ℝ ∞ (radialEndResidue Radial.latticeIndex D m c p ε) y :=
  ContDiffAt.sum (fun i _ => (radialEndProbability_contDiffAt hA hAB D m hp ε hy i).mul contDiffAt_const)

 attribute [local instance] OAI.PackingSufficiencySupport.CubicModel.cubicRadialEndSmoothSigmaCompact
theorem tendsto_radial_cubic_cutoff_mass_bp240_oai {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B)
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hr : 0 < r) (hRp : 0<R) (hR1 : R<1)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R) (c : ℝ) :
    Tendsto (fun n => surfaceCutoffMass (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)
      (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)) atTop
      (𝓝 (c*(3*((D:ℝ)-3*(p.1+p.2))-2*markedHeight S (planeVector p.1 p.2))*Real.pi)) := by
  obtain ⟨Mlog,hMlog,hlog⟩ := exists_regularCoefficient_log_bound
    (cubicDegree D (A := A) (B := B)) (cubicMarkedOrder S) hR
  obtain ⟨M,hM,hbound⟩ := exists_regularPrimitive_bound
    (cubicDegree D (A := A) (B := B)) (cubicMarkedOrder S) c hR
  obtain ⟨K,hK⟩ := (hg.continuous_deriv (by simp)).bounded_above_of_compact_support hgc.deriv
  have hK0 : 0≤K := (norm_nonneg (deriv g 0)).trans (hK 0)
  have hKg (t : ℝ) : |deriv g t|≤K := by simpa only [Real.norm_eq_abs] using hK t
  have hpoint (ε : EndIndex) (n : ℕ) (y : Plane)
      (hy : y∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))) :
      y∈(infinityDiffeomorph (parameters 0) ε).source ∧
      Complex.equivRealProdCLM.symm y∈endRegularRegion ∧
      y∈radialAnnulus 0 R ∧ 0 < radiusSq y ∧ radiusSq y<1 := by
    have hn : 1≤(n:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hys : y∈radialAnnulus 0 R := ⟨radiusSq_nonneg _,hy.2.trans (div_le_self hRp.le hn)⟩
    have hxR : Complex.equivRealProdCLM.symm y∈endRegularRegion := by
      apply hR
      change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R
      rw [radiusSq_complex]
      exact hys.2
    have hRI : {s : ℂ | Complex.normSq s≤R/((n:ℝ)+1)}⊆infinityRegion (parameters 0) :=
      fun s hs => (hR (hs.trans (div_le_self hRp.le hn))).1
    exact ⟨radialAnnulus_in_end (parameters 0) (div_pos hr (by positivity)) hRI ε hy,
      hxR,hys,(div_pos hr (by positivity)).trans_le hy.1,hys.2.trans_lt hR1⟩
  have ht := tendsto_curveCutoff_bounded_residue_bp240 (parameters 0)
    (radialPrimitive (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)
    (radialPrimitive_smooth hA hAB _ _ c hp)
    (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)
    (radialForm_smooth hA hAB _ _ c hp) (radialForm_skew _ _ _ c p) rfl
    hg hgc hr hRp.le (fun s hs => (hR hs).1) h1 h0 hK0 hM hKg
    (fun ε => c*limitingEndOrder D S (planeVector p.1 p.2) ε)
    (logarithmicError (|c| * (2*Mlog+Fintype.card (TrapezoidWeight A B))) R)
    (fun n => logarithmicError_nonneg (by positivity) hRp hR1 n)
    (tendsto_logarithmicError hRp _)
    (radialEndRegularPrimitive (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)
    (radialEndResidue (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)
    (fun ε n y hy => (radialEndRegularPrimitive_contDiffAt hA hAB _ _ c hp ε
      (hpoint ε n y hy).1 (hpoint ε n y hy).2.1).continuousAt.continuousWithinAt)
    (fun ε n y hy => (radialEndResidue_contDiffAt hA hAB _ _ c hp ε
      (hpoint ε n y hy).1).continuousAt.continuousWithinAt)
    (fun ε n y hy => radialEndRegularPrimitive_norm_le (Radial.lattice_zero A B) _ _ c p ε y
      (fun k => hbound k ε y (hpoint ε n y hy).2.2.1))
    (fun ε n y hy => by
      have hh := radialEndResidue_error_bp240 hA hS0 hAB hSB hB hS hp ε
        (hpoint ε n y hy).1 (hpoint ε n y hy).2.1
        (hpoint ε n y hy).2.2.2.1 (hpoint ε n y hy).2.2.2.2 hMlog
        (fun k => hlog k ε y (hpoint ε n y hy).2.2.1) c
      apply hh.trans
      rw [←mul_div_assoc]
      exact logarithmicError_bound (by positivity) hRp hR1 n (hpoint ε n y hy).2.2.2.1 hy.2)
    (fun ε n y hy => radialPrimitive_infinity
      (Radial.latticeIndex (A := A) (B := B)) (fun k => (cubicMarked_lt_degree hB hS k).le)
      (fun k => cubicMarked_twice_complement hB hS k) c p ε
      (hpoint ε n y hy).1 (hpoint ε n y hy).2.1)
  rw [←Finset.mul_sum] at ht
  rw [sum_limitingEndOrder] at ht
  exact ht

end PackingSufficiencySupport.CubicModel

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.CubicModel.tendsto_radial_cubic_cutoff_mass_bp240_oai := @OAI.PackingSufficiencySupport.CubicModel.tendsto_radial_cubic_cutoff_mass_bp240_oai
