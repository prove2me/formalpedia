-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.CubicModel.exists_cubic_bubble_separated_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:34.730776+00:00
-- url     : https://prove2.me/submissions/24eda642-ca89-4fe0-8469-7d74224c85de

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_exists_uniform_cubic_bubble_transfer_bp240
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in

theorem inverse_chart_isEmbedding {f g : E → E} {U W : Set E}
    (hf : ContinuousOn f U) (hg : ContinuousOn g W)
    (himage : f '' U = W) (hl : ∀ x ∈ U, g (f x) = x)
    (hr : ∀ y ∈ W, g y ∈ U ∧ f (g y) = y) :
    Topology.IsEmbedding (fun y : W => g y) := by
  let e : PartialHomeomorph E E := {
    toFun := f
    invFun := g
    source := U
    target := W
    map_source' := fun x hx => himage ▸ mem_image_of_mem f hx
    map_target' := fun y hy => (hr y hy).1
    left_inv' := hl
    right_inv' := fun y hy => (hr y hy).2
    continuousOn_toFun := hf
    continuousOn_invFun := hg }
  exact e.symm.isEmbedding_restrict

theorem inverse_chart_pullback {f g : E → E} {U W : Set E}
    (hU : IsOpen U) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g W) (hr : ∀ y ∈ W, g y ∈ U ∧ f (g y) = y)
    (A : E → E →L[ℝ] E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hform : ∀ x ∈ U, ∀ v w,
      B (fderiv ℝ f x v) (fderiv ℝ f x w) = A x v w)
    {y : E} (hy : y ∈ W) (v w : E) :
    A (g y) (fderiv ℝ g y v) (fderiv ℝ g y w) = B v w := by
  have hdf : DifferentiableAt ℝ f (g y) :=
    (hf.contDiffAt (hU.mem_nhds (hr y hy).1)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdg : DifferentiableAt ℝ g y :=
    (hg.contDiffAt (hW.mem_nhds hy)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq : (f ∘ g) =ᶠ[𝓝 y] id :=
    Filter.eventually_of_mem (hW.mem_nhds hy) (fun z hz => (hr z hz).2)
  have hd : (fderiv ℝ f (g y)).comp (fderiv ℝ g y) = ContinuousLinearMap.id ℝ E := by
    rw [←fderiv_comp y hdf hdg,heq.fderiv_eq]
    exact fderiv_id
  calc
    A (g y) (fderiv ℝ g y v) (fderiv ℝ g y w) =
      B (fderiv ℝ f (g y) (fderiv ℝ g y v))
        (fderiv ℝ f (g y) (fderiv ℝ g y w)) := (hform _ (hr y hy).1 _ _).symm
    _ = B v w := by
      change B ((fderiv ℝ f (g y)).comp (fderiv ℝ g y) v)
        ((fderiv ℝ f (g y)).comp (fderiv ℝ g y) w) = _
      rw [hd]
      rfl

end
section

variable {ι : Type*} [Fintype ι]

theorem phaseOpenBall_open (a : ℝ) : IsOpen (phaseOpenBall (ι := ι) a) :=
  isOpen_lt phaseSq_smooth.continuous continuous_const

theorem fsBallMap_image {a : ℝ} (ha : 0 < a) :
    fsBallMap (ι := ι) a '' univ = phaseOpenBall a := by
  apply Subset.antisymm
  · rintro _ ⟨z,_,rfl⟩
    exact fsBallMap_mem ha z
  · intro z hz
    exact ⟨fsAffineMap a z,mem_univ _,fsBallMap_fsAffineMap ha hz⟩

theorem fsAffineMap_isEmbedding {a : ℝ} (ha : 0 < a) :
    Topology.IsEmbedding (fun z : phaseOpenBall (ι := ι) a => fsAffineMap a z.1) :=
  inverse_chart_isEmbedding (fsBallMap_smooth a).continuous.continuousOn
    (fsAffineMap_smoothOn a).continuousOn (fsBallMap_image ha)
    (fun z _ => fsAffineMap_fsBallMap ha z)
    (fun _ hz => ⟨mem_univ _,fsBallMap_fsAffineMap ha hz⟩)

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

theorem fsAffineMap_pullback {a : ℝ} (ha : 0 < a) {z : PlanePhase ι}
    (hz : z ∈ phaseOpenBall a) (v w : PlanePhase ι) :
    affineFSForm a (fsAffineMap a z)
      (fderiv ℝ (fsAffineMap a) z v) (fderiv ℝ (fsAffineMap a) z w) = phaseArea v w := by
  apply inverse_chart_pullback isOpen_univ (phaseOpenBall_open a)
    (fsBallMap_smooth a).contDiffOn (fsAffineMap_smoothOn a)
    (fun y hy => ⟨Set.mem_univ _,fsBallMap_fsAffineMap ha hy⟩)
    (affineFSForm a) phaseArea (fun y _ => fsBallMap_pullback ha.le y) hz

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

theorem openBall_isOpen (n : ℕ) (R : ℝ) : IsOpen (openBall n R) :=
  isOpen_lt (continuous_capacity n) continuous_const

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

 theorem firstQuadricChart_smooth : ContDiff ℂ ∞ firstQuadricChart := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact contDiff_snd
  · exact contDiff_const
  · exact contDiff_fst.fst
  · exact contDiff_fst.snd

 theorem outerPolynomial_smooth {A B : ℕ} (L S : ℕ) (t δ : ℝ) :
    ContDiff ℂ ∞ (outerPolynomial (A := A) (B := B) L S t δ) := by
  exact contDiff_pi.mpr (fun ki => contDiff_const.mul (liftedSection_smooth _ _ _ _))

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem quadricLiftPolynomial_one (n : ℕ) (x : Fin 4 → ℂ) :
    quadricLiftPolynomial n 1 x=x 1^n := by
  classical
  simp [quadricLiftPolynomial,quadricLiftMonomial,liftAlpha,liftBeta,liftGamma,liftDelta]

 theorem outerPolynomial_vertex {A B : ℕ} (L S : ℕ) (t δ : ℝ)
    (p : CubicAmbient) (k : TrapezoidWeight A B) (hk : Radial.latticeIndex k=(0,0)) :
    outerPolynomial L S t δ (firstQuadricChart p) (k,none)=1 := by
  simp [outerPolynomial,liftedSection,hk,cubicNormalSection,coefficientPolynomial,
    coefficientPowers,quadricLiftPolynomial_one,firstQuadricChart]

 theorem outerPolynomial_nonzero {A B : ℕ} (L S : ℕ) (t δ : ℝ) (p : CubicAmbient) :
    complexCartesian (outerPolynomial (A := A) (B := B) L S t δ (firstQuadricChart p))≠0 := by
  obtain ⟨k,hk⟩ := lattice_zero A B
  intro h
  have he := congrFun (complexCartesian.injective (h.trans (map_zero _).symm)) (k,none)
  rw [outerPolynomial_vertex L S t δ p k hk] at he
  exact one_ne_zero he

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_SixLargeQuadricPacking
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

omit [Fintype ι] in
 theorem homogeneousBubble_zero {m p : ℕ} (hp : m<p) (L : ℕ) (x : Option ι → ℂ) :
    homogeneousBubble L m p 0 x=0 := by
  ext j
  simp [homogeneousBubble,zero_pow (show p-m≠0 by omega)]

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

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open scoped BigOperators

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

 theorem cubicBubblePolynomial_real_smooth {L S A B m p N : ℕ} (t δ ε : ℝ) :
     ContDiff ℝ ∞ (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) := by
   exact ((cubicBubblePolynomial_joint_smooth L S m p N t δ).comp
       (contDiff_const.prodMk contDiff_id)).restrict_scalars ℝ

end PackingSufficiencySupport.CubicModel

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
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology

 theorem complexCartesian_standardForm {n : ℕ} (v w : Ambient n) :
    standardForm v w=phaseArea (complexCartesian v) (complexCartesian w) := by
  simp only [standardForm,phaseArea_apply,complexCartesian]
  rfl

 theorem affineFSForm_mul {ι : Type*} [Fintype ι] (a b : ℝ) (x v w : PlanePhase ι) :
     affineFSForm (a*b) x v w=a*affineFSForm b x v w := by
   rw [affineFSForm_apply,affineFSForm_apply]
   ring

 theorem complexFSAffine_smoothOn {n : ℕ} (a : ℝ) :
     ContDiffOn ℝ ∞ (complexFSAffine (n := n) a) (openBall n (Real.pi*a)) := by
   have hinto : MapsTo (complexCartesian (ι := Fin n)) (openBall n (Real.pi*a)) (phaseOpenBall a) := by
     intro x hx
     change phaseSq (complexCartesian x)<a
     rw [complexCartesian_sq]
     exact (mul_lt_mul_iff_right₀ Real.pi_pos).mp hx
   exact (complexCartesian (ι := Fin n)).symm.contDiff.comp_contDiffOn
     ((fsAffineMap_smoothOn a).comp (complexCartesian (ι := Fin n)).contDiff.contDiffOn hinto)

 theorem complexCartesian_ball_isEmbedding {n : ℕ} (a : ℝ) :
     Topology.IsEmbedding (fun x : openBall n (Real.pi*a) => complexCartesian x.val) :=
   (complexCartesian (ι := Fin n)).toHomeomorph.isEmbedding.comp
     (Topology.IsEmbedding.subtypeVal (p := fun x => x∈openBall n (Real.pi*a)))

 theorem complexCartesian_ball_codRestrict {n : ℕ} (a : ℝ) :
     Topology.IsEmbedding (fun x : openBall n (Real.pi*a) =>
       (⟨complexCartesian x.val,complexCartesian_ball_into x⟩ : phaseOpenBall a)) :=
   (complexCartesian_ball_isEmbedding (n := n) a).codRestrict (phaseOpenBall a) complexCartesian_ball_into

 theorem complexFSAffine_isEmbedding {n : ℕ} {a : ℝ} (ha : 0<a) :
     Topology.IsEmbedding (fun x : openBall n (Real.pi*a) => complexFSAffine a x.val) := by
   have hf : Topology.IsEmbedding (fun x : openBall n (Real.pi*a) => fsAffineMap a (complexCartesian x.val)) :=
     (fsAffineMap_isEmbedding (ι := Fin n) ha).comp (complexCartesian_ball_codRestrict (n := n) a)
   exact (complexCartesian (ι := Fin n)).symm.toHomeomorph.isEmbedding.comp hf

 theorem complexFSAffine_pullback {n : ℕ} {a : ℝ} (ha : 0<a) {x : Ambient n}
     (hx : x∈openBall n (Real.pi*a)) (v w : Ambient n) :
     affineFSForm a (complexCartesian (complexFSAffine a x))
       (complexCartesian (fderiv ℝ (complexFSAffine a) x v))
       (complexCartesian (fderiv ℝ (complexFSAffine a) x w))=standardForm v w := by
   have hxc : complexCartesian x∈phaseOpenBall a := by
     change phaseSq (complexCartesian x)<a
     rw [complexCartesian_sq]
     exact (mul_lt_mul_iff_right₀ Real.pi_pos).mp hx
   have hs := ((fsAffineMap_smoothOn a).contDiffAt ((phaseOpenBall_open a).mem_nhds hxc)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
   have hd (u : Ambient n) : fderiv ℝ (complexFSAffine a) x u=
       complexCartesian.symm (fderiv ℝ (fsAffineMap a) (complexCartesian x) (complexCartesian u)) := by
     exact congrArg (fun L => L u) ((complexCartesian.symm.hasFDerivAt.comp x
       (hs.hasFDerivAt.comp x (complexCartesian (ι := Fin n)).hasFDerivAt)).fderiv)
   rw [complexFSAffine,hd,hd]
   simp only [ContinuousLinearEquiv.apply_symm_apply]
   rw [fsAffineMap_pullback ha hxc,complexCartesian_standardForm]

 theorem complexFSAffine_ball_embedding {m : ℕ} {r a : ℝ} (ha : 0<a) (hr : r<Real.pi*a) :
     FormNeighborhoodEmbedding (closedBall (m+1) r) (fun _ => successorStandardForm m)
       (fun x => (affineFSForm a (complexCartesian x)).bilinearComp
         complexCartesian.toContinuousLinearMap complexCartesian.toContinuousLinearMap) (complexFSAffine a) := by
   refine ⟨openBall (m+1) (Real.pi*a),openBall_isOpen _ _,?_,
     (complexFSAffine_smoothOn a).contMDiffOn,complexFSAffine_isEmbedding ha,?_⟩
   · intro x hx
     exact (show capacity x ≤ r from hx).trans_lt hr
   · intro x hx v w
     simp only [mfderiv_eq_fderiv]
     exact (complexFSAffine_pullback ha hx v w).trans
       (successorStandardForm_apply m v w).symm

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem exists_uniform_cubic_bubble_ball {L S A B p N : ℕ} (m : ℕ)
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (hm : m+1≤p) (t δ : ℝ) {c : ℝ} (hc : 0 < c)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : 0<D 0)
     {r : ℝ} (hr : r<Real.pi*(D 0*((m+1:ℕ)*c)))
     {T : Set (Fin 3 → ℂ)} (hT : IsOpen T) (h0T : (0 : Fin 3 → ℂ)∈T)
     {η : ℝ} (hη : 0<η) :
     ∃ τ>0,τ≤η ∧ ∀ ε∈Ioc (0:ℝ) τ,∃ g : Ambient 3 → Ambient 3,
       FormNeighborhoodEmbedding (closedBall 3 r) (fun _ => successorStandardForm 2)
         (degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)) g ∧
       MapsTo g (closedBall 3 r) T := by
   let a : ℝ := D 0*((m+1:ℕ)*c)
   have ha : 0<a := mul_pos hD0 (mul_pos (by positivity) hc)
   let f : Ambient 3 → Ambient 3 := complexFSAffine a
   have hf := complexFSAffine_ball_embedding (m := 2) ha hr
   let K : Set (Fin 3 → ℂ) := f '' closedBall 3 r
   have hK : IsCompact K := by
     obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hf
     exact (closedBall_isCompact 3 r).image_of_continuousOn (hs.continuousOn.mono hKU)
   obtain ⟨τ,hτ,hτη,hall⟩ := exists_uniform_cubic_bubble_transfer_bp240 m hAS hS hB hp hN hm t δ hc hD hD0 hK hT h0T hη
   refine ⟨τ,hτ,hτη,?_⟩
   intro ε hε
   obtain ⟨g,W,hW,hKW,hg,he,hgT,hgf⟩ := hall ε hε
   have him : MapsTo f (closedBall 3 r) W := fun x hx => hKW ⟨x,hx,rfl⟩
   refine ⟨g ∘ f,hf.postcompose hW hg.contMDiff.contMDiffOn he ?_ him,?_⟩
   · intro x hx v w
     simp only [mfderiv_eq_fderiv]
     exact (hgf x hx v w).trans
       (affineFSForm_mul (D 0) ((m+1:ℕ)*c) (complexCartesian x)
         (complexCartesian v) (complexCartesian w)).symm
   · exact hgT.comp him

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

omit [Fintype ι] [Fintype κ] [Fintype ν] in
 theorem complexLeftBlockCLM_apply (z : κ → ℂ) :
     complexLeftBlockCLM (ι := ι) (ν := ν) z=complexLeftBlock z := by
   ext i
   rcases i with (i|(k|j)) <;> rfl

 theorem complexLeftBlock_sq (z : κ → ℂ) :
     phaseSq (complexCartesian (complexLeftBlock (ι := ι) (ν := ν) z))=
       phaseSq (complexCartesian z) := by
   simp [complexCartesian_sq,complexLeftBlock,Fintype.sum_sum_type]

 theorem complexLeftBlock_pairing (z v : κ → ℂ) :
     complexPairing (complexLeftBlock (ι := ι) (ν := ν) z) (complexLeftBlock v)=
       complexPairing z v := by
   simp [complexPairing,complexLeftBlock,Fintype.sum_sum_type]

 theorem complexLeftBlock_hopf (c : ℝ) (z v : κ → ℂ) :
     hopfPrimitive c (complexCartesian (complexLeftBlock (ι := ι) (ν := ν) z))
       (complexCartesian (complexLeftBlock v))=
     hopfPrimitive c (complexCartesian z) (complexCartesian v) := by
   simp only [hopfPrimitive,smul_apply,smul_eq_mul,complexLeftBlock_sq,
     ←complexPairing_im,complexLeftBlock_pairing]

 theorem complexLeftBlock_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
     {F : E → (κ → ℂ)} (hF : ContDiff ℝ ∞ F) (c : ℝ) :
     primitivePullback (hopfPrimitive c)
       (fun z => complexCartesian (complexLeftBlock (ι := ι) (ν := ν) (F z)))=
     primitivePullback (hopfPrimitive c) (fun z => complexCartesian (F z)) := by
   ext z v
   have hD := complexCartesian.hasFDerivAt.comp z
     ((complexLeftBlockCLM (ι := ι) (ν := ν)).hasFDerivAt.comp z
       (hF.differentiable (by simp) z).hasFDerivAt)
   have hD' := complexCartesian.hasFDerivAt.comp z (hF.differentiable (by simp) z).hasFDerivAt
   change hopfPrimitive c _ (fderiv ℝ _ z v)=hopfPrimitive c _ (fderiv ℝ _ z v)
   rw [show fderiv ℝ (fun z => complexCartesian (complexLeftBlock (ι := ι) (ν := ν) (F z))) z=_ from by simpa only [Function.comp_def,complexLeftBlockCLM_apply] using hD.fderiv,
     show fderiv ℝ (fun z => complexCartesian (F z)) z=_ from hD'.fderiv]
   simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
     complexLeftBlockCLM_apply] using complexLeftBlock_hopf (ι := ι) (ν := ν) c (F z) (fderiv ℝ F z v)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem firstBubbleLift_smooth : ContDiff ℂ ∞ firstBubbleLift := by
   apply contDiff_pi.mpr
   rintro (_|i)
   · exact contDiff_snd
   · fin_cases i
     · exact contDiff_const
     · exact contDiff_fst.fst
     · exact contDiff_fst.snd

 theorem firstBubbleLift_coordinates (z : CubicAmbient) :
     distinguishedHomogeneousCoordinates (firstBubbleLift z)=firstQuadricChart z := by
   ext i
   fin_cases i <;> rfl

 theorem firstBubbleLift_nonzero (z : CubicAmbient) : firstBubbleLift z≠0 := by
   intro h
   exact one_ne_zero (congrFun h (some 0))

 theorem cubicOuterBubble_nonzero {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ)
     (ε : ℂ) (z : CubicAmbient) :
     complexCartesian (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε (firstBubbleLift z))≠0 := by
   intro h
   have he := complexCartesian.injective (h.trans (map_zero _).symm)
   have ho : outerPolynomial (A := A) (B := B) L S t δ (firstQuadricChart z)=0 := by
     ext i
     have hh := congrFun he (Sum.inl i)
     simpa only [cubicBubblePolynomial,bubblePolynomial,Sum.elim_inl,Function.comp_def,
       firstBubbleLift_coordinates,Pi.zero_apply] using hh
   apply outerPolynomial_nonzero (A := A) (B := B) L S t δ z
   rw [ho,map_zero]

 theorem cubicOuterBubble_joint_real_smooth {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ) :
     ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient =>
       cubicBubblePolynomial (A := A) (B := B) L S m p N t δ a.1 (firstBubbleLift a.2)) := by
   have hε : ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient => (a.1:ℂ)) :=
     Complex.ofRealCLM.contDiff.comp contDiff_fst
   have hF : ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient => firstBubbleLift a.2) :=
     (firstBubbleLift_smooth.restrict_scalars ℝ).comp contDiff_snd
   have hG : ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient => bubbleCoordinates (a.1:ℂ) (firstBubbleLift a.2)) := by
     apply contDiff_pi.mpr
     rintro (_|i)
     · exact hε.mul ((contDiff_apply ℝ ℂ none).comp hF)
     · exact (contDiff_apply ℝ ℂ (some i)).comp hF
   apply contDiff_pi.mpr
   rintro (i|(j|k))
   · change ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient =>
       outerPolynomial (A := A) (B := B) L S t δ (distinguishedHomogeneousCoordinates (firstBubbleLift a.2)) i)
     simp only [firstBubbleLift_coordinates]
     exact (contDiff_apply ℝ ℂ i).comp (((outerPolynomial_smooth (A := A) (B := B) L S t δ).restrict_scalars ℝ).comp
       ((firstQuadricChart_smooth.restrict_scalars ℝ).comp contDiff_snd))
   · change ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient => (a.1:ℂ)^(p-m)*(firstBubbleLift a.2 none)^(L-m)*
       homogeneousVeronese m (bubbleCoordinates (a.1:ℂ) (firstBubbleLift a.2)) j)
     exact ((hε.pow _).mul (((contDiff_apply ℝ ℂ none).comp hF).pow _)).mul
       ((contDiff_apply ℝ ℂ j).comp (((homogeneousVeronese_smooth m).restrict_scalars ℝ).comp hG))
   · change ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient => (a.1:ℂ)^N*homogeneousVeronese L (firstBubbleLift a.2) k)
     exact (hε.pow N).mul ((contDiff_apply ℝ ℂ k).comp
       (((homogeneousVeronese_smooth L).restrict_scalars ℝ).comp hF))

 theorem cubicOuterBubblePrimitive_joint_smooth {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) :
     ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient =>
       cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D a.1 a.2) := by
   have hF : ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient => complexCartesian (firstBubbleLift a.2)) :=
     complexCartesian.contDiff.comp ((firstBubbleLift_smooth.restrict_scalars ℝ).comp contDiff_snd)
   have hQ := complexCartesian.contDiff.comp
     (cubicOuterBubble_joint_real_smooth (A := A) (B := B) L S m p N t δ)
   have hFn (a : ℝ×CubicAmbient) : complexCartesian (firstBubbleLift a.2)≠0 := by
     intro h
     exact firstBubbleLift_nonzero a.2 (complexCartesian.injective (h.trans (map_zero _).symm))
   exact (contDiff_const.sub (contDiff_const.mul (hD.comp contDiff_fst))).smul
     (fibrePrimitivePullback_smooth hF (fun a => hopfPrimitive_smoothAt c (hFn a))) |>.add
       ((hD.comp contDiff_fst).smul (fibrePrimitivePullback_smooth hQ
         (fun a => hopfPrimitive_smoothAt c (cubicOuterBubble_nonzero L S m p N t δ a.1 a.2))))

 theorem cubicOuterBubblePrimitive_smooth_family {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) :
     SmoothOneFormFamily (cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D) := by
   intro x
   simpa only [vector_chartOneForm] using
     (cubicOuterBubblePrimitive_joint_smooth (A := A) (B := B) L S m p N t δ c hD).contDiffOn

 theorem cubicOuterBubblePrimitive_zero {A B L S m p N : ℕ} (hmp : m<p) (hN : 0<N)
     (t δ c : ℝ) {D : ℝ → ℝ} (hD : (L:ℝ)*D 0=1) :
     cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D 0=
       outerAmbientPrimitive (A := A) (B := B) L S (D 0*c) t δ := by
   have he : (fun z => cubicBubblePolynomial (A := A) (B := B) L S m p N t δ (0:ℝ) (firstBubbleLift z))=
       (fun z => complexLeftBlock (ι := Fin m → Option (Fin 3)) (ν := Fin L → Option (Fin 3))
         (outerPolynomial (A := A) (B := B) L S t δ (firstQuadricChart z))) := by
     funext z
     ext i
     rcases i with (i|(j|k))
     · simp only [cubicBubblePolynomial,bubblePolynomial,Sum.elim_inl,Function.comp_def,
         firstBubbleLift_coordinates,complexLeftBlock]
     · simp only [cubicBubblePolynomial,bubblePolynomial,Sum.elim_inr,Sum.elim_inl,
         Complex.ofReal_zero,homogeneousBubble_zero hmp,Pi.zero_apply,complexLeftBlock]
     · simp [cubicBubblePolynomial,bubblePolynomial,complexLeftBlock,zero_pow hN.ne']
   unfold cubicOuterBubblePrimitive
   rw [hD,sub_self,zero_smul,zero_add]
   change D 0•primitivePullback (hopfPrimitive c) (fun z => complexCartesian
     (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ (0:ℝ) (firstBubbleLift z)))=_
   simp_rw [congrFun he]
   erw [complexLeftBlock_primitive (((outerPolynomial_smooth (A := A) (B := B) L S t δ).restrict_scalars ℝ).comp
     (firstQuadricChart_smooth.restrict_scalars ℝ))]
   funext z
   apply ContinuousLinearMap.ext
   intro v
   simp only [Function.comp_def,Pi.smul_apply,smul_apply,smul_eq_mul,primitivePullback,outerAmbientPrimitive,
     ContinuousLinearMap.comp_apply,hopfPrimitive]
   ring

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_SixCubicInnerNormalPacking
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope
open FiniteMoment.Radial

 theorem exists_uniform_outer_bubble_transfer {A B L S m p N : ℕ} (hmp : m<p) (hN : 0<N)
     (t δ c : ℝ) {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : (L:ℝ)*D 0=1)
     {K : Set CubicAmbient} (hK : IsCompact K)
     (hinv : ∀ x∈K,(outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ x).IsInvertible)
     {T : Set CubicAmbient} (hT : IsOpen T) (hKT : K⊆T) {η : ℝ} (hη : 0<η) :
     ∃ τ>0,τ≤η ∧ ∀ ε∈Ioc (0:ℝ) τ,∃ g : CubicAmbient → CubicAmbient,∃ W,
       IsOpen W ∧ K⊆W ∧ ContDiff ℝ ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
       MapsTo g W T ∧ ∀ x∈W,∀ v w,
       cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε
         (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)=
       outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ x v w := by
   let Γ := cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D
   have he0 (x : CubicAmbient) : manifoldExteriorOneForm (Γ 0) x=
       outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ x := by
     change manifoldExteriorOneForm (cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D 0) x=_
     rw [cubicOuterBubblePrimitive_zero hmp hN t δ c hD0,vector_exteriorOneForm]
     rfl
   have hid : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicAmbient)) 𝓘(ℝ,CubicAmbient) ∞
       (fun a : ℝ×CubicAmbient => a.2) := contMDiff_snd
   obtain ⟨τ,hτ,hτη,hall⟩ := exists_uniform_compact_exact_fibre_embedding_central_into_bp240
     (cubicOuterBubblePrimitive_smooth_family (A := A) (B := B) L S m p N t δ c hD) hK
     (by intro x hx; rw [he0]; exact hinv x hx) isOpen_univ (subset_univ K) hη hid
     (fun _ _ => Topology.IsEmbedding.subtypeVal) hT hKT
     (fun ε => cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε) (by
       intro ε _ x _
       apply ContinuousLinearMap.ext
       intro v
       apply ContinuousLinearMap.ext
       intro w
       simp only [manifoldMapDifferential,mfderiv_eq_fderiv,fderiv_fun_id,
         vector_exteriorOneForm,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.id_apply]
       rfl)
   refine ⟨τ,hτ,hτη,?_⟩
   intro ε hε
   obtain ⟨g,W,hW,hKW,hg,he,hgT,hgf⟩ := hall ε hε
   refine ⟨g,W,hW,hKW,hg.contDiff,he,hgT,?_⟩
   intro x hx v w
   have hh := hgf x hx v w
   rw [he0] at hh
   simp only [mfderiv_eq_fderiv] at hh
   convert! hh using 1
   all_goals try with_reducible_and_instances rfl

 theorem outer_packing_uniform_bubble_into {A B L S m p N k : ℕ} (hmp : m<p) (hN : 0<N)
     (t δ c : ℝ) {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : (L:ℝ)*D 0=1)
     {T : Set CubicAmbient} (hT : IsOpen T)
     (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient)
     (hf : ∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
       (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ) (f i))
     (hinto : ∀ i,MapsTo (f i) (closedBall 3 (r i)) T)
     (hd : Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r i)) (f j '' closedBall 3 (r j))))
     {η : ℝ} (hη : 0<η) :
     ∃ τ>0,τ≤η ∧ ∀ ε∈Ioc (0:ℝ) τ,∃ g : Fin k → Ambient 3 → CubicAmbient,
       (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
         (cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε) (g i)) ∧
       (∀ i,MapsTo (g i) (closedBall 3 (r i)) T) ∧
       Pairwise (fun i j => Disjoint (g i '' closedBall 3 (r i)) (g j '' closedBall 3 (r j))) := by
   let K : Set CubicAmbient := ⋃ i,f i '' closedBall 3 (r i)
   have hK : IsCompact K := by
     apply isCompact_iUnion
     intro i
     obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hf i
     exact (closedBall_isCompact 3 (r i)).image_of_continuousOn (hs.continuousOn.mono hKU)
   have hKT : K⊆T := by
     intro x hx
     obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
     exact hinto i hy
   have hdim : Module.finrank ℝ (Ambient 3)=Module.finrank ℝ CubicAmbient := by
     simp [Ambient,CubicAmbient,PlaneBase,Module.finrank_pi_fintype,Complex.finrank_real_complex]
   have hinv (x : CubicAmbient) (hx : x∈K) :
       (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ x).IsInvertible := by
     obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
     exact (hf i).target_invertible hdim hy (successorStandardForm_isInvertible 2)
   obtain ⟨τ,hτ,hτη,hall⟩ := exists_uniform_outer_bubble_transfer hmp hN t δ c hD hD0 hK hinv
     hT hKT hη
   refine ⟨τ,hτ,hτη,?_⟩
   intro ε hε
   obtain ⟨g,W,hW,hKW,hg,he,hgT,hgf⟩ := hall ε hε
   obtain ⟨hcomp,hdj⟩ := postcompose_form_packing (fun i => closedBall 3 (r i))
     (fun _ => successorStandardForm 2)
     (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ)
     (cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε)
     hW g hg.contMDiff.contMDiffOn he (by
       intro x hx v w
       simp only [mfderiv_eq_fderiv]
       convert! hgf x hx v w using 1) f hf
     (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hd
   exact ⟨fun i => g ∘ f i,hcomp,
     fun i x hx => hgT (hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)),hdj⟩

 theorem firstToDistinguished_isEmbedding :
     Topology.IsEmbedding (fun z : {z : CubicAmbient // z.2≠0} => firstToDistinguished z.val) :=
   Topology.IsEmbedding.subtypeVal.comp firstDistinguishedHomeomorph.isEmbedding

 theorem firstToDistinguished_lift {z : CubicAmbient} (hz : z.2≠0) :
     complexAffineLift (firstToDistinguished z)=z.2⁻¹•firstBubbleLift z := by
   ext i
   rcases i with (_|i)
   · simp [complexAffineLift,firstBubbleLift,Pi.smul_apply,smul_eq_mul,hz]
   · fin_cases i <;> simp [complexAffineLift,firstBubbleLift,firstToDistinguished,
       Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]

 theorem firstToDistinguished_lift_near {z : CubicAmbient} (hz : z.2≠0) :
     (fun y => complexAffineLift (firstToDistinguished y))=ᶠ[𝓝 z]
       (fun y : CubicAmbient => y.2⁻¹•firstBubbleLift y) := by
   filter_upwards [(isOpen_ne_fun continuous_snd continuous_const).mem_nhds hz] with y hy
   exact firstToDistinguished_lift hy

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Filter

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem hopfCurvaturePullback_congr_near {F G : E → (ι → ℂ)} {x : E}
     (h : F=ᶠ[𝓝 x]G) (c : ℝ) (v w : E) :
     hopfCurvaturePullback c F x v w=hopfCurvaturePullback c G x v w := by
   have hc : (fun y => complexCartesian (F y))=ᶠ[𝓝 x](fun y => complexCartesian (G y)) :=
     h.fun_comp complexCartesian
   unfold hopfCurvaturePullback
   rw [h.eq_of_nhds,hc.fderiv_eq]

 theorem degreeHopfCurvaturePullback_congr_near {P : (ι → ℂ) → (κ → ℂ)}
     {F G : E → (ι → ℂ)} {x : E} (h : F=ᶠ[𝓝 x]G) (q c d : ℝ) (v w : E) :
     degreeHopfCurvaturePullback q P c d F x v w=degreeHopfCurvaturePullback q P c d G x v w := by
   unfold degreeHopfCurvaturePullback
   rw [hopfCurvaturePullback_congr_near h]
   exact congrArg (fun u : ℝ => (1-q*d)*hopfCurvaturePullback c G x v w+d*u)
     (hopfCurvaturePullback_congr_near (h.fun_comp P) c v w)

 theorem homogeneousMixedPrimitive_exterior {P : (ι → ℂ) → (κ → ℂ)}
     (hP : ContDiff ℝ ∞ P) {F : E → (ι → ℂ)} (hF : ContDiff ℝ ∞ F)
     {x : E} (hx : complexCartesian (F x)≠0) (hPx : complexCartesian (P (F x))≠0)
     (q c d : ℝ) (v w : E) :
     euclideanExteriorOneForm ((1-q*d)•primitivePullback (hopfPrimitive c) (complexCartesian ∘ F)+
       d•primitivePullback (hopfPrimitive c) (complexCartesian ∘ P ∘ F)) x v w=
       degreeHopfCurvaturePullback q P c d F x v w := by
   have hFC := complexCartesian.contDiff.comp hF
   have hPC := complexCartesian.contDiff.comp (hP.comp hF)
   have hα := primitivePullback_smoothAt (g := complexCartesian ∘ F) (hopfPrimitive_smoothAt c hx) hFC.contDiffAt
   have hβ := primitivePullback_smoothAt (g := complexCartesian ∘ P ∘ F) (hopfPrimitive_smoothAt c hPx) hPC.contDiffAt
   erw [euclideanExteriorOneForm_add ((hα.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).const_smul (1-q*d))
       ((hβ.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).const_smul d),
     euclideanExteriorOneForm_smul (1-q*d) (hα.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
     euclideanExteriorOneForm_smul d (hβ.differentiableAt (by simp)),
     primitivePullback_exteriorAt (g := complexCartesian ∘ F) (hopfPrimitive_smoothAt c hx) hFC.contDiffAt,
     primitivePullback_exteriorAt (g := complexCartesian ∘ P ∘ F) (hopfPrimitive_smoothAt c hPx) hPC.contDiffAt]
   rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Topology
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem cubicOuterBubbleForm_homogeneous {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ)
     (D : ℝ → ℝ) (ε : ℝ) (z v w : CubicAmbient) :
     cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε z v w=
       degreeHopfCurvaturePullback (L:ℝ)
         (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) c (D ε) firstBubbleLift z v w := by
   have hzn : complexCartesian (firstBubbleLift z)≠0 := by
     intro h
     exact firstBubbleLift_nonzero z (complexCartesian.injective (h.trans (map_zero _).symm))
   exact homogeneousMixedPrimitive_exterior (cubicBubblePolynomial_real_smooth t δ ε)
     (firstBubbleLift_smooth.restrict_scalars ℝ) hzn
       (cubicOuterBubble_nonzero L S m p N t δ ε z) (L:ℝ) c (D ε) v w

 theorem firstToDistinguished_curvature {L S A B m p N : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hm : m≤L) (t δ c : ℝ)
     (D : ℝ → ℝ) {ε : ℝ} (hε : ε≠0) {z : CubicAmbient} (hz : z.2≠0) (v w : CubicAmbient) :
     degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) c (D ε)
       (firstToDistinguished z) (fderiv ℝ firstToDistinguished z v) (fderiv ℝ firstToDistinguished z w)=
       cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε z v w := by
   have hP := cubicBubblePolynomial_real_smooth (L := L) (S := S) (A := A) (B := B) (m := m) (p := p) (N := N) t δ ε
   rw [degreeAffineForm_pullback hP ((firstToDistinguished_smoothAt hz).differentiableAt (by simp)),
     cubicOuterBubbleForm_homogeneous]
   have hlocal := degreeHopfCurvaturePullback_congr_near
     (P := cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε)
     (firstToDistinguished_lift_near hz) (L:ℝ) c (D ε) v w
   exact hlocal.trans (degreeHopfCurvaturePullback_gauge hP
     (fun x hx => cubicBubblePolynomial_nonzero L S m p N t δ (Complex.ofReal_ne_zero.mpr hε) hx)
     (cubicBubblePolynomial_homogeneous hAS hS hB hm p N t δ ε)
     ((differentiableAt_snd (𝕜 := ℝ)).inv hz)
     ((firstBubbleLift_smooth.restrict_scalars ℝ).differentiable (by simp) z)
     (inv_ne_zero hz) (firstBubbleLift_nonzero z) c (D ε) v w)

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

 theorem exists_cubic_bubble_separated_bp240_oai {A B L S m p N k : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (hm : m+1<p) (t δ : ℝ) {c : ℝ} (hc : 0 < c)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : 0<D 0) (hDL : (L:ℝ)*D 0=1)
     {r₀ : ℝ} (hr₀ : r₀<Real.pi*(D 0*((m+1:ℕ)*c)))
     (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient)
     (hf : ∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
       (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ) (f i))
     (hinto : ∀ i,∀ x∈closedBall 3 (r i),(f i x).2≠0)
     (hd : Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r i)) (f j '' closedBall 3 (r j))))
     {η : ℝ} (hη : 0<η) :
     ∃ ε∈Ioc (0:ℝ) η,∃ g₀ : Ambient 3 → Ambient 3,∃ g : Fin k → Ambient 3 → Ambient 3,
       FormNeighborhoodEmbedding (closedBall 3 r₀) (fun _ => successorStandardForm 2)
         (degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)) g₀ ∧
       (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
         (degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)) (g i)) ∧
       (∀ i,Disjoint (g₀ '' closedBall 3 r₀) (g i '' closedBall 3 (r i))) ∧
       Pairwise (fun i j => Disjoint (g i '' closedBall 3 (r i)) (g j '' closedBall 3 (r j))) := by
   let U : Set CubicAmbient := {z | z.2≠0}
   have hU : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
   have hgU : ContDiffOn ℝ ∞ firstToDistinguished U := fun _ hx =>
     (firstToDistinguished_smoothAt hx).contDiffWithinAt
   let K : Set CubicAmbient := ⋃ i,f i '' closedBall 3 (r i)
   have hK : IsCompact K := by
     apply isCompact_iUnion
     intro i
     obtain ⟨W,_hW,hKW,hs,_he,_hf⟩ := hf i
     exact (closedBall_isCompact 3 (r i)).image_of_continuousOn (hs.continuousOn.mono hKW)
   have hKU : K⊆U := by
     intro x hx
     obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
     exact hinto i y hy
   have hK' : IsCompact (firstToDistinguished '' K) :=
     hK.image_of_continuousOn (hgU.continuousOn.mono hKU)
   have hzero : (0 : Fin 3 → ℂ)∉firstToDistinguished '' K := by
     rintro ⟨x,hx,he⟩
     have he0 := congrFun he 0
     exact inv_ne_zero (hKU hx) he0
   obtain ⟨V,W,hV,hW,hKV,h0W,hVW⟩ :=
     normal_separation hK'.isClosed isClosed_singleton (disjoint_singleton_right.mpr hzero)
   let T : Set CubicAmbient := U ∩ firstToDistinguished ⁻¹' V
   have hT : IsOpen T := hgU.continuousOn.isOpen_inter_preimage hU hV
   have hfT : ∀ i,MapsTo (f i) (closedBall 3 (r i)) T := by
     intro i x hx
     exact ⟨hinto i x hx,hKV ⟨f i x,mem_iUnion.mpr ⟨i,x,hx,rfl⟩,rfl⟩⟩
   obtain ⟨τ,hτ,hτη,houter⟩ := outer_packing_uniform_bubble_into (N := N) hm (by omega) t δ c hD hDL
     hT r f hf hfT hd hη
   obtain ⟨σ,hσ,_hση,hbubble⟩ := exists_uniform_cubic_bubble_ball m hAS hS hB hp hN hm.le
     t δ hc hD hD0 hr₀ hW (h0W (mem_singleton 0)) hτ
   let ε : ℝ := min τ σ/2
   have hε : 0<ε := half_pos (lt_min hτ hσ)
   have hετ : ε≤τ := (half_le_self (le_of_lt (lt_min hτ hσ))).trans (min_le_left _ _)
   have hεσ : ε≤σ := (half_le_self (le_of_lt (lt_min hτ hσ))).trans (min_le_right _ _)
   obtain ⟨g,hg,hgT,hdg⟩ := houter ε ⟨hε,hετ⟩
   obtain ⟨g₀,hg₀,hg₀W⟩ := hbubble ε ⟨hε,hεσ⟩
   obtain ⟨hgf,hdgf⟩ := postcompose_form_packing (fun i => closedBall 3 (r i))
     (fun _ => successorStandardForm 2)
     (cubicOuterBubbleForm (A := A) (B := B) L S (m+1) p N t δ c D ε)
     (degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε))
     hU firstToDistinguished hgU.contMDiffOn firstToDistinguished_isEmbedding (by
       intro z hz v w
       simp only [mfderiv_eq_fderiv]
       exact firstToDistinguished_curvature hAS hS hB (by omega) t δ c D hε.ne' hz v w)
     g hg (fun i x hx => (hgT i hx).1) hdg
   refine ⟨ε,⟨hε,hετ.trans hτη⟩,g₀,fun i => firstToDistinguished ∘ g i,hg₀,hgf,?_,hdgf⟩
   intro i
   exact hVW.symm.mono (image_subset_iff.mpr hg₀W)
     (image_subset_iff.mpr (fun x hx => (hgT i hx).2))

end PackingSufficiencySupport.CubicModel

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.CubicModel.exists_cubic_bubble_separated_bp240_oai := @OAI.PackingSufficiencySupport.CubicModel.exists_cubic_bubble_separated_bp240_oai
