-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:56:00.454252+00:00
-- url     : https://prove2.me/submissions/0cea1a11-24c1-4d87-9962-ac1d45f1f08c

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp017
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_supportedHolder_closed_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_ProperIndexZeroPath_endpoint_exists_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_adapted_line_continuation_data_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_packing_two_line_reduction_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_actual_small_normal_packing_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_actual_normal_transfer_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_polynomial_target_embedding_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_hasPacking_dim_ge_four_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_hasPacking_six_large_normalized_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_BanachSpace
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped BoundedContinuousFunction Topology ContDiff
open Set Filter
section

variable (X E : Type*) [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma graph_closed (α : ℝ) : IsClosed (graph X E α : Set (Ambient X E)) := by
  change IsClosed {u : Ambient X E | ∀ p : Pairs X, _}
  simp only [← Set.iInter_ofPred]
  apply isClosed_iInter
  intro p
  exact isClosed_eq
    ((BoundedContinuousFunction.evalCLM ℝ p).continuous.comp continuous_snd)
    ((((BoundedContinuousFunction.evalCLM ℝ p.val.1).continuous.comp continuous_fst).sub
      ((BoundedContinuousFunction.evalCLM ℝ p.val.2).continuous.comp continuous_fst)).const_smul _)

instance instCompleteSpaceSubtypeAmbientMemSubmoduleRealHolder (α : ℝ) [CompleteSpace E] : CompleteSpace (Holder X E α) :=
  (graph_closed X E α).completeSpace_coe

variable {X E}

variable {α : ℝ}

variable (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma jetGraph_closed (α : ℝ) : IsClosed (jetGraph (E := E) D α : Set (JetAmbient (E := E) D α)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu huv x
  have hv0 : Tendsto (fun n => valueCLM α (u n).1) atTop (𝓝 (valueCLM α v.1)) :=
    ((valueCLM α).continuous.comp continuous_fst).tendsto v |>.comp huv
  have hv1 : Tendsto (fun n => valueCLM α (u n).2) atTop (𝓝 (valueCLM α v.2)) :=
    ((valueCLM α).continuous.comp continuous_snd).tendsto v |>.comp huv
  have huni := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hv1
  exact hasFDerivAt_of_tendstoUniformly huni (fun n => hu n)
    (fun y => (BoundedContinuousFunction.evalCLM ℝ y).continuous.tendsto _ |>.comp hv0) x

instance instCompleteSpaceSubtypeJetAmbientMemSubmoduleRealCOneHolder (α : ℝ) [CompleteSpace E] : CompleteSpace (COneHolder (E := E) D α) :=
  (jetGraph_closed (E := E) D α).completeSpace_coe

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
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

theorem isBallEmbedding_id (n : ℕ) (r : ℝ) :
    IsBallEmbedding r (id : Ambient n → Ambient n) := by
  refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, contDiff_id.contDiffOn, ?_, ?_⟩
  · simpa only [id_eq] using (Topology.IsEmbedding.subtypeVal (p := fun x : Ambient n => x ∈ (Set.univ : Set (Ambient n))))
  · intro x _ v w
    simp

theorem matrix_J_pairing {n : ℕ} (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (i j : Fin n ⊕ Fin n) :
    (A.transpose * Matrix.J (Fin n) ℝ * A) i j =
      ∑ k, (A (Sum.inr k) i * A (Sum.inl k) j -
        A (Sum.inl k) i * A (Sum.inr k) j) := by
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Matrix.fromBlocks,
    Matrix.one_apply, Finset.sum_add_distrib, sub_eq_add_neg]

theorem det_eq_one_of_preserves_standardForm {n : ℕ}
    (L : Ambient n →ₗ[ℝ] Ambient n)
    (hL : ∀ v w, standardForm (L v) (L w) = standardForm v w) :
    LinearMap.det L = 1 := by
  let b := realBasis n
  let M := LinearMap.toMatrix b b L
  have pair (T : Ambient n →ₗ[ℝ] Ambient n) (i j : Fin n ⊕ Fin n) :
      ((LinearMap.toMatrix b b T).transpose * Matrix.J (Fin n) ℝ *
        LinearMap.toMatrix b b T) i j = - standardForm (T (b i)) (T (b j)) := by
    rw [matrix_J_pairing]
    simp only [LinearMap.toMatrix_apply, b, realBasis_repr]
    change (∑ k, ((T (realBasis n i) k).im * (T (realBasis n j) k).re -
      (T (realBasis n i) k).re * (T (realBasis n j) k).im)) =
      -(∑ k, ((T (realBasis n i) k).re * (T (realBasis n j) k).im -
        (T (realBasis n i) k).im * (T (realBasis n j) k).re))
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hM : M ∈ Matrix.symplecticGroup (Fin n) ℝ := by
    apply SymplecticGroup.mem_iff'.mpr
    ext i j
    change (M.transpose * Matrix.J (Fin n) ℝ * M) i j = _
    rw [show (M.transpose * Matrix.J (Fin n) ℝ * M) i j =
      -standardForm (L (b i)) (L (b j)) from pair L i j, hL]
    simpa using (pair LinearMap.id i j).symm
  rw [← LinearMap.det_toMatrix b L]
  exact SymplecticGroup.det_eq_one hM

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

theorem IsBallEmbedding.volume_image {n : ℕ} {r : ℝ}
    {f : Ambient n → Ambient n} (hf : IsBallEmbedding r f) :
    volume (f '' closedBall n r) = volume (closedBall n r) := by
  rcases hf with ⟨U, hU, hsub, hsmooth, hembed, hform⟩
  have hdiff : ∀ x ∈ closedBall n r,
      HasFDerivWithinAt f (fderiv ℝ f x) (closedBall n r) x := by
    intro x hx
    exact ((hsmooth.differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds (hsub hx))).hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn f (closedBall n r) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hembed.injective
      (show f (⟨x, hsub hx⟩ : U) = f (⟨y, hsub hy⟩ : U) from hxy))
  have hs := (closedBall_isClosed n r).measurableSet
  calc
    volume (f '' closedBall n r) = ∫⁻ x in closedBall n r,
        ENNReal.ofReal |(fderiv ℝ f x).det| :=
      (lintegral_abs_det_fderiv_eq_addHaar_image volume hs hdiff hinj).symm
    _ = ∫⁻ _ in closedBall n r, (1 : ℝ≥0∞) := by
      apply setLIntegral_congr_fun hs
      intro x hx
      have hd := det_eq_one_of_preserves_standardForm (fderiv ℝ f x).toLinearMap
        (hform x (hsub hx))
      simp [show (fderiv ℝ f x).det = 1 from hd]
    _ = volume (closedBall n r) := by simp

theorem capacity_smul {n : ℕ} (t : ℝ) (z : Ambient n) :
    capacity (t • z) = t ^ 2 * capacity z := by
  simp only [capacity, Pi.smul_apply, Complex.normSq_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, ← Finset.mul_sum]
  ring

theorem closedBall_eq_smul {n : ℕ} {r : ℝ} (hr : 0 < r) :
    closedBall n r = Real.sqrt r • closedBall n 1 := by
  ext z
  constructor
  · intro hz
    refine ⟨(Real.sqrt r)⁻¹ • z, ?_, ?_⟩
    · change capacity ((Real.sqrt r)⁻¹ • z) ≤ 1
      rw [capacity_smul, inv_pow, Real.sq_sqrt hr.le, ← div_eq_inv_mul,
        div_le_iff₀ hr]
      simpa [closedBall] using hz
    · simp [smul_smul, ne_of_gt (Real.sqrt_pos.mpr hr)]
  · rintro ⟨w, hw, rfl⟩
    change capacity (Real.sqrt r • w) ≤ r
    rw [capacity_smul, Real.sq_sqrt hr.le]
    simpa using mul_le_mul_of_nonneg_left hw hr.le

theorem volume_closedBall {n : ℕ} {r : ℝ} (hr : 0 < r) :
    volume (closedBall n r) = ENNReal.ofReal (r ^ n) * volume (closedBall n 1) := by
  rw [closedBall_eq_smul hr, Measure.addHaar_smul]
  have hd : Module.finrank ℝ (Ambient n) = 2 * n := by
    simp [Ambient, Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  rw [hd, pow_mul, Real.sq_sqrt hr.le, abs_of_pos (pow_pos hr n)]

theorem capacity_nonneg {n : ℕ} (z : Ambient n) : 0 ≤ capacity z :=
  mul_nonneg Real.pi_pos.le (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (z j))

theorem unitBall_volume_pos (n : ℕ) : 0 < volume (closedBall n 1) := by
  have hp : 0 < volume (openBall n 1) :=
    (openBall_isOpen n 1).measure_pos volume ⟨0, by simp [openBall]⟩
  exact hp.trans_le (measure_mono (fun _ hx => (show capacity _ < 1 from hx).le))

theorem unitBall_volume_ne_top (n : ℕ) : volume (closedBall n 1) ≠ ⊤ :=
  (closedBall_isCompact n 1).measure_lt_top.ne

theorem IsBallEmbedding.closedBall_continuousOn {n : ℕ} {r : ℝ}
    {f : Ambient n → Ambient n} (hf : IsBallEmbedding r f) :
    ContinuousOn f (closedBall n r) := by
  rcases hf with ⟨U, _, hsub, hsmooth, _, _⟩
  exact hsmooth.continuousOn.mono hsub

theorem IsBallEmbedding.isCompact_image {n : ℕ} {r : ℝ}
    {f : Ambient n → Ambient n} (hf : IsBallEmbedding r f) :
    IsCompact (f '' closedBall n r) :=
  (closedBall_isCompact n r).image_of_continuousOn hf.closedBall_continuousOn

theorem HasPacking.exists_smaller_target {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hR : 0 < R) (hp : HasPacking n k R r) :
    ∃ σ, 0 < σ ∧ σ < R ∧ HasPacking n k σ r := by
  rcases hp with ⟨f, hf, htarget, hdisj⟩
  let S : Set (Ambient n) := ⋃ i, f i '' closedBall n (r i)
  have hc : IsCompact (insert 0 S) :=
    (isCompact_iUnion (fun i => (hf i).isCompact_image)).insert 0
  obtain ⟨z, hz, hmax⟩ := hc.exists_isMaxOn (Set.insert_nonempty 0 S)
    (continuous_capacity n).continuousOn
  have hS : insert (0 : Ambient n) S ⊆ openBall n R := by
    intro y hy
    rcases hy with rfl | hy
    · simpa [openBall] using hR
    · rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
      exact htarget i hi
  have hzR : capacity z < R := hS hz
  refine ⟨(capacity z + R) / 2, ?_, ?_, f, hf, ?_, hdisj⟩
  · linarith [capacity_nonneg z]
  · linarith
  · intro i y hy
    have hm : capacity y ≤ capacity z := hmax (Set.mem_insert_of_mem 0
      (Set.mem_iUnion.mpr ⟨i, hy⟩))
    change capacity y < (capacity z + R) / 2
    linarith

theorem HasPacking.volume_le {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hR : 0 < R) (hr : ∀ i, 0 < r i) (hp : HasPacking n k R r) :
    ∑ i, (r i) ^ n ≤ R ^ n := by
  rcases hp with ⟨f, hf, htarget, hdisj⟩
  have hm : volume (⋃ i, f i '' closedBall n (r i)) ≤ volume (closedBall n R) := by
    apply measure_mono
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    exact (show capacity z < R from htarget i hi).le
  rw [measure_iUnion hdisj (fun i => (hf i).isCompact_image.measurableSet),
    tsum_fintype] at hm
  simp_rw [(hf _).volume_image, volume_closedBall (hr _)] at hm
  rw [volume_closedBall hR, ← Finset.sum_mul] at hm
  have he := (ENNReal.mul_le_mul_iff_left (unitBall_volume_pos n).ne'
    (unitBall_volume_ne_top n)).mp hm
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg (hr i).le n)] at he
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hR.le n)).mp he

theorem HasPacking.volume_lt {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hn : 0 < n) (hR : 0 < R) (hr : ∀ i, 0 < r i)
    (hp : HasPacking n k R r) : ∑ i, (r i) ^ n < R ^ n := by
  obtain ⟨σ, hσ, hσR, hpσ⟩ := hp.exists_smaller_target hR
  exact (hpσ.volume_le hσ hr).trans_lt (pow_lt_pow_left₀ hσR hσ.le hn.ne')

theorem IsBallEmbedding.dilate {n : ℕ} {r t : ℝ} {f : Ambient n → Ambient n}
    (hf : IsBallEmbedding r f) (ht : t ≠ 0) :
    IsBallEmbedding (t ^ 2 * r) (fun z => t • f (t⁻¹ • z)) := by
  let e := dilation n t ht
  rcases hf with ⟨U, hU, hsub, hsmooth, hembed, hform⟩
  have hmaps : Set.MapsTo e.symm (e '' U) U := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  refine ⟨e '' U, e.isOpenMap _ hU, ?_, ?_, ?_, ?_⟩
  · intro z hz
    refine ⟨e.symm z, hsub ?_, e.apply_symm_apply z⟩
    change capacity (t⁻¹ • z) ≤ r
    rw [capacity_smul, inv_pow, ← div_eq_inv_mul, div_le_iff₀ (sq_pos_of_ne_zero ht)]
    simpa [closedBall, mul_comm] using hz
  · exact (hsmooth.comp e.symm.contDiff.contDiffOn hmaps).const_smul t
  · exact e.toHomeomorph.isEmbedding.comp (hembed.comp (e.toHomeomorph.image U).symm.isEmbedding)
  · intro z hz v w
    have hd := ((hsmooth.differentiableOn (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
      (hU.mem_nhds (hmaps hz))).hasFDerivAt
    have hchain := (e.hasFDerivAt.comp z (hd.comp z e.symm.hasFDerivAt))
    have heq : e.toContinuousLinearMap.comp
        ((fderiv ℝ f (e.symm z)).comp e.symm.toContinuousLinearMap) =
        fderiv ℝ f (e.symm z) := by
      apply ContinuousLinearMap.ext
      intro a
      change t • (fderiv ℝ f (e.symm z) (t⁻¹ • a)) = _
      rw [map_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]
    rw [heq] at hchain
    have hdg : fderiv ℝ (fun z => t • f (t⁻¹ • z)) z = fderiv ℝ f (e.symm z) :=
      hchain.fderiv
    rw [hdg]
    exact hform _ (hmaps hz) v w

theorem HasPacking.dilate {n k : ℕ} {R t : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) (ht : t ≠ 0) :
    HasPacking n k (t ^ 2 * R) (fun i => t ^ 2 * r i) := by
  rcases hp with ⟨f, hf, htarget, hdisj⟩
  have hsource {a : ℝ} {z : Ambient n} (hz : z ∈ closedBall n (t ^ 2 * a)) :
      t⁻¹ • z ∈ closedBall n a := by
    change capacity (t⁻¹ • z) ≤ a
    rw [capacity_smul, inv_pow, ← div_eq_inv_mul, div_le_iff₀ (sq_pos_of_ne_zero ht)]
    simpa [closedBall, mul_comm] using hz
  refine ⟨fun i z => t • f i (t⁻¹ • z), fun i => (hf i).dilate ht, ?_, ?_⟩
  · intro i z hz
    rcases hz with ⟨x, hx, rfl⟩
    change capacity (t • f i (t⁻¹ • x)) < t ^ 2 * R
    rw [capacity_smul]
    exact mul_lt_mul_of_pos_left (htarget i ⟨_, hsource hx, rfl⟩) (sq_pos_of_ne_zero ht)
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have heq' : f j (t⁻¹ • y) = f i (t⁻¹ • x) := by
      have := congrArg (fun z : Ambient n => t⁻¹ • z) heq
      simpa [smul_smul, ht] using this
    exact Set.disjoint_left.mp (hdisj i j hij)
      ⟨_, hsource hx, rfl⟩ ⟨_, hsource hy, heq'⟩

theorem hasPacking_normalize {n k : ℕ} {R : ℝ} {r : Fin k → ℝ} (hR : 0 < R) :
    HasPacking n k R r ↔ HasPacking n k 1 (fun i => r i / R) := by
  constructor
  · intro hp
    have ht : Real.sqrt R⁻¹ ≠ 0 := (Real.sqrt_pos.mpr (inv_pos.mpr hR)).ne'
    have h := hp.dilate ht
    simpa only [Real.sq_sqrt (inv_nonneg.mpr hR.le), inv_mul_cancel₀ hR.ne',
      div_eq_inv_mul] using h
  · intro hp
    have ht : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
    have h := hp.dilate ht
    simpa only [Real.sq_sqrt hR.le, mul_one, mul_div_cancel₀ _ hR.ne'] using h

theorem hasPacking_one_iff {n : ℕ} {R r : ℝ} (hn : 0 < n)
    (hR : 0 < R) (hr : 0 < r) :
    HasPacking n 1 R (fun _ => r) ↔ r < R := by
  constructor
  · intro hp
    have h := hp.volume_lt hn hR (fun _ => hr)
    simp only [Fin.sum_univ_one] at h
    exact lt_of_pow_lt_pow_left₀ n hR.le h
  · intro h
    refine ⟨fun _ => id, fun _ => isBallEmbedding_id n r, ?_, ?_⟩
    · intro i z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact lt_of_le_of_lt hx h
    · intro i j hij
      exact False.elim (hij (Subsingleton.elim i j))

end PackingSufficiencySupport
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RearrangementBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking
open scoped ContDiff ENNReal Pointwise Classical

theorem hasPacking_iff_support {n k : ℕ} {R : ℝ} {r : Fin k → ℝ} :
    HasPacking n k R r ↔ PackingSufficiencySupport.HasPacking n k R r := by
  constructor
  · rintro ⟨U,f,h,hdis⟩
    refine ⟨f,?_,?_,hdis⟩
    · intro i
      exact ⟨U i,(h i).2.1.1,(h i).1,(h i).2.1.2⟩
    · intro i
      exact Set.image_subset_iff.mpr (h i).2.2
  · rintro ⟨f,hf,ht,hdis⟩
    choose U hUopen hUsub hUs hUemb hUsymp using hf
    refine ⟨U,f,?_,hdis⟩
    intro i
    exact ⟨hUsub i,⟨hUopen i,hUs i,hUemb i,hUsymp i⟩,Set.image_subset_iff.mp (ht i)⟩

theorem HasPacking.volume_lt {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hn : 0 < n) (hR : 0 < R) (hr : ∀ i, 0 < r i)
    (hp : HasPacking n k R r) : (∑ i, r i ^ n) < R ^ n :=
  (hasPacking_iff_support.mp hp).volume_lt hn hR hr

end HigherDimensionalBallPacking

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
-- module Solutions.OAIQ240_BP.BallPacking_Holder_NonlinearCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne_2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_2
local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_ra5c55c_1 : NormedAddCommGroup (COne D E →L[ℝ] COne D F) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_ra5c55c_1 : NormedSpace ℝ (COne D E →L[ℝ] COne D F) := ContinuousLinearMap.toNormedSpace
instance instCompleteSpaceSubtypeAmbientMemSubmoduleRealHMapSupportedHolder (K : Set D) [CompleteSpace E] : CompleteSpace (supportedHolder (E := E) K) :=
  (supportedHolder_closed_bp240 K).completeSpace_coe

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance markedAffineInst1_ra5c55c_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_ra5c55c_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_ra5c55c_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_ra5c55c_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma markedModel_closed (K : Set ℂ) : IsClosed (markedModel (E := E) K : Set (COne ℂ E)) :=
  (jetEval (E := E) 0).isClosed_ker.inter ((supportedHolder_closed_bp240 K).preimage standardJetCR.continuous)

instance instCompleteSpaceSubtypeJetAmbientComplexHDivRealOfNatMemSubmoduleCOneMarkedModel (K : Set ℂ) : CompleteSpace (markedModel (E := E) K) :=
  (markedModel_closed K).completeSpace_coe



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
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

theorem rational_small_slack {ι : Type*} [Fintype ι] (n : ℕ) (r : ι → ℝ)
    (hhalf : ∀ i, r i < 1/2) (hvol : ∑ i,r i^n < 1) :
    ∃ q : ι → ℚ, (∀ i, r i < q i) ∧ (∀ i, (q i : ℝ) < 1/2) ∧
      ∑ i,(q i : ℝ)^n < 1 := by
  let U : Set (ι → ℝ) := {s | (∀ i,s i<1/2) ∧ ∑ i,s i^n<1}
  have hU : IsOpen U := by
    have ha : IsOpen {s : ι → ℝ | ∀ i,s i<1/2} := by
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
    exact ha.inter (isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).pow n)
      continuous_const)
  obtain ⟨q,hq,hUq⟩ := exists_rational_above_in_open hU (show r∈U from ⟨hhalf,hvol⟩)
  exact ⟨q,hq,hUq⟩

end PackingSufficiencySupport

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

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open Hamiltonian MomentPolytope

 theorem actual_small_polynomial_packing (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+3)<1) :
    ∃ d t : ℝ,0<d ∧ d<1/2 ∧ 0<t ∧
      ∃ f : Fin N → Ambient (m+3) → Affine (m+2),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+3) (r' i))
          (fun _ => successorStandardForm (m+2))
          (normalAmbientForm (parameters m) (1/Real.pi) d t) (f i)) ∧
        Pairwise (fun i j => Disjoint (f i '' closedBall (m+3) (r' i))
          (f j '' closedBall (m+3) (r' j))) := by
  classical
  obtain ⟨h,d,hrh,hhd,hdhalf,ℓ,φ,hφ,hφK,hdisj⟩ :=
    actual_small_normal_packing_bp240 m r r' hr hr' hrr hhalf hvol
  let K : Set (NormalSpace (parameters m)) := ⋃ i,φ i '' closedBall (m+3) (r' i)
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hφ i
    exact (closedBall_isCompact (m+3) (r' i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hhdR : (h:ℝ)<d := by exact_mod_cast hhd
  have hd : 0<(d:ℝ) := by
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    exact ((hr i).trans (hrh i)).trans hhdR
  have hKd (p : NormalSpace (parameters m)) (hp : p∈K) : phaseSq p.2<(d:ℝ)/Real.pi := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    have hm := (interior_subset (hφK i hx)).2.2
    have he : (∑ j,planeMoments (φ i x).2 j)=Real.pi*phaseSq (φ i x).2 := by
      simp only [planeMoments,radialArea,radiusSq,phaseSq,phaseDot_apply,pow_two,← Finset.mul_sum]
    rw [he] at hm
    exact (lt_div_iff₀ Real.pi_pos).mpr (by simpa only [mul_comm] using hm.trans_lt hhdR)
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,hgform⟩ :=
    exists_actual_normal_transfer_bp240 (parameters m) hd hdhalf hK hKd
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall (m+3) (r' i))
    (fun _ => successorStandardForm (m+2))
    (globalHorizontalCoupling phaseArea (normalHorizontalPrimitive (parameters m) 2 ∘ planeMoments))
    (normalAmbientForm (parameters m) (1/Real.pi) d t)
    hW g hg.contMDiffOn hgemb hgform φ hφ
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hdisj
  exact ⟨d,t,hd,hdhalf,ht,fun i => g ∘ φ i,hf,hdj⟩

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open Hamiltonian DiagonalQuadrics DiagonalQuadrics.Explicit
open CubicModel

 theorem hasPacking_small_enlarged (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+3)<1) : HasPacking (m+3) N 1 r' := by
  obtain ⟨d,t,hd,hdhalf,_ht,φ,hφ,hdisj⟩ :=
    actual_small_polynomial_packing m r r' hr hr' hrr hhalf hvol
  obtain ⟨g,hg,hgemb,hgmem,hgform⟩ :=
    exists_polynomial_target_embedding_bp240 (parameters m) t
      (one_div_pos.mpr Real.pi_pos) hd.le hdhalf
  have hform (x : Affine (m+2)) (_hx : x∈(univ : Set (Affine (m+2)))) (v w) :
      successorStandardForm (m+2) (mfderiv 𝓘(ℝ,Affine (m+2)) 𝓘(ℝ,Ambient (m+3)) g x v)
        (mfderiv 𝓘(ℝ,Affine (m+2)) 𝓘(ℝ,Ambient (m+3)) g x w)=
      normalAmbientForm (parameters m) (1/Real.pi) d t x v w := by
    rw [mfderiv_eq_fderiv]
    exact (successorStandardForm_apply _ _ _).trans (hgform x v w)
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall (m+3) (r' i))
    (fun _ => successorStandardForm (m+2))
    (normalAmbientForm (parameters m) (1/Real.pi) d t)
    (fun _ => successorStandardForm (m+2)) isOpen_univ g hg.contMDiff.contMDiffOn
    (hgemb.comp Topology.IsEmbedding.subtypeVal) hform φ hφ
    (fun _ _ _ => mem_univ _) hdisj
  refine ⟨fun i => g ∘ φ i,fun i => isBallEmbedding_iff_formNeighborhoodEmbedding.mpr (hf i),?_,?_⟩
  · intro i y hy
    obtain ⟨x,_hx,rfl⟩ := hy
    simpa only [mul_one_div_cancel Real.pi_ne_zero,Function.comp_apply] using hgmem (φ i x)
  · intro i j hij
    exact hdj hij

 theorem hasPacking_small_normalized {n N : ℕ} (hn : 3≤n) (hN : 1≤N)
    (r : Fin N → ℝ) (hr : ∀ i,0 < r i) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^n<1) : HasPacking n N 1 r := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  have hs : 3+m=m+3 := Nat.add_comm _ _
  simp only [hs] at hvol ⊢
  let : NeZero N := ⟨by omega⟩
  obtain ⟨q,hq,hqhalf,hqvol⟩ := rational_small_slack (m+3) r hhalf hvol
  exact hasPacking_small_enlarged m (fun i => (q i:ℝ)) r
    (fun i => (hr i).trans (hq i)) (fun i => (hr i).le) hq hqhalf hqvol

 theorem HasPacking.reindex {n N : ℕ} {R : ℝ} {r : Fin N → ℝ}
    (hp : HasPacking n N R r) (e : Equiv.Perm (Fin N)) :
    HasPacking n N R (r ∘ e) := by
  obtain ⟨f,hf,hm,hd⟩ := hp
  exact ⟨f ∘ e,fun i => hf (e i),fun i => hm (e i),
    fun i j hij => hd (e i) (e j) (fun h => hij (e.injective h))⟩

 theorem hasPacking_six_normalized {N : ℕ} (hN : 1≤N)
    (r : Fin N → ℝ) (hr : ∀ i,0 < r i)
    (hvol : ∑ i,r i^3<1) (hpair : ∀ i j,i≠j → r i+r j<1) : HasPacking 3 N 1 r := by
  classical
  by_cases hsmall : ∀ i,r i<1/2
  · exact hasPacking_small_normalized (by omega) hN r hr hsmall hvol
  obtain ⟨j,hj⟩ := not_forall.mp hsmall
  have hj : 1/2 ≤ r j := le_of_not_gt hj
  cases N with
  | zero => omega
  | succ K =>
    cases K with
    | zero =>
      have heqr : r=(fun _ => r 0) := funext fun i => congrArg r (Fin.eq_zero i)
      rw [heqr] at hvol ⊢
      apply (hasPacking_one_iff (by omega) zero_lt_one (hr 0)).mpr
      exact lt_of_pow_lt_pow_left₀ 3 zero_le_one (by simpa using hvol)
    | succ K =>
      let e : Equiv.Perm (Fin (K+1+1)) := Equiv.swap 0 j
      have hrvol : ∑ i,(r (e i))^3<1 := by
        rw [show (∑ i,r (e i)^3)=(∑ i,r i^3) from Equiv.sum_comp e (fun i => r i^3)]
        exact hvol
      have hrlarge : 1/2≤(r ∘ e) 0 := by
        simpa only [Function.comp_apply,e,Equiv.swap_apply_left] using hj
      have hp := hasPacking_six_large_normalized_bp240 (r ∘ e) (fun i => hr (e i))
        hrlarge hrvol (fun i j hij => hpair (e i) (e j) (fun h => hij (e.injective h)))
      have hh := hp.reindex e.symm
      simpa only [Function.comp_def,Equiv.apply_symm_apply] using hh

 theorem hasPacking_of_inequalities {n N : ℕ} (hn : 3≤n) (hN : 1≤N)
    {R : ℝ} (hR : 0<R) (r : Fin N → ℝ) (hr : ∀ i,0 < r i)
    (hvol : ∑ i,r i^n<R^n) (hpair : ∀ i j,i≠j → r i+r j<R) : HasPacking n N R r := by
  by_cases hfour : 4≤n
  · exact hasPacking_dim_ge_four_bp240 hfour hN hR r hr hvol hpair
  have hn3 : n=3 := by omega
  subst n
  apply (hasPacking_normalize hR).mpr
  apply hasPacking_six_normalized hN (fun i => r i/R) (fun i => div_pos (hr i) hR)
  · simp only [div_pow,← Finset.sum_div]
    exact (div_lt_one (pow_pos hR 3)).mpr hvol
  · intro i j hij
    rw [← add_div]
    exact (div_lt_one hR).mpr (hpair i j hij)

end PackingSufficiencySupport

namespace HigherDimensionalBallPacking
open scoped ContDiff Topology
open Set Function
open scoped BigOperators

 theorem HasPacking.subfamily {n k ℓ : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) (e : Fin ℓ ↪ Fin k) :
    HasPacking n ℓ R (r ∘ e) := by
   obtain ⟨U,f,hf,hd⟩ := hp
   exact ⟨U ∘ e,f ∘ e,fun i => hf (e i),
     fun i j hij => hd (e i) (e j) (fun he => hij (e.injective he))⟩

 theorem HasPacking.two_balls {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) {i j : Fin k} (hij : i≠j) :
    HasPacking n 2 R ![r i,r j] := by
   let e : Fin 2 ↪ Fin k := ⟨![i,j],by
     intro a b he
     fin_cases a <;> fin_cases b
     · rfl
     · exact False.elim (hij he)
     · exact False.elim (hij he.symm)
     · rfl⟩
   have he : r ∘ e=![r i,r j] := by
     funext a
     fin_cases a <;> rfl
   simpa only [he] using hp.subfamily e

 theorem HasPacking.two_balls_smaller_target {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) (hR : 0<R) {i j : Fin k} (hij : i≠j) :
    ∃ σ,0<σ ∧ σ<R ∧ HasPacking n 2 σ ![r i,r j] := by
   obtain ⟨σ,hσ,hσR,hpσ⟩ := (hasPacking_iff_support.mp hp).exists_smaller_target hR
   exact ⟨σ,hσ,hσR,(hasPacking_iff_support.mpr hpσ).two_balls hij⟩

 theorem HasPacking.unit_pair_counterexample {n k : ℕ} {R : ℝ} {r : Fin k → ℝ}
    (hp : HasPacking n k R r) (hR : 0<R) (hr : ∀ i,0 < r i)
    {i j : Fin k} (hij : i≠j) (hbad : R ≤ r i+r j) :
    ∃ a b : ℝ,0<a ∧ 0<b ∧ 1<a+b ∧ HasPacking n 2 1 ![a,b] := by
   obtain ⟨σ,hσ,hσR,hpσ⟩ := hp.two_balls_smaller_target hR hij
   have hp' := (PackingSufficiencySupport.hasPacking_normalize hσ).mp
     (hasPacking_iff_support.mp hpσ)
   have he : (fun l : Fin 2 => (![r i,r j] : Fin 2 → ℝ) l/σ)=![r i/σ,r j/σ] := by
     funext l
     fin_cases l <;> rfl
   refine ⟨r i/σ,r j/σ,div_pos (hr i) hσ,div_pos (hr j) hσ,?_,?_⟩
   · rw [←add_div]
     exact (one_lt_div hσ).mpr (hσR.trans_le hbad)
   · apply hasPacking_iff_support.mpr
     simpa only [he] using hp'

theorem hasPacking_of_inequalities {n k : ℕ} (hn : 3≤n) (hk : 1≤k)
    {R : ℝ} {r : Fin k → ℝ} (hR : 0<R) (hr : ∀ i,0 < r i)
    (h : PackingInequalities n k R r) : HasPacking n k R r := by
  exact hasPacking_iff_support.mpr
    (PackingSufficiencySupport.hasPacking_of_inequalities hn hk hR r hr h.1 h.2)

end HigherDimensionalBallPacking
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_TwoBallBound
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking
open Rigidity Rigidity.HolderCompletion

 theorem adapted_affine_line {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    (hinside : tsupport (fun x => J x-standardJ n)⊆openBall n 1)
    (p q : Phase n) (hpq : p≠q) : ∃ u,AffineLineCurve J p q u := by
  let : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
  let : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
  let : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
  let : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
  obtain ⟨β,β₁,M,δ,hpath,hend⟩ := adapted_line_continuation_data_bp240 hJs hJ hJc hinside p q hpq
  let : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) β.rOut)) := inferInstance
  let : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) β.rOut)) := inferInstance
  let : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) β.rOut)) := inferInstance
  let : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) β.rOut)) := inferInstance
  obtain ⟨w,hw,hz⟩ := hpath.endpoint_exists_bp240
  exact ⟨_,hend w hw hz⟩

 theorem normalized_two_ball_bound (n : ℕ) (_ : 3≤n)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) (hp : HasPacking n 2 1 ![a,b]) : a+b≤1 := by
  obtain ⟨J,p,q,hJs,hJ,hJc,hinside,hpq,harea⟩ := packing_two_line_reduction_bp240 ha hb hp
  obtain ⟨u,hu⟩ := adapted_affine_line hJs hJ hJc hinside p q hpq
  exact harea u hu

end HigherDimensionalBallPacking

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking

 theorem HasPacking.strict_pair_bound {n k : ℕ} (hn : 3≤n)
    {R : ℝ} {r : Fin k → ℝ} (hR : 0<R) (hr : ∀ i,0 < r i)
    (hp : HasPacking n k R r) (i j : Fin k) (hij : i≠j) : r i+r j<R := by
  by_contra hbad
  obtain ⟨a,b,ha,hb,hab,hpab⟩ := hp.unit_pair_counterexample hR hr hij (le_of_not_gt hbad)
  exact (not_le_of_gt hab) (normalized_two_ball_bound n hn a b ha hb hpab)

 theorem main_theorem_oai (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (R : ℝ) (r : Fin k → ℝ) (hR : 0 < R) (hr : ∀ i, 0 < r i) :
    HasPacking n k R r ↔ PackingInequalities n k R r := by
  constructor
  · intro hp
    exact ⟨hp.volume_lt (by omega) hR hr,hp.strict_pair_bound hn hR hr⟩
  · exact hasPacking_of_inequalities hn hk hR hr

end HigherDimensionalBallPacking

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.main_theorem_oai := @OAI.HigherDimensionalBallPacking.main_theorem_oai
