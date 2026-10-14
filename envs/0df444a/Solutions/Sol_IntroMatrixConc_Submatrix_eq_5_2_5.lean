-- Prove2me | solution 1 for IntroMatrixConc.Submatrix.eq_5_2_5
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T04:49:23.356039+00:00
-- url     : https://prove2.me/submissions/048a430f-9d72-45f1-8074-560239938bb3

import Mathlib
import Definitions.Def_IntroMatrixConc_Submatrix_Defs
import Theorems.Thm_IntroMatrixConc_Submatrix_eq_5_1_8
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TroppMatrixConcentration IntroMatrixConc.Submatrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace TroppColumnMax

noncomputable def oneBool (x : ℝ) : Bool := if x = 1 then true else false

def boolReal (b : Bool) : ℝ := if b then 1 else 0

lemma oneBool_meas : Measurable oneBool := by
  exact Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const

lemma boolReal_oneBool (x : ℝ) (hx : x = 0 ∨ x = 1) : boolReal (oneBool x) = x := by
  rcases hx with rfl | rfl <;> simp [oneBool, boolReal]

lemma finite_integrable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (ν : Measure A) [IsFiniteMeasure ν] (f : A → ℝ) : Integrable f ν := by
  classical
  apply (integrable_const (∑ a : A, ‖f a‖)).mono' (measurable_of_finite f).aestronglyMeasurable
  exact Eventually.of_forall (fun a => Finset.single_le_sum (fun b hb => norm_nonneg _) (Finset.mem_univ a))

lemma finite_comp_integrable {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (μ : Measure Ω) [IsFiniteMeasure μ]
    (v : Ω → A) (hv : Measurable v) (f : A → ℝ) : Integrable (fun ω => f (v ω)) μ := by
  have hi := finite_integrable (μ.map v) f
  exact (integrable_map_measure (measurable_of_finite f).aestronglyMeasurable hv.aemeasurable).mp hi

lemma bernoulli_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (q : ℝ) (h : IsBernoulli μ g q) : Integrable g μ := by
  apply (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
  filter_upwards [h.1] with ω hω
  rcases hω with he | he <;> simp [he]

lemma bernoulli_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (q : ℝ) (h : IsBernoulli μ g q) : (∫ ω, g ω ∂μ) = q := by
  have hs : MeasurableSet {ω | g ω = 1} := hg (measurableSet_singleton 1)
  have he : g =ᵐ[μ] ({ω | g ω = 1}.indicator (fun _ => (1 : ℝ))) := by
    filter_upwards [h.1] with ω hω
    rcases hω with he | he <;> simp [he]
  rw [integral_congr_ae he, integral_indicator_const _ hs]
  simpa only [smul_eq_mul, mul_one, Measure.real] using h.2

lemma max_eq_norm_of_psd {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hp : A.PosSemidef) : lambdaMax A = ‖A‖ := by
  unfold lambdaMax
  have hf : (spectrum ℝ A).Finite := by
    rw [hp.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have hn := CStarAlgebra.norm_mem_spectrum_of_nonneg hp.nonneg
  apply le_antisymm
  · apply csSup_le ⟨‖A‖, hn⟩
    intro x hx
    have hx' := (spectrum.algebraMap_mem_iff ℂ).mpr hx
    have hb := spectrum.norm_le_norm_of_mem hx'
    have hb' : |x| ≤ ‖A‖ := by simpa using hb
    exact (le_abs_self x).trans hb'
  · exact le_csSup hf.bddAbove hn

lemma min_nonneg_of_psd {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hp : A.PosSemidef) : 0 ≤ lambdaMin A := by
  unfold lambdaMin
  rw [hp.isHermitian.spectrum_real_eq_range_eigenvalues]
  apply le_csInf (Set.range_nonempty _)
  rintro x ⟨i,rfl⟩
  exact (hp.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp hp) i

lemma diagonal_psd {n : ℕ} (v : Fin n → ℝ) (hv : ∀ k, 0 ≤ v k) :
    (Matrix.diagonal (fun k => (v k : ℂ))).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro k
  exact_mod_cast hv k

lemma diagonal_max {n : ℕ} [NeZero n] (v : Fin n → ℝ) (hv : ∀ k, 0 ≤ v k) :
    lambdaMax (Matrix.diagonal (fun k => (v k : ℂ))) = ⨆ k, v k := by
  rw [max_eq_norm_of_psd _ (diagonal_psd v hv), Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonempty (fun k => (v k : ℂ))).mpr
    intro k
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hv k)]
    exact le_ciSup (Set.finite_range v).bddAbove k
  · apply ciSup_le
    intro k
    have h := norm_le_pi_norm (fun k => (v k : ℂ)) k
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hv k)] using h

def rowDiagonal {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ) (j : Fin d) :
    Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun k => (‖B j k‖ ^ 2 : ℝ))

lemma rowDiagonal_psd {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ) (j : Fin d) :
    (rowDiagonal B j).PosSemidef := diagonal_psd _ (fun k => sq_nonneg _)

lemma rowDiagonal_bound {d n : ℕ} [NeZero d] [NeZero n]
    (B : Matrix (Fin d) (Fin n) ℂ) (j : Fin d) :
    lambdaMax (rowDiagonal B j) ≤ maxEntrySq B := by
  rw [rowDiagonal, diagonal_max _ (fun k => sq_nonneg _)]
  unfold maxEntrySq
  exact le_ciSup (Set.finite_range (fun j : Fin d => ⨆ k : Fin n, ‖B j k‖ ^ 2)).bddAbove j

lemma entry_nonneg {d n : ℕ} [NeZero d] [NeZero n]
    (B : Matrix (Fin d) (Fin n) ℂ) : 0 ≤ maxEntrySq B := by
  unfold maxEntrySq
  have h (j : Fin d) : 0 ≤ ⨆ k : Fin n, ‖B j k‖ ^ 2 :=
    (sq_nonneg ‖B j ⟨0, NeZero.pos n⟩‖).trans (le_ciSup (Set.finite_range (fun k : Fin n => ‖B j k‖ ^ 2)).bddAbove (⟨0, NeZero.pos n⟩ : Fin n))
  exact (h ⟨0, NeZero.pos d⟩).trans (le_ciSup (Set.finite_range (fun j : Fin d => ⨆ k : Fin n, ‖B j k‖ ^ 2)).bddAbove (⟨0, NeZero.pos d⟩ : Fin d))

lemma rowDiagonal_sum {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ) :
    (∑ j, rowDiagonal B j) = Matrix.diagonal (fun k => ((∑ j, ‖B j k‖ ^ 2 : ℝ) : ℂ)) := by
  ext k l
  by_cases h : k = l <;> simp [rowDiagonal, Matrix.diagonal, h, Matrix.sum_apply]

lemma selection_diagonal {Ω : Type*} {d n : ℕ} [NeZero n]
    (B : Matrix (Fin d) (Fin n) ℂ) (δ : Fin d → Ω → ℝ) (ω : Ω)
    (hδ : ∀ j, δ j ω = 0 ∨ δ j ω = 1) :
    maxSelectedColumnSq B δ ω = lambdaMax (∑ j, δ j ω • rowDiagonal B j) := by
  have he : (∑ j, δ j ω • rowDiagonal B j) =
      Matrix.diagonal (fun k => ((∑ j, ‖selectedRows B δ ω j k‖ ^ 2 : ℝ) : ℂ)) := by
    ext k l
    by_cases h : k = l
    · subst l
      simp only [Matrix.sum_apply, Matrix.smul_apply, rowDiagonal, Matrix.diagonal_apply_eq]
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hc : selectedRows B δ ω j k = (δ j ω : ℂ) * B j k := Matrix.diagonal_mul _ _ _ _
      rcases hδ j with he | he <;> simp [hc, he]
    · simp [Matrix.sum_apply, Matrix.smul_apply, rowDiagonal, Matrix.diagonal, h]
  rw [he, diagonal_max _ (fun k => Finset.sum_nonneg (fun j hj => sq_nonneg _))]
  rfl

end TroppColumnMax
open TroppColumnMax

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d n : ℕ} [NeZero d] [NeZero n]
    (B : Matrix (Fin d) (Fin n) ℂ) (δ : Fin d → Ω → ℝ) (p : ℝ)
    (hp0 : 0 ≤ p) (hpd : p ≤ (d : ℝ))
    (hδMeas : ∀ j, Measurable (δ j)) (hIndep : iIndepFun δ μ)
    (hδ : ∀ j, IsBernoulli μ (δ j) (p / (d : ℝ))) :
    Integrable (fun ω => maxSelectedColumnSq B δ ω) μ ∧
    (∫ ω, maxSelectedColumnSq B δ ω ∂μ) ≤
      (1.72 : ℝ) * (p / (d : ℝ)) * maxColumnSq B +
        Real.log n * maxEntrySq B := by
  classical
  let q := p / (d : ℝ)
  have hq : 0 ≤ q := div_nonneg hp0 (Nat.cast_nonneg d)
  let X : Fin d → Ω → Matrix (Fin n) (Fin n) ℂ := fun j ω => δ j ω • rowDiagonal B j
  let Y := fun ω => ∑ j, X j ω
  have hXm : ∀ j, Measurable (X j) := by intro j; unfold X; fun_prop
  have hXi : ∀ j, Integrable (X j) μ := fun j =>
    (bernoulli_integrable μ _ (hδMeas j) q (hδ j)).smul_const _
  have hXh : ∀ j, ∀ᵐ ω ∂μ, (X j ω).IsHermitian := by
    intro j
    filter_upwards [(hδ j).1] with ω he
    rcases he with he | he
    · simp [X, he]
    · simpa [X, he] using (rowDiagonal_psd B j).isHermitian
  have hXb : ∀ j, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (X j ω) ∧ lambdaMax (X j ω) ≤ maxEntrySq B := by
    intro j
    filter_upwards [(hδ j).1] with ω he
    rcases he with he | he
    · simpa [X, he, lambdaMin, lambdaMax, spectrum.zero_eq] using entry_nonneg B
    · simpa [X, he] using And.intro (min_nonneg_of_psd _ (rowDiagonal_psd B j)) (rowDiagonal_bound B j)
  have hInd : iIndepFun X μ := hIndep.comp (fun j t => t • rowDiagonal B j) (by intro j; fun_prop)
  have H := IntroMatrixConc.Submatrix.eq_5_1_8 μ X (maxEntrySq B) (entry_nonneg B) hXm hInd hXh hXb
  change Integrable (fun ω => lambdaMax (Y ω)) μ ∧
    (∫ ω, lambdaMax (Y ω) ∂μ) ≤ (1.72 : ℝ) * lambdaMax (∫ ω, Y ω ∂μ) + maxEntrySq B * Real.log n at H
  have heY : (∫ ω, Y ω ∂μ) = q • (∑ j, rowDiagonal B j) := by
    unfold Y
    rw [integral_finset_sum _ (fun j hj => hXi j)]
    simp only [X, integral_smul_const]
    simp_rw [bernoulli_mean μ _ (hδMeas _) q (hδ _)]
    rw [← Finset.smul_sum]
  have hsum : (∑ j, rowDiagonal B j).PosSemidef := by
    rw [rowDiagonal_sum]
    exact diagonal_psd _ (fun k => Finset.sum_nonneg (fun j hj => sq_nonneg _))
  have hmax : lambdaMax (∑ j, rowDiagonal B j) = maxColumnSq B := by
    rw [rowDiagonal_sum, diagonal_max _ (fun k => Finset.sum_nonneg (fun j hj => sq_nonneg _))]
    rfl
  have hmean : lambdaMax (q • (∑ j, rowDiagonal B j)) = q * maxColumnSq B := by
    rw [max_eq_norm_of_psd _ (hsum.smul hq), norm_smul, Real.norm_eq_abs, abs_of_nonneg hq,
      ← max_eq_norm_of_psd _ hsum, hmax]
  have he : (fun ω => maxSelectedColumnSq B δ ω) =ᵐ[μ] (fun ω => lambdaMax (Y ω)) := by
    filter_upwards [ae_all_iff.mpr (fun j => (hδ j).1)] with ω hw
    exact selection_diagonal B δ ω hw
  refine ⟨H.1.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  rw [heY, hmean] at H
  simpa [q, mul_assoc, mul_comm, mul_left_comm] using H.2

#print axioms solution
