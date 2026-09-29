-- Prove2me | solution 1 for MatrixCompletion.NoSpuriousMin.perturbation_terms_bound_corrected
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-14T18:54:37.75927+00:00
-- url     : https://prove2.me/submissions/538accdc-a031-4db0-92b1-ec8d2aa6868a

import Definitions.Def_MCNoSpuriousMinModel
import Theorems.Thm_MatrixCompletion_NoSpuriousMin_sampling_deviation_bound
import Theorems.Thm_MatrixCompletion_NoSpuriousMin_regularizer_perturbation_bound
import Theorems.Thm_MatrixCompletion_NoSpuriousMin_row_norms_of_factorization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Matrix Finset MatrixCompletion.NoSpuriousMin WithLp

set_option maxHeartbeats 1000000

namespace MCAux

set_option maxHeartbeats 1000000

/-! ### `vecNorm` and Frobenius basics -/

lemma vecNorm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ vecNorm x := Real.sqrt_nonneg _

lemma vecNorm_sq {n : ℕ} (x : Fin n → ℝ) : vecNorm x ^ 2 = ∑ i, x i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma vecNorm_eq_norm {n : ℕ} (x : Fin n → ℝ) :
    vecNorm x = ‖(toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq, vecNorm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp [sq_abs]

lemma vecNorm_zero {n : ℕ} : vecNorm (0 : Fin n → ℝ) = 0 := by
  simp [vecNorm]

lemma vecNorm_eq_zero {n : ℕ} {x : Fin n → ℝ} (h : vecNorm x = 0) : x = 0 := by
  have h2 : ∑ i, x i ^ 2 = 0 := by rw [← vecNorm_sq, h]; ring
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x j)).mp h2 i
    (Finset.mem_univ i)
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

lemma vecNorm_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) : vecNorm (c • x) = |c| * vecNorm x := by
  rw [vecNorm, vecNorm, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c)]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply, smul_eq_mul]; ring

/-- Cauchy–Schwarz for a plain finite sum. -/
lemma abs_sum_mul_le {n : ℕ} (x y : Fin n → ℝ) :
    |∑ j, x j * y j| ≤ vecNorm x * vecNorm y := by
  have h := abs_real_inner_le_norm (toLp 2 x : EuclideanSpace ℝ (Fin n)) (toLp 2 y)
  rw [EuclideanSpace.inner_toLp_toLp] at h
  simpa [vecNorm_eq_norm, dotProduct, mul_comm] using h

lemma frobSq_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma frobNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ frobNorm A :=
  Real.sqrt_nonneg _

lemma frobNorm_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : frobNorm A ^ 2 = frobSq A :=
  Real.sq_sqrt (frobSq_nonneg A)

lemma innerM_self {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : innerM A A = frobSq A := by
  simp only [innerM, frobSq, sq]

lemma innerM_comm {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : innerM A B = innerM B A :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma innerM_add_left {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) ℝ) :
    innerM (A + B) C = innerM A C + innerM B C := by
  simp only [innerM, Matrix.add_apply, add_mul, ← Finset.sum_add_distrib]

lemma innerM_add_right {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) ℝ) :
    innerM A (B + C) = innerM A B + innerM A C := by
  simp only [innerM, Matrix.add_apply, mul_add, ← Finset.sum_add_distrib]

/-- Cauchy–Schwarz for the matrix (Frobenius) pairing. -/
lemma abs_innerM_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    |innerM A B| ≤ frobNorm A * frobNorm B := by
  classical
  have hsq : innerM A B ^ 2 ≤ frobSq A * frobSq B := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
      (fun q => A q.1 q.2) (fun q => B q.1 q.2)
    simpa [innerM, frobSq, Fintype.sum_prod_type] using h
  rw [frobNorm, frobNorm, ← Real.sqrt_mul (frobSq_nonneg A),
    show |innerM A B| = Real.sqrt (innerM A B ^ 2) from (Real.sqrt_sq_eq_abs _).symm]
  exact Real.sqrt_le_sqrt hsq

lemma frobSq_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : frobSq Aᵀ = frobSq A := by
  simp only [frobSq, Matrix.transpose_apply]
  exact Finset.sum_comm

lemma frobSq_eq_sum_rowNorm_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobSq A = ∑ i, rowNorm A i ^ 2 :=
  Finset.sum_congr rfl fun i _ => (vecNorm_sq (A i)).symm

lemma frobSq_eq_trace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobSq A = (Aᵀ * A).trace := by
  simp only [frobSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, sq]
  exact Finset.sum_comm

lemma eq_zero_of_frobSq_eq_zero {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} (h : frobSq A = 0) :
    A = 0 := by
  ext i j
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    fun k _ => Finset.sum_nonneg fun _ _ => sq_nonneg (A k _)).mp h i (Finset.mem_univ i)
  have := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => sq_nonneg (A i l)).mp hi j
    (Finset.mem_univ j)
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-! ### The variational singular values -/

lemma vecNorm_mulVec_le_frob {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {v : Fin n → ℝ}
    (hv : vecNorm v = 1) : vecNorm (A *ᵥ v) ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) := by
  have hv2 : ∑ j, v j ^ 2 = 1 := by rw [← vecNorm_sq, hv]; norm_num
  rw [vecNorm]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, (A *ᵥ v) i ^ 2
      ≤ ∑ i, (∑ j, A i j ^ 2) * ∑ j, v j ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa [Matrix.mulVec, dotProduct] using
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) v
    _ = ∑ i, ∑ j, A i j ^ 2 := by simp [hv2]

lemma bddAbove_sigma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    BddAbove (Set.range fun v : {v : Fin n → ℝ // vecNorm v = 1} =>
      vecNorm (A.mulVec v.1)) := by
  refine ⟨Real.sqrt (∑ i, ∑ j, A i j ^ 2), ?_⟩
  rintro _ ⟨v, rfl⟩
  exact vecNorm_mulVec_le_frob A v.2

lemma bddBelow_sigma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    BddBelow (Set.range fun v : {v : Fin n → ℝ // vecNorm v = 1} =>
      vecNorm (A.mulVec v.1)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact vecNorm_nonneg _

/-- A canonical unit vector, so that the sphere is nonempty. -/
lemma sphere_nonempty {n : ℕ} (hn : 0 < n) :
    Nonempty {v : Fin n → ℝ // vecNorm v = 1} := by
  classical
  refine ⟨⟨fun j => if j = ⟨0, hn⟩ then 1 else 0, ?_⟩⟩
  have h1 : ∑ j : Fin n, (if j = ⟨0, hn⟩ then (1 : ℝ) else 0) ^ 2 = 1 := by
    simp
  rw [vecNorm, h1, Real.sqrt_one]

lemma vecNorm_mulVec_le_sigmaMax {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {v : Fin n → ℝ}
    (hv : vecNorm v = 1) : vecNorm (A *ᵥ v) ≤ sigmaMax A :=
  le_ciSup (bddAbove_sigma A) (⟨v, hv⟩ : {v : Fin n → ℝ // vecNorm v = 1})

lemma sigmaMin_le_vecNorm_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {v : Fin n → ℝ}
    (hv : vecNorm v = 1) : sigmaMin A ≤ vecNorm (A *ᵥ v) :=
  ciInf_le (bddBelow_sigma A) (⟨v, hv⟩ : {v : Fin n → ℝ // vecNorm v = 1})

lemma sigmaMin_nonneg {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ sigmaMin A := by
  haveI := sphere_nonempty (n := n) hn
  exact le_ciInf fun v => vecNorm_nonneg _

/-- The defining property of `sigmaMin`, without the normalization. -/
lemma sigmaMin_mul_vecNorm_le {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) : sigmaMin A * vecNorm v ≤ vecNorm (A *ᵥ v) := by
  rcases eq_or_ne (vecNorm v) 0 with h | h
  · have hv : v = 0 := vecNorm_eq_zero h
    subst hv
    simp [h, vecNorm_zero]
  · have hpos : 0 < vecNorm v := lt_of_le_of_ne (vecNorm_nonneg v) (Ne.symm h)
    set c := vecNorm v with hc
    have hw : vecNorm (c⁻¹ • v) = 1 := by
      rw [vecNorm_smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]
    have h1 : sigmaMin A ≤ vecNorm (A *ᵥ (c⁻¹ • v)) := sigmaMin_le_vecNorm_mulVec A hw
    have h2 : A *ᵥ (c⁻¹ • v) = c⁻¹ • (A *ᵥ v) := by
      rw [Matrix.mulVec_smul]
    rw [h2, vecNorm_smul, abs_of_pos (inv_pos.mpr hpos)] at h1
    calc sigmaMin A * c ≤ c⁻¹ * vecNorm (A *ᵥ v) * c :=
          mul_le_mul_of_nonneg_right h1 hpos.le
      _ = vecNorm (A *ᵥ v) := by field_simp

/-- `‖A Bᵀ‖_F² ≥ σ_min(A)² ‖B‖_F²`: each row of `B` is hit by `A`. -/
lemma frobSq_mul_transpose_ge {m n k : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin k) (Fin n) ℝ) :
    sigmaMin A ^ 2 * frobSq B ≤ frobSq (A * Bᵀ) := by
  have key : frobSq (A * Bᵀ) = ∑ j, vecNorm (A *ᵥ B j) ^ 2 := by
    have h1 : frobSq (A * Bᵀ) = ∑ j, ∑ i, ((A * Bᵀ) i j) ^ 2 := Finset.sum_comm
    rw [h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vecNorm_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [key, frobSq_eq_sum_rowNorm_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := sigmaMin_mul_vecNorm_le hn A (B j)
  have h0 : 0 ≤ sigmaMin A * vecNorm (B j) :=
    mul_nonneg (sigmaMin_nonneg hn A) (vecNorm_nonneg _)
  calc sigmaMin A ^ 2 * rowNorm B j ^ 2 = (sigmaMin A * vecNorm (B j)) ^ 2 := by
        rw [rowNorm]; ring
    _ ≤ vecNorm (A *ᵥ B j) ^ 2 := by
        exact pow_le_pow_left₀ h0 h 2

/-- `‖A‖_F² ≤ n σ_max(A)²`: the columns of `A` are images of the standard unit vectors. -/
lemma frobSq_le_card_mul_sigmaMax_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobSq A ≤ n * sigmaMax A ^ 2 := by
  classical
  have hcol : ∀ j : Fin n, ∑ i, A i j ^ 2 ≤ sigmaMax A ^ 2 := by
    intro j
    have hn : 0 < n := j.pos
    have hv : vecNorm (fun l => if l = j then (1 : ℝ) else 0) = 1 := by
      have h1 : ∑ l : Fin n, (if l = j then (1 : ℝ) else 0) ^ 2 = 1 := by
        simp
      rw [vecNorm, h1, Real.sqrt_one]
    have hmv : A *ᵥ (fun l => if l = j then (1 : ℝ) else 0) = fun i => A i j := by
      funext i
      simp [Matrix.mulVec, dotProduct]
    have := vecNorm_mulVec_le_sigmaMax A hv
    rw [hmv] at this
    have h2 := pow_le_pow_left₀ (vecNorm_nonneg _) this 2
    rwa [vecNorm_sq] at h2
  have : frobSq A = ∑ j, ∑ i, A i j ^ 2 := Finset.sum_comm
  rw [this]
  calc ∑ j : Fin n, ∑ i, A i j ^ 2 ≤ ∑ _j : Fin n, sigmaMax A ^ 2 :=
        Finset.sum_le_sum fun j _ => hcol j
    _ = n * sigmaMax A ^ 2 := by simp [mul_comm]

lemma sigmaMax_nonneg {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ sigmaMax A := by
  haveI := sphere_nonempty (n := n) hn
  obtain ⟨v⟩ := ‹Nonempty {v : Fin n → ℝ // vecNorm v = 1}›
  exact le_trans (vecNorm_nonneg _) (le_ciSup (bddAbove_sigma A) v)

/-! ### The 2→∞ norm -/

lemma rowNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    0 ≤ rowNorm A i := vecNorm_nonneg _

lemma rowNorm_le_twoInftyNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    rowNorm A i ≤ twoInftyNorm A :=
  le_ciSup (Finite.bddAbove_range _) i

lemma twoInftyNorm_nonneg {m n : ℕ} (hm : 0 < m) (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ twoInftyNorm A :=
  le_trans (rowNorm_nonneg A ⟨0, hm⟩) (rowNorm_le_twoInftyNorm A ⟨0, hm⟩)

lemma twoInftyNorm_pos {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} (h : 0 < frobSq A) :
    0 < twoInftyNorm A := by
  by_contra hle
  push_neg at hle
  have hzero : ∀ i, rowNorm A i = 0 := fun i =>
    le_antisymm (le_trans (rowNorm_le_twoInftyNorm A i) hle) (rowNorm_nonneg A i)
  have : frobSq A = 0 := by
    rw [frobSq_eq_sum_rowNorm_sq]
    exact Finset.sum_eq_zero fun i _ => by rw [hzero i]; ring
  exact absurd this (ne_of_gt h)

/-! ### Two factorizations of the same Gram matrix -/

lemma colProj_transpose {m n : ℕ} (Z : Matrix (Fin m) (Fin n) ℝ) :
    (colProj Z)ᵀ = colProj Z := by
  have hGt : (Zᵀ * Z)ᵀ = Zᵀ * Z := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [colProj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, hGt, Matrix.mul_assoc]

/-- `‖Av‖² = ⟨v, AᵀA v⟩`. -/
lemma vecNorm_mulVec_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    vecNorm (A *ᵥ v) ^ 2 = ∑ k, v k * ((Aᵀ * A) *ᵥ v) k := by
  rw [vecNorm_sq]
  have hgram : ∀ k, ((Aᵀ * A) *ᵥ v) k = ∑ i, A i k * (A *ᵥ v) i := by
    intro k
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  calc ∑ i, (A *ᵥ v) i ^ 2 = ∑ i, ∑ k, (A i k * v k) * (A *ᵥ v) i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul]
        simp [Matrix.mulVec, dotProduct, sq]
    _ = ∑ k, ∑ i, v k * (A i k * (A *ᵥ v) i) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k, v k * ((Aᵀ * A) *ᵥ v) k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.mul_sum, hgram]

/-- A matrix with a positive smallest singular value has an invertible Gram matrix. -/
lemma isUnit_det_gram {m n : ℕ} (hn : 0 < n) {Z : Matrix (Fin m) (Fin n) ℝ}
    (hσ : 0 < sigmaMin Z) : IsUnit (Zᵀ * Z).det := by
  classical
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h0 : vecNorm (Z *ᵥ v) ^ 2 = 0 := by
    rw [vecNorm_mulVec_sq, hzero]
    simp
  have h1 : vecNorm (Z *ᵥ v) = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    exact this
  have h2 : sigmaMin Z * vecNorm v ≤ 0 := by
    rw [← h1]; exact sigmaMin_mul_vecNorm_le hn Z v
  have h3 : 0 < vecNorm v := by
    rcases eq_or_lt_of_le (vecNorm_nonneg v) with h | h
    · exact absurd (vecNorm_eq_zero h.symm) hv
    · exact h
  exact absurd h2 (not_le.mpr (mul_pos hσ h3))

/-- The column-span projector of `Z` fixes any aligned factor `U`. -/
lemma colProj_mul_of_gram_eq {m n : ℕ} (hn : 0 < n)
    {Z U : Matrix (Fin m) (Fin n) ℝ} (hσ : 0 < sigmaMin Z) (hU : U * Uᵀ = Z * Zᵀ) :
    colProj Z * U = U := by
  classical
  have hG : IsUnit (Zᵀ * Z).det := isUnit_det_gram hn hσ
  have hGinv : (Zᵀ * Z)⁻¹ * (Zᵀ * Z) = 1 := Matrix.nonsing_inv_mul _ hG
  have hPZ : colProj Z * Z = Z := by
    rw [colProj, Matrix.mul_assoc, Matrix.mul_assoc, hGinv, Matrix.mul_one]
  have hQZ : (1 - colProj Z) * Z = 0 := by
    rw [Matrix.sub_mul, hPZ, Matrix.one_mul, sub_self]
  have hQU : (1 - colProj Z) * U = 0 := by
    apply eq_zero_of_frobSq_eq_zero
    rw [frobSq_eq_trace, Matrix.trace_mul_comm]
    have h1 : ((1 - colProj Z) * U) * ((1 - colProj Z) * U)ᵀ = 0 := by
      rw [Matrix.transpose_mul]
      rw [show (1 - colProj Z) * U * (Uᵀ * (1 - colProj Z)ᵀ)
            = ((1 - colProj Z) * (U * Uᵀ)) * (1 - colProj Z)ᵀ by
          simp [Matrix.mul_assoc]]
      rw [hU, ← Matrix.mul_assoc, hQZ, Matrix.zero_mul, Matrix.zero_mul]
    rw [h1, Matrix.trace_zero]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hQU
  exact hQU.symm

/-- `Uᵀ (1 − P) = 0` for an aligned factor: the transposed form. -/
lemma mul_colProj_of_gram_eq {m n : ℕ} (hn : 0 < n)
    {Z U : Matrix (Fin m) (Fin n) ℝ} (hσ : 0 < sigmaMin Z) (hU : U * Uᵀ = Z * Zᵀ) :
    Uᵀ * colProj Z = Uᵀ := by
  have h := congrArg Matrix.transpose (colProj_mul_of_gram_eq hn hσ hU)
  rwa [Matrix.transpose_mul, colProj_transpose] at h

/-- If `U Uᵀ = Z Zᵀ` and `Z` has full column rank, then `U = Z R` for an orthogonal `R`. -/
lemma exists_orthogonal_of_gram_eq {m n : ℕ} (hn : 0 < n)
    {Z U : Matrix (Fin m) (Fin n) ℝ} (hσ : 0 < sigmaMin Z) (hU : U * Uᵀ = Z * Zᵀ) :
    ∃ R : Matrix (Fin n) (Fin n) ℝ, U = Z * R ∧ Rᵀ * R = 1 := by
  classical
  set G : Matrix (Fin n) (Fin n) ℝ := Zᵀ * Z with hGdef
  have hG : IsUnit G.det := isUnit_det_gram hn hσ
  have hGinv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
  have hGinv' : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hG
  have hPU : colProj Z * U = U := colProj_mul_of_gram_eq hn hσ hU
  set R : Matrix (Fin n) (Fin n) ℝ := G⁻¹ * Zᵀ * U with hRdef
  have hZR : Z * R = U := by
    rw [hRdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← colProj, hPU]
  have hbig : (Z * R) * (Z * R)ᵀ = Z * Zᵀ := by rw [hZR, hU]
  have hmid : G * (R * Rᵀ) * G = G * G := by
    have e1 : Zᵀ * ((Z * R) * (Z * R)ᵀ) * Z = G * (R * Rᵀ) * G := by
      rw [Matrix.transpose_mul, hGdef]; simp [Matrix.mul_assoc]
    have e2 : Zᵀ * (Z * Zᵀ) * Z = G * G := by rw [hGdef]; simp [Matrix.mul_assoc]
    rw [← e1, ← e2, hbig]
  have hRRt : R * Rᵀ = 1 := by
    calc R * Rᵀ = (G⁻¹ * G) * (R * Rᵀ) * (G * G⁻¹) := by
          rw [hGinv, hGinv', Matrix.one_mul, Matrix.mul_one]
      _ = G⁻¹ * (G * (R * Rᵀ) * G) * G⁻¹ := by simp [Matrix.mul_assoc]
      _ = G⁻¹ * (G * G) * G⁻¹ := by rw [hmid]
      _ = (G⁻¹ * G) * (G * G⁻¹) := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hGinv, hGinv', Matrix.one_mul]
  exact ⟨R, hZR.symm, mul_eq_one_comm.mp hRRt⟩

/-- Aligned factors have the same smallest singular value. -/
lemma sigmaMin_le_of_gram_eq {m n : ℕ} (hn : 0 < n) {Z U : Matrix (Fin m) (Fin n) ℝ}
    (hσ : 0 < sigmaMin Z) (hU : U * Uᵀ = Z * Zᵀ) : sigmaMin Z ≤ sigmaMin U := by
  haveI := sphere_nonempty (n := n) hn
  obtain ⟨R, hR, hRo⟩ := exists_orthogonal_of_gram_eq hn hσ hU
  refine le_ciInf fun v => ?_
  have hiso : vecNorm (R *ᵥ v.1) = vecNorm v.1 := by
    have h1 : vecNorm (R *ᵥ v.1) ^ 2 = vecNorm v.1 ^ 2 := by
      rw [vecNorm_mulVec_sq, hRo, vecNorm_sq]
      simp [Matrix.one_mulVec, sq]
    have := congrArg Real.sqrt h1
    rwa [Real.sqrt_sq (vecNorm_nonneg _), Real.sqrt_sq (vecNorm_nonneg _)] at this
  have h2 : U *ᵥ v.1 = Z *ᵥ (R *ᵥ v.1) := by
    rw [hR, Matrix.mulVec_mulVec]
  rw [h2]
  have := sigmaMin_mul_vecNorm_le hn Z (R *ᵥ v.1)
  rwa [hiso, v.2, mul_one] at this

/-- The absorption inequality: `‖U Δᵀ‖_F² ≥ σ_min(Z)² ‖Δ‖_F²` for an aligned `U`. -/
lemma frobSq_mul_transpose_ge_sigmaMin {d r : ℕ} (hr : 0 < r)
    {Z U : Matrix (Fin d) (Fin r) ℝ} (hσ : 0 < sigmaMin Z) (hU : U * Uᵀ = Z * Zᵀ)
    (D : Matrix (Fin d) (Fin r) ℝ) :
    sigmaMin Z ^ 2 * frobSq D ≤ frobSq (U * Dᵀ) := by
  refine le_trans ?_ (frobSq_mul_transpose_ge hr U D)
  refine mul_le_mul_of_nonneg_right ?_ (frobSq_nonneg D)
  exact pow_le_pow_left₀ hσ.le (sigmaMin_le_of_gram_eq hr hσ hU) 2

end MCAux

open MCAux

namespace PTB

set_option maxHeartbeats 1000000

variable {d : ℕ}

/-! ### Bilinearity of the sampling deviation -/

lemma projSet_add (Ω : Finset (Fin d × Fin d)) (A B : Matrix (Fin d) (Fin d) ℝ) :
    projSet Ω (A + B) = projSet Ω A + projSet Ω B := by
  classical
  ext i j
  simp only [projSet, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

lemma sampDev_comm (Ω : Finset (Fin d × Fin d)) (t : ℝ) (A B : Matrix (Fin d) (Fin d) ℝ) :
    sampDev Ω t A B = sampDev Ω t B A := by
  rw [sampDev, sampDev, innerM_comm (projSet Ω A), innerM_comm A]

lemma sampDev_add_left (Ω : Finset (Fin d × Fin d)) (t : ℝ)
    (A B C : Matrix (Fin d) (Fin d) ℝ) :
    sampDev Ω t (A + B) C = sampDev Ω t A C + sampDev Ω t B C := by
  rw [sampDev, sampDev, sampDev, projSet_add, innerM_add_left, innerM_add_left]
  ring

lemma sampDev_add_right (Ω : Finset (Fin d × Fin d)) (t : ℝ)
    (A B C : Matrix (Fin d) (Fin d) ℝ) :
    sampDev Ω t A (B + C) = sampDev Ω t A B + sampDev Ω t A C := by
  rw [sampDev_comm, sampDev_add_left, sampDev_comm Ω t B A, sampDev_comm Ω t C A]

/-! ### The numerical core of the absorption step -/

/-- With the sampling constant raised to `10²⁸`, the regularizer's `λα²‖Δ‖_F²` term fits
inside the `σ_min(Z)²` budget on the right-hand side. -/
lemma key_arith {S ν p σ μ κ t s dd rr : ℝ}
    (hdd : 2 ≤ dd) (hrr : 1 ≤ rr) (hμ : 1 ≤ μ) (hκ : 1 ≤ κ)
    (hS : S ≤ 100 * (t + s)) (hS0 : 0 ≤ S)
    (ht : 0 ≤ t) (ht2 : t ^ 2 = dd * p) (hs : 0 ≤ s)
    (hν : ν ^ 2 ≤ μ ^ 2 * rr / dd) (hν0 : 0 ≤ ν)
    (hσ : 1 / κ ≤ σ) (hσ0 : 0 < σ) (hp0 : 0 < p)
    (hpC : 10 ^ 28 * μ ^ 4 * κ ^ 4 * rr ^ 2 * (1 + s ^ 2) ≤ p * dd) :
    1600000000 * S * ν ^ 2 ≤ 8 / 1000 * p * σ ^ 2 := by
  have hdd0 : (0:ℝ) < dd := by linarith
  have hκ0 : (0:ℝ) < κ := by linarith
  have hμ2 : (1:ℝ) ≤ μ ^ 2 := by nlinarith
  have hκ2 : (1:ℝ) ≤ κ ^ 2 := by nlinarith
  have hstep : (1:ℝ) ≤ μ ^ 2 * rr := by nlinarith
  have hc1 : 1 ≤ μ ^ 2 * rr * κ ^ 2 := by nlinarith
  have hc0 : (0:ℝ) < μ ^ 2 * rr * κ ^ 2 := by linarith
  have hpc : 10 ^ 28 * (μ ^ 2 * rr * κ ^ 2) ^ 2 * (1 + s ^ 2) ≤ p * dd := by
    have heq : 10 ^ 28 * (μ ^ 2 * rr * κ ^ 2) ^ 2 * (1 + s ^ 2)
        = 10 ^ 28 * μ ^ 4 * κ ^ 4 * rr ^ 2 * (1 + s ^ 2) := by ring
    linarith [hpC, heq.le, heq.ge]
  -- `t = √(dp)` is large
  have hA : 40000000000000 * (μ ^ 2 * rr * κ ^ 2) ≤ t := by
    have h1 : (40000000000000 * (μ ^ 2 * rr * κ ^ 2)) ^ 2 ≤ t ^ 2 := by
      rw [ht2, mul_comm dd p]
      nlinarith [hpc, mul_nonneg (sq_nonneg (μ ^ 2 * rr * κ ^ 2)) (sq_nonneg s)]
    nlinarith [h1, ht, hc0]
  have hAt : 20000000000000 * (μ ^ 2 * rr * κ ^ 2) * t ≤ p * dd / 2 := by
    nlinarith [hA, ht, ht2]
  -- `s = √(log d)` is small
  have hB : 20000000000000 * (μ ^ 2 * rr * κ ^ 2) * s ≤ p * dd / 2 := by
    have h1 : 10 ^ 28 * (μ ^ 2 * rr * κ ^ 2) * (1 + s ^ 2)
        ≤ 10 ^ 28 * (μ ^ 2 * rr * κ ^ 2) ^ 2 * (1 + s ^ 2) := by
      have hprod : (0:ℝ) ≤
          ((μ ^ 2 * rr * κ ^ 2) ^ 2 - (μ ^ 2 * rr * κ ^ 2)) * (1 + s ^ 2) :=
        mul_nonneg (by nlinarith [hc1, hc0]) (by positivity)
      nlinarith [hprod]
    have h2 : (0:ℝ) ≤ (μ ^ 2 * rr * κ ^ 2) * (1 + s ^ 2 - 2 * s) :=
      mul_nonneg hc0.le (by nlinarith [sq_nonneg (s - 1)])
    nlinarith [hpc, h1, h2, mul_nonneg hc0.le hs]
  have hsum : 20000000000000 * (μ ^ 2 * rr * κ ^ 2) * (t + s) ≤ p * dd := by
    nlinarith [hAt, hB]
  -- assemble
  have hσκ : (1:ℝ) ≤ σ * κ := by
    rw [div_le_iff₀ hκ0] at hσ
    linarith
  have hσ2 : 1 / κ ^ 2 ≤ σ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hσκ]
  have hν2 : S * ν ^ 2 ≤ 100 * (t + s) * (μ ^ 2 * rr / dd) := by
    have h1 : S * ν ^ 2 ≤ 100 * (t + s) * ν ^ 2 :=
      mul_le_mul_of_nonneg_right hS (sq_nonneg ν)
    have h2 : 100 * (t + s) * ν ^ 2 ≤ 100 * (t + s) * (μ ^ 2 * rr / dd) :=
      mul_le_mul_of_nonneg_left hν (by linarith)
    linarith
  have hfinal : 1600000000 * (100 * (t + s) * (μ ^ 2 * rr / dd))
      ≤ 8 / 1000 * p * (1 / κ ^ 2) := by
    rw [← sub_nonneg]
    have key : 8 / 1000 * p * (1 / κ ^ 2)
          - 1600000000 * (100 * (t + s) * (μ ^ 2 * rr / dd))
        = (8 / 1000 * (p * dd - 20000000000000 * (μ ^ 2 * rr * κ ^ 2) * (t + s)))
            / (dd * κ ^ 2) := by
      field_simp
      ring
    rw [key]
    exact div_nonneg (by linarith) (by positivity)
  nlinarith [hν2, hfinal, hσ2, hp0]

end PTB

open PTB

/-! ### The corrected Lemma 4.8 -/

theorem solution
    {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r)
    (Z X U : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (p μ κ lam α : ℝ)
    (hμ : 1 ≤ μ) (hκ : 1 ≤ κ) (hcond : sigmaMax Z ≤ κ * sigmaMin Z)
    (hσ : 0 < sigmaMin Z)
    (hinc : Incoherent μ Z) (hZnorm : frobSq Z = (r : ℝ))
    (hα1 : 100 * twoInftyNorm Z ≤ α) (hα2 : α ≤ 200 * twoInftyNorm Z)
    (hlam1 : 100 * sampDevNorm Ω p ≤ lam) (hlam2 : lam ≤ 200 * sampDevNorm Ω p)
    (hp : SampleCondition d r p μ κ)
    (hpC : 10 ^ 28 * μ ^ 4 * κ ^ 4 * (r : ℝ) ^ 2 * (1 + Real.log d) / d ≤ p)
    (hgood : GoodSample Z Ω p)
    (hU : U * Uᵀ = Z * Zᵀ) (hpsd : (Xᵀ * U).PosSemidef) :
    sampDev Ω p ((X - U) * (X - U)ᵀ) ((X - U) * (X - U)ᵀ)
        - 3 * sampDev Ω p (X * Xᵀ - U * Uᵀ) (X * Xᵀ - U * Uᵀ)
        + lam * (regHessQF α X (X - U) - 4 * innerM (regGrad α X) (X - U)) ≤
      p / 50 * (frobSq ((X - U)ᵀ * (X - U)) + frobSq (U * (X - U)ᵀ)) := by
  classical
  have hd0 : 0 < d := by omega
  have hr0 : 0 < r := by omega
  haveI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have hdR : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hrR : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd0R : (0:ℝ) < (d:ℝ) := by linarith
  set Dm : Matrix (Fin d) (Fin r) ℝ := X - U with hDm
  -- basic positivity
  have hS0 : 0 ≤ sampDevNorm Ω p := by
    rw [sampDevNorm]; exact sigmaMax_nonneg hd0 _
  have hν0 : 0 ≤ twoInftyNorm Z := twoInftyNorm_nonneg hd0 Z
  have hlam0 : 0 ≤ lam := le_trans (by linarith) hlam1
  have hlogd : (0:ℝ) ≤ Real.log d := Real.log_nonneg (by linarith)
  have hp0 : 0 < p := by
    have hnum : (0:ℝ) < 10 ^ 28 * μ ^ 4 * κ ^ 4 * (r:ℝ) ^ 2 * (1 + Real.log d) := by positivity
    exact lt_of_lt_of_le (div_pos hnum hd0R) hpC
  have hνpos : 0 < twoInftyNorm Z := twoInftyNorm_pos (by rw [hZnorm]; linarith)
  have hαpos : 0 < α := by linarith
  -- nonnegativity of the pieces
  have hQ0 : (0:ℝ) ≤ ∑ i, rowNorm Dm i ^ 4 := Finset.sum_nonneg fun i _ => by positivity
  have hF0 : (0:ℝ) ≤ frobSq Dm := frobSq_nonneg _
  have hE0 : (0:ℝ) ≤ frobSq (U * Dmᵀ) := frobSq_nonneg _
  have hP0 : (0:ℝ) ≤ ∑ k, rowNorm U k ^ 2 * rowNorm Dm k ^ 2 :=
    Finset.sum_nonneg fun k _ => by positivity
  -- Lemma 4.4 with the four factorizations
  have hQeq : (∑ k, vecNorm (Dm k) ^ 2 * vecNorm (Dm k) ^ 2) = ∑ i, rowNorm Dm i ^ 4 :=
    Finset.sum_congr rfl fun k _ => by rw [rowNorm]; ring
  have hPeq : (∑ k, vecNorm (U k) ^ 2 * vecNorm (Dm k) ^ 2)
      = ∑ k, rowNorm U k ^ 2 * rowNorm Dm k ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [rowNorm, rowNorm]
  have hb1 : |sampDev Ω p (Dm * Dmᵀ) (Dm * Dmᵀ)|
      ≤ sampDevNorm Ω p * (∑ i, rowNorm Dm i ^ 4) := by
    have h := sampling_deviation_bound Ω p Dm Dm Dm Dm
    rw [hQeq] at h
    calc |sampDev Ω p (Dm * Dmᵀ) (Dm * Dmᵀ)|
        ≤ sampDevNorm Ω p * Real.sqrt (∑ i, rowNorm Dm i ^ 4)
            * Real.sqrt (∑ i, rowNorm Dm i ^ 4) := h
      _ = sampDevNorm Ω p * (∑ i, rowNorm Dm i ^ 4) := by
          rw [mul_assoc, Real.mul_self_sqrt hQ0]
  have hb2 : |sampDev Ω p (U * Dmᵀ) (Dm * Dmᵀ)|
      ≤ sampDevNorm Ω p * Real.sqrt (∑ k, rowNorm U k ^ 2 * rowNorm Dm k ^ 2)
          * Real.sqrt (∑ i, rowNorm Dm i ^ 4) := by
    have h := sampling_deviation_bound Ω p U Dm Dm Dm
    rwa [hQeq, hPeq] at h
  have hb3 : |sampDev Ω p (Dm * Uᵀ) (Dm * Dmᵀ)|
      ≤ sampDevNorm Ω p * Real.sqrt (∑ i, rowNorm Dm i ^ 4)
          * Real.sqrt (∑ k, rowNorm U k ^ 2 * rowNorm Dm k ^ 2) := by
    have h := sampling_deviation_bound Ω p Dm Dm U Dm
    rwa [hQeq, hPeq] at h
  -- the tangent-space term
  have hWsymm : (U * Dmᵀ + Dm * Uᵀ).IsSymm := by
    show (U * Dmᵀ + Dm * Uᵀ)ᵀ = U * Dmᵀ + Dm * Uᵀ
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose, add_comm]
  have hQU0 : (1 - colProj Z) * U = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, colProj_mul_of_gram_eq hr0 hσ hU, sub_self]
  have hUQ0 : Uᵀ * (1 - colProj Z) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, mul_colProj_of_gram_eq hr0 hσ hU, sub_self]
  have htan : (1 - colProj Z) * (U * Dmᵀ + Dm * Uᵀ) * (1 - colProj Z) = 0 := by
    rw [Matrix.mul_add, Matrix.add_mul,
      show (1 - colProj Z) * (U * Dmᵀ) * (1 - colProj Z)
          = ((1 - colProj Z) * U) * (Dmᵀ * (1 - colProj Z)) by simp [Matrix.mul_assoc],
      show (1 - colProj Z) * (Dm * Uᵀ) * (1 - colProj Z)
          = ((1 - colProj Z) * Dm) * (Uᵀ * (1 - colProj Z)) by simp [Matrix.mul_assoc],
      hQU0, hUQ0, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  have hbW : |sampDev Ω p (U * Dmᵀ + Dm * Uᵀ) (U * Dmᵀ + Dm * Uᵀ)|
      ≤ p / 1000 * frobSq (U * Dmᵀ + Dm * Uᵀ) := by
    have h := hgood.tangent_conc _ _ hWsymm hWsymm htan htan
    calc |sampDev Ω p (U * Dmᵀ + Dm * Uᵀ) (U * Dmᵀ + Dm * Uᵀ)|
        ≤ p / 1000 * frobNorm (U * Dmᵀ + Dm * Uᵀ) * frobNorm (U * Dmᵀ + Dm * Uᵀ) := h
      _ = p / 1000 * frobSq (U * Dmᵀ + Dm * Uᵀ) := by
          rw [mul_assoc, ← pow_two, frobNorm_sq]
  have hWbound : frobSq (U * Dmᵀ + Dm * Uᵀ) ≤ 4 * frobSq (U * Dmᵀ) := by
    have hDU : Dm * Uᵀ = (U * Dmᵀ)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [hDU]
    have hexp : frobSq (U * Dmᵀ + (U * Dmᵀ)ᵀ)
        = frobSq (U * Dmᵀ) + 2 * innerM (U * Dmᵀ) ((U * Dmᵀ)ᵀ) + frobSq ((U * Dmᵀ)ᵀ) := by
      rw [← innerM_self, innerM_add_left, innerM_add_right, innerM_add_right,
        innerM_self, innerM_self, innerM_comm ((U * Dmᵀ)ᵀ) (U * Dmᵀ)]
      ring
    rw [hexp, frobSq_transpose]
    have hcs : innerM (U * Dmᵀ) ((U * Dmᵀ)ᵀ) ≤ frobSq (U * Dmᵀ) := by
      have h := abs_innerM_le (U * Dmᵀ) ((U * Dmᵀ)ᵀ)
      rw [frobNorm, frobNorm, frobSq_transpose,
        Real.mul_self_sqrt (frobSq_nonneg (U * Dmᵀ))] at h
      exact le_trans (le_abs_self _) h
    linarith
  have h3W : 3 * |sampDev Ω p (U * Dmᵀ + Dm * Uᵀ) (U * Dmᵀ + Dm * Uᵀ)|
      ≤ 12 / 1000 * p * frobSq (U * Dmᵀ) := by
    have h1 : p / 1000 * frobSq (U * Dmᵀ + Dm * Uᵀ) ≤ p / 1000 * (4 * frobSq (U * Dmᵀ)) :=
      mul_le_mul_of_nonneg_left hWbound (by linarith)
    linarith [hbW]
  -- the row-norm bookkeeping
  have hPbound : (∑ k, rowNorm U k ^ 2 * rowNorm Dm k ^ 2)
      ≤ twoInftyNorm Z ^ 2 * frobSq Dm := by
    rw [frobSq_eq_sum_rowNorm_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [row_norms_of_factorization U Z hU k]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (rowNorm_nonneg Z k) (rowNorm_le_twoInftyNorm Z k) 2)
      (sq_nonneg (rowNorm Dm k))
  have hsqPle : Real.sqrt (∑ k, rowNorm U k ^ 2 * rowNorm Dm k ^ 2)
      ≤ twoInftyNorm Z * Real.sqrt (frobSq Dm) := by
    have h1 := Real.sqrt_le_sqrt hPbound
    rwa [Real.sqrt_mul (sq_nonneg (twoInftyNorm Z)), Real.sqrt_sq hν0] at h1
  have hAM : 6 * (sampDevNorm Ω p * Real.sqrt (∑ k, rowNorm U k ^ 2 * rowNorm Dm k ^ 2)
        * Real.sqrt (∑ i, rowNorm Dm i ^ 4)
      + sampDevNorm Ω p * Real.sqrt (∑ i, rowNorm Dm i ^ 4)
        * Real.sqrt (∑ k, rowNorm U k ^ 2 * rowNorm Dm k ^ 2))
      ≤ 24 * sampDevNorm Ω p * (∑ i, rowNorm Dm i ^ 4)
        + 3 / 2 * sampDevNorm Ω p * twoInftyNorm Z ^ 2 * frobSq Dm := by
    have ha : Real.sqrt (∑ i, rowNorm Dm i ^ 4) ^ 2 = ∑ i, rowNorm Dm i ^ 4 := Real.sq_sqrt hQ0
    have hb : Real.sqrt (frobSq Dm) ^ 2 = frobSq Dm := Real.sq_sqrt hF0
    have h1 : Real.sqrt (∑ k, rowNorm U k ^ 2 * rowNorm Dm k ^ 2)
          * Real.sqrt (∑ i, rowNorm Dm i ^ 4)
        ≤ (twoInftyNorm Z * Real.sqrt (frobSq Dm)) * Real.sqrt (∑ i, rowNorm Dm i ^ 4) :=
      mul_le_mul_of_nonneg_right hsqPle (Real.sqrt_nonneg _)
    have hstep1 := mul_le_mul_of_nonneg_left h1 hS0
    have hstep2 : (0:ℝ) ≤ sampDevNorm Ω p
        * (4 * (∑ i, rowNorm Dm i ^ 4)
            - 2 * (Real.sqrt (∑ i, rowNorm Dm i ^ 4)
                * (twoInftyNorm Z * Real.sqrt (frobSq Dm)))
            + twoInftyNorm Z ^ 2 * frobSq Dm / 4) := by
      have h := mul_nonneg hS0 (sq_nonneg (2 * Real.sqrt (∑ i, rowNorm Dm i ^ 4)
        - twoInftyNorm Z * Real.sqrt (frobSq Dm) / 2))
      have e : (2 * Real.sqrt (∑ i, rowNorm Dm i ^ 4)
            - twoInftyNorm Z * Real.sqrt (frobSq Dm) / 2) ^ 2
          = 4 * (Real.sqrt (∑ i, rowNorm Dm i ^ 4) ^ 2)
            - 2 * (Real.sqrt (∑ i, rowNorm Dm i ^ 4)
                * (twoInftyNorm Z * Real.sqrt (frobSq Dm)))
            + twoInftyNorm Z ^ 2 * (Real.sqrt (frobSq Dm) ^ 2) / 4 := by ring
      rw [ha, hb] at e
      rwa [e] at h
    linarith [hstep1, hstep2]
  -- the regularizer (Chen–Li Lemma 4.10)
  have hreg0 := regularizer_perturbation_bound Z X U α hαpos hU hα1
  rw [← hDm] at hreg0
  have hreg : lam * (regHessQF α X Dm - 4 * innerM (regGrad α X) Dm)
      ≤ lam * (199.54 * α ^ 2 * frobSq Dm - 0.3 * (∑ i, rowNorm Dm i ^ 4)) :=
    mul_le_mul_of_nonneg_left hreg0 hlam0
  have hQcoef : 26 * sampDevNorm Ω p * (∑ i, rowNorm Dm i ^ 4)
      ≤ 0.3 * lam * (∑ i, rowNorm Dm i ^ 4) :=
    mul_le_mul_of_nonneg_right (by linarith) hQ0
  -- the absorption step
  have hν2 : twoInftyNorm Z ^ 2 ≤ μ ^ 2 * (r:ℝ) / (d:ℝ) := by
    have hνle : twoInftyNorm Z ≤ μ / Real.sqrt d * Real.sqrt r := by
      refine ciSup_le fun i => ?_
      have h := hinc i
      rwa [frobNorm, hZnorm] at h
    calc twoInftyNorm Z ^ 2 ≤ (μ / Real.sqrt d * Real.sqrt r) ^ 2 :=
          pow_le_pow_left₀ hν0 hνle 2
      _ = μ ^ 2 * (r:ℝ) / (d:ℝ) := by
          rw [mul_pow, div_pow, Real.sq_sqrt (le_of_lt hd0R),
            Real.sq_sqrt (by linarith : (0:ℝ) ≤ (r:ℝ))]
          ring
  have hsmax1 : (1:ℝ) ≤ sigmaMax Z := by
    have h := frobSq_le_card_mul_sigmaMax_sq Z
    rw [hZnorm] at h
    have h2 : (1:ℝ) ≤ sigmaMax Z ^ 2 := by nlinarith [hrR, h]
    nlinarith [h2, sigmaMax_nonneg hr0 Z]
  have hσκ : 1 / κ ≤ sigmaMin Z := by
    have hκ0 : (0:ℝ) < κ := by linarith
    rw [div_le_iff₀ hκ0]
    nlinarith [hcond, hsmax1]
  have hpCkey : 10 ^ 28 * μ ^ 4 * κ ^ 4 * (r:ℝ) ^ 2
      * (1 + Real.sqrt (Real.log d) ^ 2) ≤ p * (d:ℝ) := by
    rw [Real.sq_sqrt hlogd]
    rw [div_le_iff₀ hd0R] at hpC
    linarith
  have hkey : 1600000000 * sampDevNorm Ω p * twoInftyNorm Z ^ 2
      ≤ 8 / 1000 * p * sigmaMin Z ^ 2 :=
    key_arith (S := sampDevNorm Ω p) (ν := twoInftyNorm Z) (σ := sigmaMin Z)
      (t := Real.sqrt ((d:ℝ) * p)) (s := Real.sqrt (Real.log d))
      (dd := (d:ℝ)) (rr := (r:ℝ))
      hdR hrR hμ hκ hgood.spec_bound hS0 (Real.sqrt_nonneg _)
      (Real.sq_sqrt (by positivity)) (Real.sqrt_nonneg _) hν2 hν0 hσκ hσ hp0 hpCkey
  have hα2sq : α ^ 2 ≤ 40000 * twoInftyNorm Z ^ 2 := by nlinarith [hα2, hαpos, hν0]
  have hlamα : lam * α ^ 2 ≤ 200 * sampDevNorm Ω p * (40000 * twoInftyNorm Z ^ 2) := by
    have h1 : lam * α ^ 2 ≤ (200 * sampDevNorm Ω p) * α ^ 2 :=
      mul_le_mul_of_nonneg_right hlam2 (sq_nonneg α)
    have h2 : (200 * sampDevNorm Ω p) * α ^ 2
        ≤ (200 * sampDevNorm Ω p) * (40000 * twoInftyNorm Z ^ 2) :=
      mul_le_mul_of_nonneg_left hα2sq (by linarith)
    linarith
  have hcoefle : 3 / 2 * sampDevNorm Ω p * twoInftyNorm Z ^ 2 + 199.54 * lam * α ^ 2
      ≤ 1600000000 * sampDevNorm Ω p * twoInftyNorm Z ^ 2 := by
    nlinarith [hlamα, mul_nonneg hS0 (sq_nonneg (twoInftyNorm Z))]
  have hEge : sigmaMin Z ^ 2 * frobSq Dm ≤ frobSq (U * Dmᵀ) :=
    frobSq_mul_transpose_ge_sigmaMin hr0 hσ hU Dm
  have habs : (3 / 2 * sampDevNorm Ω p * twoInftyNorm Z ^ 2 + 199.54 * lam * α ^ 2)
      * frobSq Dm ≤ 8 / 1000 * p * frobSq (U * Dmᵀ) := by
    have h1 := mul_le_mul_of_nonneg_right hcoefle hF0
    have h2 := mul_le_mul_of_nonneg_right hkey hF0
    have h3 := mul_le_mul_of_nonneg_left hEge (show (0:ℝ) ≤ 8 / 1000 * p by linarith)
    linarith
  -- assemble
  have hsplit : sampDev Ω p (X * Xᵀ - U * Uᵀ) (X * Xᵀ - U * Uᵀ)
      = sampDev Ω p (U * Dmᵀ + Dm * Uᵀ) (U * Dmᵀ + Dm * Uᵀ)
        + 2 * (sampDev Ω p (U * Dmᵀ) (Dm * Dmᵀ) + sampDev Ω p (Dm * Uᵀ) (Dm * Dmᵀ))
        + sampDev Ω p (Dm * Dmᵀ) (Dm * Dmᵀ) := by
    have hM : X * Xᵀ - U * Uᵀ = (U * Dmᵀ + Dm * Uᵀ) + Dm * Dmᵀ := by
      rw [hDm]
      simp only [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]
      abel
    have e1 := sampDev_add_left Ω p (U * Dmᵀ + Dm * Uᵀ) (Dm * Dmᵀ)
      ((U * Dmᵀ + Dm * Uᵀ) + Dm * Dmᵀ)
    have e2 := sampDev_add_right Ω p (U * Dmᵀ + Dm * Uᵀ) (U * Dmᵀ + Dm * Uᵀ) (Dm * Dmᵀ)
    have e3 := sampDev_add_right Ω p (Dm * Dmᵀ) (U * Dmᵀ + Dm * Uᵀ) (Dm * Dmᵀ)
    have e4 := sampDev_comm Ω p (Dm * Dmᵀ) (U * Dmᵀ + Dm * Uᵀ)
    have e5 := sampDev_add_left Ω p (U * Dmᵀ) (Dm * Uᵀ) (Dm * Dmᵀ)
    rw [hM]
    linarith [e1, e2, e3, e4, e5]
  rw [hsplit]
  have hfrob0 : (0:ℝ) ≤ frobSq (Dmᵀ * Dm) := frobSq_nonneg _
  have hlast : p / 50 * frobSq (U * Dmᵀ)
      ≤ p / 50 * (frobSq (Dmᵀ * Dm) + frobSq (U * Dmᵀ)) := by
    have : (0:ℝ) ≤ p / 50 * frobSq (Dmᵀ * Dm) := by positivity
    linarith
  linarith [hb1, hb2, hb3, h3W, hAM, hreg, hQcoef, habs, hlast,
    neg_le_abs (sampDev Ω p (Dm * Dmᵀ) (Dm * Dmᵀ)),
    neg_le_abs (sampDev Ω p (U * Dmᵀ + Dm * Uᵀ) (U * Dmᵀ + Dm * Uᵀ)),
    neg_le_abs (sampDev Ω p (U * Dmᵀ) (Dm * Dmᵀ)),
    neg_le_abs (sampDev Ω p (Dm * Uᵀ) (Dm * Dmᵀ))]
