-- Prove2me | solution 1 for ModernConvex.MatrixCube.rank_two_eig_l1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:56:23.779925+00:00
-- url     : https://prove2.me/submissions/e0b198a5-f341-431a-a14a-940eecd207d9

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

open Matrix
open ModernConvex.MatrixCube

theorem g69a2_trace_sq_eig {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 := by
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set U := hA.eigenvectorUnitary
  set D : Matrix (Fin k) (Fin k) ℝ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hUU : star (U : Matrix (Fin k) (Fin k) ℝ) * (U : Matrix (Fin k) (Fin k) ℝ) = 1 :=
    Unitary.coe_star_mul_self U
  have h1 : A * A = (U : Matrix (Fin k) (Fin k) ℝ) * (D * D) * star (U : Matrix (Fin k) (Fin k) ℝ) := by
    conv_lhs => rw [hspec]
    calc (U : Matrix (Fin k) (Fin k) ℝ) * D * star (U : Matrix (Fin k) (Fin k) ℝ) *
          ((U : Matrix (Fin k) (Fin k) ℝ) * D * star (U : Matrix (Fin k) (Fin k) ℝ))
        = (U : Matrix (Fin k) (Fin k) ℝ) * D * (star (U : Matrix (Fin k) (Fin k) ℝ) *
          (U : Matrix (Fin k) (Fin k) ℝ)) * D * star (U : Matrix (Fin k) (Fin k) ℝ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h1, trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  simp [D, diagonal_mul_diagonal, trace_diagonal, sq]

theorem g69a2_rank_le_two {n : ℕ} (f g : Fin n → ℝ) :
    (vecMulVec f g + vecMulVec g f).rank ≤ 2 := by
  have : vecMulVec f g + vecMulVec g f =
      (Matrix.of fun i (k : Fin 2) => ![f i, g i] k) * (Matrix.of fun (k : Fin 2) j => ![g j, f j] k) := by
    ext i j
    simp [vecMulVec_apply, mul_apply, Fin.sum_univ_two]
  rw [this]
  exact (rank_mul_le_left _ _).trans (rank_le_width _)

theorem g69a2_two_supp {n : ℕ} (l : Fin n → ℝ) (h : Fintype.card {i // l i ≠ 0} ≤ 2) :
    ∃ a b : ℝ, ∑ i, |l i| = |a| + |b| ∧ ∑ i, l i = a + b ∧ ∑ i, l i ^ 2 = a ^ 2 + b ^ 2 := by
  set T := Finset.univ.filter (fun i => l i ≠ 0)
  have hT : T.card ≤ 2 := by
    rw [Fintype.card_subtype] at h; exact h
  have key : ∀ F : ℝ → ℝ, F 0 = 0 → ∑ i, F (l i) = ∑ i ∈ T, F (l i) := by
    intro F hF
    rw [Finset.sum_filter_of_ne]
    intro i _ hi h0; exact hi (by rw [h0, hF])
  rw [key (fun x => |x|) (by simp), show ∑ i, l i = ∑ i ∈ T, l i from key id rfl,
    show ∑ i, l i ^ 2 = ∑ i ∈ T, l i ^ 2 from key (fun x => x ^ 2) (by simp)]
  interval_cases hc : T.card
  · rw [Finset.card_eq_zero] at hc
    rw [hc]; exact ⟨0, 0, by simp⟩
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    rw [hi]; exact ⟨l i, 0, by simp⟩
  · obtain ⟨i, j, hij, hi⟩ := Finset.card_eq_two.mp hc
    rw [hi]; exact ⟨l i, l j, by simp [Finset.sum_pair hij]⟩

theorem g69a2_r2_real (a b P F G : ℝ) (hF : 0 ≤ F) (hG : 0 ≤ G) (hPFG : P ^ 2 ≤ F * G)
    (hs : a + b = 2 * P) (hq : a ^ 2 + b ^ 2 = 2 * (F * G) + 2 * P ^ 2) :
    |a| + |b| = 2 * Real.sqrt F * Real.sqrt G := by
  have e2 : 2 * (a * b) = (a + b) ^ 2 - (a ^ 2 + b ^ 2) := by ring
  rw [hs, hq] at e2
  have hab : a * b ≤ 0 := by nlinarith
  have h1 : (|a| + |b|) ^ 2 = 4 * (F * G) := by
    have : |a| * |b| = -(a * b) := by rw [← abs_mul, abs_of_nonpos hab]
    have e : (|a| + |b|) ^ 2 = |a| ^ 2 + |b| ^ 2 + 2 * (|a| * |b|) := by ring
    rw [e, sq_abs, sq_abs, this, hq]
    linarith
  have h2 : 2 * Real.sqrt F * Real.sqrt G = Real.sqrt (4 * (F * G)) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hF, show (4:ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]; ring
  rw [h2, ← h1, Real.sqrt_sq (by positivity)]

theorem g69a2_trAA {n : ℕ} (f g : Fin n → ℝ) :
    ((vecMulVec f g + vecMulVec g f) * (vecMulVec f g + vecMulVec g f)).trace =
      2 * ((∑ i, f i ^ 2) * (∑ i, g i ^ 2)) + 2 * (∑ i, f i * g i) ^ 2 := by
  have e : 2 * ((∑ i, f i ^ 2) * (∑ i, g i ^ 2)) + 2 * (∑ i, f i * g i) ^ 2 =
      (∑ i, f i ^ 2) * (∑ i, g i ^ 2) + (∑ i, g i ^ 2) * (∑ i, f i ^ 2) +
        2 * ((∑ i, f i * g i) * (∑ i, f i * g i)) := by ring
  rw [e, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp only [trace, diag, mul_apply, Matrix.add_apply, vecMulVec_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem g69a2_r2_main {n : ℕ} (f g : Fin n → ℝ) :
    eigL1 (vecMulVec f g + vecMulVec g f) =
      2 * Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
  set A := vecMulVec f g + vecMulVec g f with hAdef
  have h : A.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp [hAdef, vecMulVec_apply, mul_comm, add_comm]
  unfold eigL1 eigVec
  rw [dif_pos h]
  have hcard : Fintype.card {i // h.eigenvalues i ≠ 0} ≤ 2 := by
    rw [← h.rank_eq_card_non_zero_eigs]; exact g69a2_rank_le_two f g
  obtain ⟨a, b, h1, h2, h3⟩ := g69a2_two_supp h.eigenvalues hcard
  rw [h1]
  have hs : a + b = 2 * ∑ i, f i * g i := by
    rw [← h2]
    have := h.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id] at this
    rw [← this, hAdef, trace_add, trace_vecMulVec, trace_vecMulVec, dotProduct_comm g f]
    simp [dotProduct]; ring
  have hq : a ^ 2 + b ^ 2 = 2 * ((∑ i, f i ^ 2) * (∑ i, g i ^ 2)) + 2 * (∑ i, f i * g i) ^ 2 := by
    rw [← h3, ← g69a2_trace_sq_eig A h, hAdef, g69a2_trAA]
  refine g69a2_r2_real a b _ _ _ (Finset.sum_nonneg fun i _ => sq_nonneg _)
    (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_ hs hq
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g


/-- Ben-Tal–Nemirovski, Lemma 4.4.5, p. 197: for vectors `f, g ∈ ℝⁿ` and `A = fgᵀ + gfᵀ`,
`‖λ(A)‖₁ = 2‖f‖₂‖g‖₂`, where `‖λ(A)‖₁` is the sum of the absolute values of the eigenvalues
of the symmetric matrix `A` and `‖·‖₂` is the Euclidean norm. -/
theorem solution {n : ℕ} (f g : Fin n → ℝ) :
    eigL1 (vecMulVec f g + vecMulVec g f) =
      2 * Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := g69a2_r2_main f g

