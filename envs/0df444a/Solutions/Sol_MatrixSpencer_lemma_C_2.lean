-- Prove2me | solution 1 for MatrixSpencer.lemma_C_2
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-12T13:05:55.412909+00:00
-- url     : https://prove2.me/submissions/bed4c43a-79cf-410a-90ab-8965bac40550

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Matrix
open scoped BigOperators Kronecker

private def tensor {n d r : ℕ} (C : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (z : Fin n → (Fin d × Fin r → ℝ)) (a b : Fin d) (x : Fin d × Fin r) : ℝ :=
  ∑ i, C i a b * z i x

private lemma energy {n d r : ℕ} (C : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hC : ∀ i, (C i).IsSymm) (z : Fin n → (Fin d × Fin r → ℝ)) :
    ∑ i, ∑ j, (C i * C j).trace * (z i ⬝ᵥ z j) =
      ∑ a, ∑ b, ∑ x, tensor C z a b x ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct,
    tensor, pow_two, Finset.sum_mul, Finset.mul_sum]
  let e : (Fin n × Fin n × (Fin d × Fin r) × Fin d × Fin d) ≃
      (Fin d × Fin d × (Fin d × Fin r) × Fin n × Fin n) :=
    { toFun := fun q => (q.2.2.2.1, q.2.2.2.2, q.2.2.1, q.2.1, q.1)
      invFun := fun q => (q.2.2.2.2, q.2.2.2.1, q.2.2.1, q.1, q.2.1)
      left_inv := by intro q; rfl
      right_inv := by intro q; rfl }
  have hh := Fintype.sum_equiv e
    (fun q => C q.1 q.2.2.2.1 q.2.2.2.2 * C q.2.1 q.2.2.2.2 q.2.2.2.1 *
      (z q.1 q.2.2.1 * z q.2.1 q.2.2.1))
    (fun q => C q.2.2.2.2 q.1 q.2.1 * z q.2.2.2.2 q.2.2.1 *
      (C q.2.2.2.1 q.1 q.2.1 * z q.2.2.2.1 q.2.2.1)) (by
    intro q
    dsimp [e]
    rw [(hC q.2.1).apply]
    ring)
  simpa only [Fintype.sum_prod_type] using hh

private lemma mixed {n d r : ℕ} (C D : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (z : Fin n → (Fin d × Fin r → ℝ)) :
    ∑ i, ∑ j, z i ⬝ᵥ ((C j * D i) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ z j =
      ∑ a, ∑ b, ∑ c, ∑ l,
        tensor C z a b (c, l) * tensor D z b c (a, l) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, zero_mul, ite_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Matrix.mul_apply, tensor, Finset.sum_mul, Finset.mul_sum]
  let e : (Fin n × Fin n × Fin d × Fin r × Fin d × Fin d) ≃
      (Fin d × Fin d × Fin d × Fin r × Fin n × Fin n) :=
    { toFun := fun q => (q.2.2.1, q.2.2.2.2.2, q.2.2.2.2.1, q.2.2.2.1, q.1, q.2.1)
      invFun := fun q => (q.2.2.2.2.1, q.2.2.2.2.2, q.1, q.2.2.2.1, q.2.2.1, q.2.1)
      left_inv := by intro q; rfl
      right_inv := by intro q; rfl }
  have hh := Fintype.sum_equiv e
    (fun q => z q.1 (q.2.2.1, q.2.2.2.1) *
      (C q.2.1 q.2.2.1 q.2.2.2.2.2 * D q.1 q.2.2.2.2.2 q.2.2.2.2.1 *
        z q.2.1 (q.2.2.2.2.1, q.2.2.2.1)))
    (fun q => C q.2.2.2.2.2 q.1 q.2.1 * z q.2.2.2.2.2 (q.2.2.1, q.2.2.2.1) *
      (D q.2.2.2.2.1 q.2.1 q.2.2.1 * z q.2.2.2.2.1 (q.1, q.2.2.2.1))) (by
    intro q
    dsimp [e]
    ring)
  simpa only [Fintype.sum_prod_type] using hh

private lemma mixed_bound {n d r : ℕ} (C D : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hC : ∀ i, (C i).IsSymm) (hD : ∀ i, (D i).IsSymm)
    (z : Fin n → (Fin d × Fin r → ℝ)) :
    |∑ i, ∑ j, z i ⬝ᵥ ((C j * D i) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ z j| ≤
      √(∑ i, ∑ j, (C i * C j).trace * (z i ⬝ᵥ z j)) *
        √(∑ i, ∑ j, (D i * D j).trace * (z i ⬝ᵥ z j)) := by
  let f : (Fin d × Fin d × Fin d × Fin r) → ℝ :=
    fun q => tensor C z q.1 q.2.1 (q.2.2.1, q.2.2.2)
  let g : (Fin d × Fin d × Fin d × Fin r) → ℝ :=
    fun q => tensor D z q.2.1 q.2.2.1 (q.1, q.2.2.2)
  have hc : (∑ q, f q ^ 2) = ∑ i, ∑ j, (C i * C j).trace * (z i ⬝ᵥ z j) := by
    simpa only [f, Fintype.sum_prod_type] using (energy C hC z).symm
  have hd : (∑ q, g q ^ 2) = ∑ i, ∑ j, (D i * D j).trace * (z i ⬝ᵥ z j) := by
    let e : (Fin d × Fin d × Fin d × Fin r) ≃ (Fin d × Fin d × Fin d × Fin r) :=
      { toFun := fun q => (q.2.1, q.2.2.1, q.1, q.2.2.2)
        invFun := fun q => (q.2.2.1, q.1, q.2.1, q.2.2.2)
        left_inv := by intro q; rfl
        right_inv := by intro q; rfl }
    calc
      _ = ∑ q : Fin d × Fin d × Fin d × Fin r,
          tensor D z q.1 q.2.1 (q.2.2.1, q.2.2.2) ^ 2 :=
        Fintype.sum_equiv e _ _ (by intro q; rfl)
      _ = _ := by simpa only [Fintype.sum_prod_type] using (energy D hD z).symm
  have hm : (∑ q, f q * g q) =
      ∑ i, ∑ j, z i ⬝ᵥ ((C j * D i) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ z j := by
    simpa only [f, g, Fintype.sum_prod_type] using (mixed C D z).symm
  rw [← hm, ← hc, ← hd]
  calc
    |∑ q, f q * g q| ≤ ∑ q, |f q * g q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ √(∑ q, f q ^ 2) * √(∑ q, g q ^ 2) := by
      simpa only [Finset.mem_univ, Finset.sum_const_zero, abs_mul, sq_abs] using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun q => |f q|) (fun q => |g q|)

theorem solution {n d r : ℕ} (C D : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hC : ∀ i, (C i).IsSymm) (hD : ∀ i, (D i).IsSymm) (z : Fin n → (Fin d × Fin r → ℝ)) :
    |∑ i, ∑ j, z i ⬝ᵥ ((C j * C i) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ z j| ≤
      ∑ i, ∑ j, (C i * C j).trace * (z i ⬝ᵥ z j) ∧
    |∑ i, ∑ j, z i ⬝ᵥ ((C j * D i) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ z j| ≤
      √(∑ i, ∑ j, (C i * C j).trace * (z i ⬝ᵥ z j)) *
        √(∑ i, ∑ j, (D i * D j).trace * (z i ⬝ᵥ z j)) := by
  have hnonneg : 0 ≤ ∑ i, ∑ j, (C i * C j).trace * (z i ⬝ᵥ z j) := by
    rw [energy C hC z]
    positivity
  constructor
  · simpa only [Real.mul_self_sqrt hnonneg] using mixed_bound C C hC hC z
  · exact mixed_bound C D hC hD z

#print axioms solution
