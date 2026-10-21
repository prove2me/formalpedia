-- Prove2me | solution 1 for GraphAlignment.Possible.lemma_B_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:06:15.222066+00:00
-- url     : https://prove2.me/submissions/d863d307-484b-4998-b488-99bdf22c8edf

import Mathlib
set_option autoImplicit false

open Polynomial in
theorem solution {𝕜 : Type*} [Field 𝕜] (M : Matrix (Fin 2) (Fin 2) 𝕜) (α β : 𝕜)
    (hM : M.charpoly = (X - C α) * (X - C β)) (hαβ : α ≠ β) (n : ℕ) (hn : 1 ≤ n) :
    M ^ n = (α ^ n / (α - β)) • (M - β • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) +
      (β ^ n / (β - α)) • (M - α • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) := by
  have hch := Matrix.aeval_self_charpoly M
  rw [hM] at hch
  have h : (M - α • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) * (M - β • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) = 0 := by
    simpa [Algebra.algebraMap_eq_smul_one] using hch
  have hc : (M - β • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) * (M - α • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) = 0 := by
    rw [← h]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    module
  -- eigen-relations
  have key : ∀ (a b : 𝕜) (hh : (M - a • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) * (M - b • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) = 0) (k : ℕ),
      M ^ k * (M - b • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) = a ^ k • (M - b • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) := by
    intro a b hh k
    have h1 : M * (M - b • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) = a • (M - b • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) := by
      have := hh
      rw [sub_mul, smul_mul_assoc, one_mul, sub_eq_zero] at this
      exact this
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_assoc, h1, mul_smul_comm, ih, smul_smul, pow_succ, mul_comm a]
  have hA := key α β h n
  have hB := key β α hc n
  have hsub : α - β ≠ 0 := sub_ne_zero.mpr hαβ
  have hsub' : β - α ≠ 0 := sub_ne_zero.mpr hαβ.symm
  have hone : (α - β)⁻¹ • (M - β • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) +
      (β - α)⁻¹ • (M - α • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) = 1 := by
    have e : (β - α)⁻¹ = -(α - β)⁻¹ := by
      rw [← neg_sub α β, inv_neg]
    rw [e, neg_smul, ← sub_eq_add_neg, ← smul_sub]
    have : (M - β • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) - (M - α • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) = (α - β) • 1 := by
      rw [sub_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ hsub, one_smul]
  calc M ^ n = M ^ n * 1 := (mul_one _).symm
    _ = M ^ n * ((α - β)⁻¹ • (M - β • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) +
      (β - α)⁻¹ • (M - α • (1 : Matrix (Fin 2) (Fin 2) 𝕜))) := by rw [hone]
    _ = _ := by
      rw [mul_add, mul_smul_comm, mul_smul_comm, hA, hB, smul_smul, smul_smul, div_eq_mul_inv, div_eq_mul_inv, mul_comm ((α - β)⁻¹), mul_comm ((β - α)⁻¹)]
