-- Prove2me | solution 1 for ModernConvex.Truss.observation_O
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:40:40.544001+00:00
-- url     : https://prove2.me/submissions/005be2a2-4dea-49b8-aecd-544877e8eeab

import Mathlib
import Definitions.Def_ModernConvex_Truss_Compliance

open Matrix

open ModernConvex.Truss

theorem g69a1_q_eq {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (v : Fin m → ℝ) :
    v ⬝ᵥ (stiffness B t *ᵥ v) = ∑ i, t i * ∑ j, ((B i)ᵀ *ᵥ v) j ^ 2 := by
  unfold stiffness
  rw [sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, ← mulVec_mulVec, dotProduct_mulVec,
    ← mulVec_transpose]
  simp [dotProduct, sq]

theorem g69a1_N_eq {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (ht : 0 ≤ t)
    (v : Fin m → ℝ) :
    ∑ r, (stackedMatrix B t *ᵥ v) r ^ 2 = 2 * ∑ i, t i * ∑ j, ((B i)ᵀ *ᵥ v) j ^ 2 := by
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h : (stackedMatrix B t *ᵥ v) ⟨i, j⟩ = Real.sqrt 2 * Real.sqrt (t i) * ((B i)ᵀ *ᵥ v) j := by
    simp only [stackedMatrix, mulVec, dotProduct, of_apply, transpose_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [h, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (ht i)]
  ring

theorem solution {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (ht : 0 ≤ t)
    (f : Fin m → ℝ) (τ : ℝ) :
    (¬ ∃ v : Fin m → ℝ, (1 / 2 : ℝ) * (v ⬝ᵥ (stiffness B t *ᵥ v)) - f ⬝ᵥ v + τ ≤ 0) ↔
    (¬ ∃ v : Fin m → ℝ,
      Real.sqrt (∑ r, (stackedMatrix B t *ᵥ v) r ^ 2 + (1 - f ⬝ᵥ v + τ) ^ 2) ≤ 1 + f ⬝ᵥ v - τ) := by
  have key : ∀ v : Fin m → ℝ, (1 / 2 : ℝ) * (v ⬝ᵥ (stiffness B t *ᵥ v)) - f ⬝ᵥ v + τ ≤ 0 ↔
      Real.sqrt (∑ r, (stackedMatrix B t *ᵥ v) r ^ 2 + (1 - f ⬝ᵥ v + τ) ^ 2) ≤
        1 + f ⬝ᵥ v - τ := by
    intro v
    rw [g69a1_N_eq B t ht v, ← g69a1_q_eq B t v, Real.sqrt_le_iff]
    have hq : 0 ≤ v ⬝ᵥ (stiffness B t *ᵥ v) := by
      rw [g69a1_q_eq]
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (ht i) (Finset.sum_nonneg fun j _ => sq_nonneg _)
    constructor
    · intro h
      constructor
      · linarith
      · nlinarith
    · rintro ⟨h1, h2⟩
      nlinarith
  constructor
  · rintro h ⟨v, hv⟩; exact h ⟨v, (key v).mpr hv⟩
  · rintro h ⟨v, hv⟩; exact h ⟨v, (key v).mp hv⟩
