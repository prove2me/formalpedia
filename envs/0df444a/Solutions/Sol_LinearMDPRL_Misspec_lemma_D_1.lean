-- Prove2me | solution 1 for LinearMDPRL.Misspec.lemma_D_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:14:56.089745+00:00
-- url     : https://prove2.me/submissions/7dfd5b93-e588-4c79-b607-c18c5e0ccabb

import Mathlib
set_option autoImplicit false
open Matrix

theorem solution {d : ℕ} (lam : ℝ) (hlam : 0 < lam) (t : ℕ) (φ : ℕ → Fin d → ℝ) :
    ∑ i ∈ Finset.Icc 1 t,
        φ i ⬝ᵥ (lam • (1 : Matrix (Fin d) (Fin d) ℝ) +
          ∑ j ∈ Finset.Icc 1 t, vecMulVec (φ j) (φ j))⁻¹ *ᵥ φ i ≤ d := by
  classical
  set S : Matrix (Fin d) (Fin d) ℝ := ∑ j ∈ Finset.Icc 1 t, vecMulVec (φ j) (φ j) with hS
  set Λ : Matrix (Fin d) (Fin d) ℝ := lam • (1 : Matrix (Fin d) (Fin d) ℝ) + S with hΛ
  have hSpsd : S.PosSemidef := by
    apply Matrix.posSemidef_sum
    intro j _
    simpa using Matrix.posSemidef_vecMulVec_self_star (φ j)
  have hΛpd : Λ.PosDef := (Matrix.PosDef.one.smul hlam).add_posSemidef hSpsd
  have hdet : IsUnit Λ.det := (Matrix.isUnit_iff_isUnit_det _).mp hΛpd.isUnit
  have hM : (Λ⁻¹).PosDef := hΛpd.inv
  have htr : 0 ≤ (Λ⁻¹).trace := hM.posSemidef.trace_nonneg
  have hq : ∀ x : Fin d → ℝ, x ⬝ᵥ (Λ⁻¹ *ᵥ x) = (Λ⁻¹ * vecMulVec x x).trace := by
    intro x
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have h1 : ∑ i ∈ Finset.Icc 1 t, φ i ⬝ᵥ (Λ⁻¹ *ᵥ φ i) = (Λ⁻¹ * S).trace := by
    simp only [hq]
    rw [hS, Matrix.mul_sum, Matrix.trace_sum]
  have h2 : Λ⁻¹ * S = 1 - lam • Λ⁻¹ := by
    have hSe : S = Λ - lam • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      rw [hΛ]; abel
    rw [hSe, Matrix.mul_sub, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_smul, Matrix.mul_one]
  have h3 : (Λ⁻¹ * S).trace = (d : ℝ) - lam * (Λ⁻¹).trace := by
    rw [h2, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp
  show ∑ i ∈ Finset.Icc 1 t, φ i ⬝ᵥ (Λ⁻¹ *ᵥ φ i) ≤ d
  rw [h1, h3]
  nlinarith [mul_nonneg hlam.le htr]
