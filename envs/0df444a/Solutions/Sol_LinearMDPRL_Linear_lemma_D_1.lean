-- Prove2me | solution 1 for LinearMDPRL.Linear.lemma_D_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-14T04:49:28.261202+00:00
-- url     : https://prove2.me/submissions/c0759672-8cdb-4560-898d-36eb7e15bd28

import Mathlib

open Matrix

theorem solution (d t : ℕ) (lam : ℝ) (hlam : 0 < lam) (φ : ℕ → Fin d → ℝ) :
    ∑ i ∈ Finset.Icc 1 t,
        φ i ⬝ᵥ ((lam • (1 : Matrix (Fin d) (Fin d) ℝ) +
          ∑ j ∈ Finset.Icc 1 t, vecMulVec (φ j) (φ j))⁻¹ *ᵥ φ i) ≤ d := by
  classical
  set Λ : Matrix (Fin d) (Fin d) ℝ := lam • (1 : Matrix (Fin d) (Fin d) ℝ) +
      ∑ j ∈ Finset.Icc 1 t, vecMulVec (φ j) (φ j) with hΛdef
  set B : Matrix (Fin d) (Fin d) ℝ := ∑ j ∈ Finset.Icc 1 t, vecMulVec (φ j) (φ j) with hBdef
  have hΛ : Λ.PosDef := by
    rw [hΛdef]
    apply Matrix.PosDef.add_posSemidef
    · exact Matrix.PosDef.one.smul hlam
    · rw [hBdef]
      apply Matrix.posSemidef_sum
      intro i _
      simpa using Matrix.posSemidef_vecMulVec_self_star (φ i)
  have hunit : IsUnit Λ.det := (Matrix.isUnit_iff_isUnit_det Λ).mp hΛ.isUnit
  have hterm : ∀ i, φ i ⬝ᵥ (Λ⁻¹ *ᵥ φ i) = (Λ⁻¹ * vecMulVec (φ i) (φ i)).trace := by
    intro i
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  have hsum : ∑ i ∈ Finset.Icc 1 t, φ i ⬝ᵥ (Λ⁻¹ *ᵥ φ i) = (Λ⁻¹ * B).trace := by
    calc ∑ i ∈ Finset.Icc 1 t, φ i ⬝ᵥ (Λ⁻¹ *ᵥ φ i)
        = ∑ i ∈ Finset.Icc 1 t, (Λ⁻¹ * vecMulVec (φ i) (φ i)).trace := by
          exact Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (∑ i ∈ Finset.Icc 1 t, Λ⁻¹ * vecMulVec (φ i) (φ i)).trace := by
          rw [Matrix.trace_sum]
      _ = (Λ⁻¹ * ∑ i ∈ Finset.Icc 1 t, vecMulVec (φ i) (φ i)).trace := by
          rw [Matrix.mul_sum]
      _ = (Λ⁻¹ * B).trace := by rw [hBdef]
  have hB : B = Λ - lam • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [hΛdef, hBdef]
    abel
  have hkey : (Λ⁻¹ * B).trace = (d : ℝ) - lam * Λ⁻¹.trace := by
    rw [hB, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      Matrix.nonsing_inv_mul Λ hunit, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_one]
    simp
  rw [hsum, hkey]
  have htr : 0 ≤ Λ⁻¹.trace := Matrix.PosSemidef.trace_nonneg hΛ.inv.posSemidef
  nlinarith
