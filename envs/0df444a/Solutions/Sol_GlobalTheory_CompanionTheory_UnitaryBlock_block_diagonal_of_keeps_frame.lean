-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:38.572042+00:00
-- url     : https://prove2.me/submissions/23ca1c22-4914-4263-88ae-5af6145c687f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraStarClosedBracket

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnitaryBlock
namespace GlobalTheory.CompanionTheory.UnitaryBlock
theorem _root_.solution : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ)
    (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Rᴴ * R = 1 →
    J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 →
    ∀ (g : Matrix (Fin n) (Fin n) ℂ) (h : Matrix (Fin D) (Fin D) ℂ), gᴴ * J * g = J →
    g * C = C * h → gᴴ * C = C * hᴴ →
    IsUnit h ∧ g * (J * C) = (J * C) * (hᴴ)⁻¹ ∧ g * R = R * (Rᴴ * g * R) ∧
      (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R) = J' := by
  intro n D m J J' C R hJJ hJh hC hR hJR hCR hsum g h hg hgC hgHC
  have hl : (J * gᴴ * J) * g = 1 := by
    calc (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJJ]
  have hr : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.mp hl
  have hgJ : g * J * gᴴ = J := by
    calc g * J * gᴴ = g * (J * gᴴ * J) * J := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = J := by rw [hr, Matrix.one_mul]

  obtain ⟨k, hkdef⟩ : ∃ k, k = Cᴴ * (J * gᴴ * J) * C := ⟨_, rfl⟩
  have hk : k * h = 1 := by
    calc k * h = Cᴴ * (J * gᴴ * J) * (C * h) := by
          rw [hkdef]; simp only [Matrix.mul_assoc]
      _ = Cᴴ * ((J * gᴴ * J) * g) * C := by
          rw [← hgC]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hl, Matrix.mul_one, hC]
  have hk' : h * k = 1 := mul_eq_one_comm.mp hk
  have hunit : IsUnit h := ⟨⟨h, k, hk', hk⟩, rfl⟩
  have hdet : IsUnit hᴴ.det := by
    have : IsUnit hᴴ := by
      refine ⟨⟨hᴴ, kᴴ, ?_, ?_⟩, rfl⟩
      · rw [← Matrix.conjTranspose_mul, hk, Matrix.conjTranspose_one]
      · rw [← Matrix.conjTranspose_mul, hk', Matrix.conjTranspose_one]
    exact (Matrix.isUnit_iff_isUnit_det _).mp this
  have hJC : g * (J * C) * hᴴ = J * C := by
    calc g * (J * C) * hᴴ = g * J * (C * hᴴ) := by simp only [Matrix.mul_assoc]
      _ = g * J * gᴴ * C := by rw [← hgHC]; simp only [Matrix.mul_assoc]
      _ = J * C := by rw [hgJ]
  have hsecond : g * (J * C) = (J * C) * (hᴴ)⁻¹ := by
    calc g * (J * C) = g * (J * C) * (hᴴ * (hᴴ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = (g * (J * C) * hᴴ) * (hᴴ)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (J * C) * (hᴴ)⁻¹ := by rw [hJC]

  have hgpC : (J * gᴴ * J) * C = C * k := by
    calc (J * gᴴ * J) * C = (J * gᴴ * J) * C * (h * k) := by rw [hk', Matrix.mul_one]
      _ = (J * gᴴ * J) * (C * h) * k := by simp only [Matrix.mul_assoc]
      _ = ((J * gᴴ * J) * g) * C * k := by rw [← hgC]; simp only [Matrix.mul_assoc]
      _ = C * k := by rw [hl, Matrix.one_mul]
  have hCgR : Cᴴ * (g * R) = 0 := by
    have hadj : Cᴴ * g = h * Cᴴ := by
      have := congrArg Matrix.conjTranspose hgHC
      simpa [Matrix.conjTranspose_mul] using this
    calc Cᴴ * (g * R) = (Cᴴ * g) * R := by simp only [Matrix.mul_assoc]
      _ = h * (Cᴴ * R) := by rw [hadj, Matrix.mul_assoc]
      _ = 0 := by rw [hCR, Matrix.mul_zero]
  have hgHJC : gᴴ * J * C = J * C * k := by
    calc gᴴ * J * C = (J * J) * (gᴴ * J * C) := by rw [hJJ, Matrix.one_mul]
      _ = J * ((J * gᴴ * J) * C) := by simp only [Matrix.mul_assoc]
      _ = J * C * k := by rw [hgpC, Matrix.mul_assoc]
  have hCJg : Cᴴ * J * g = kᴴ * Cᴴ * J := by
    have := congrArg Matrix.conjTranspose hgHJC
    simpa [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hCJgR : Cᴴ * J * (g * R) = 0 := by
    calc Cᴴ * J * (g * R) = (Cᴴ * J * g) * R := by simp only [Matrix.mul_assoc]
      _ = kᴴ * Cᴴ * (J * R) := by rw [hCJg]; simp only [Matrix.mul_assoc]
      _ = kᴴ * (Cᴴ * R) * J' := by rw [hJR]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hCR, Matrix.mul_zero, Matrix.zero_mul]
  have hthird : g * R = R * (Rᴴ * g * R) := by
    calc g * R = (C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ) * (g * R) := by rw [hsum, Matrix.one_mul]
      _ = C * (Cᴴ * (g * R)) + J * C * (Cᴴ * J * (g * R)) + R * (Rᴴ * g * R) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = R * (Rᴴ * g * R) := by rw [hCgR, hCJgR]; simp
  refine ⟨hunit, hsecond, hthird, ?_⟩
  have hRJ : R * J' = J * R := hJR.symm
  have hRhJR : Rᴴ * J * R = J' := by
    calc Rᴴ * J * R = Rᴴ * (J * R) := by rw [Matrix.mul_assoc]
      _ = Rᴴ * R * J' := by rw [hJR, Matrix.mul_assoc]
      _ = J' := by rw [hR, Matrix.one_mul]
  calc (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R)
      = Rᴴ * gᴴ * (R * J') * (Rᴴ * g * R) := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = Rᴴ * gᴴ * J * (R * (Rᴴ * g * R)) := by rw [hRJ]; simp only [Matrix.mul_assoc]
    _ = Rᴴ * (gᴴ * J * g) * R := by rw [← hthird]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hg, hRhJR]
end GlobalTheory.CompanionTheory.UnitaryBlock
