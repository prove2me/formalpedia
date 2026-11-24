-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:37.657195+00:00
-- url     : https://prove2.me/submissions/ac33630c-060d-4f60-b366-de96ed5271a5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryLiftCommutingInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnitaryAssembly
namespace GlobalTheory.CompanionTheory.UnitaryAssembly
theorem _root_.solution : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ k₀ ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ kR ∈ Matrix.unitaryGroup (Fin m) ℂ, kR * J' = J' * kR → ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, k * J = J * k ∧ k * C = C * k₀ ∧ kᴴ * C = C * k₀ᴴ ∧ kᴴ * R = R * kRᴴ ∧ kᴴ * (J * C) = (J * C) * k₀ᴴ := by
  intro n D m J J' C R hJJ hJh hCC hCJC hRR hJR hCR hsum k₀ hk₀ kR hkR hkRJ
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at hk₀ hkR
  have hRC : Rᴴ * C = 0 := by
    have h := congrArg conjTranspose hCR
    simpa [conjTranspose_mul] using h
  have hJ'h : J'ᴴ = J' := by
    have h1 : J' = Rᴴ * (J * R) := by
      rw [hJR, ← Matrix.mul_assoc, hRR, Matrix.one_mul]
    rw [h1]
    simp [conjTranspose_mul, hJh, Matrix.mul_assoc]
  have hRJ : Rᴴ * J = J' * Rᴴ := by
    have h := congrArg conjTranspose hJR
    simpa only [conjTranspose_mul, hJh, hJ'h] using h
  have c2 : Cᴴ * (J * C) = 0 := by rw [← Matrix.mul_assoc]; exact hCJC
  have a1 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Cᴴ * (C * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]
  have a2 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Cᴴ * (J * (C * X)) = 0 := fun X => by
    rw [← Matrix.mul_assoc J C X, ← Matrix.mul_assoc, c2, Matrix.zero_mul]
  have a3 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), Cᴴ * (R * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, hCR, Matrix.zero_mul]
  have a4 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), Rᴴ * (R * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hRR, Matrix.one_mul]
  have a5 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Rᴴ * (C * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, hRC, Matrix.zero_mul]
  have a6 : ∀ {p : Type} (X : Matrix (Fin n) p ℂ), J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have a7 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), J * (R * X) = R * (J' * X) := fun X => by
    rw [← Matrix.mul_assoc, hJR, Matrix.mul_assoc]
  have a8 : ∀ {p : Type} (X : Matrix (Fin n) p ℂ), Rᴴ * (J * X) = J' * (Rᴴ * X) := fun X => by
    rw [← Matrix.mul_assoc, hRJ, Matrix.mul_assoc]
  have a9 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), k₀ * (k₀ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hk₀, Matrix.one_mul]
  have a10 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), kR * (kRᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hkR, Matrix.one_mul]
  have a11 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), kR * (J' * X) = J' * (kR * X) := fun X => by
    rw [← Matrix.mul_assoc, hkRJ, Matrix.mul_assoc]
  have hs : C * Cᴴ + J * (C * (Cᴴ * J)) + R * Rᴴ = 1 := by
    simpa only [Matrix.mul_assoc] using hsum
  refine ⟨C * k₀ * Cᴴ + J * C * k₀ * Cᴴ * J + R * kR * Rᴴ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
    simp only [Matrix.add_mul, Matrix.mul_add, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, hJh, Matrix.mul_assoc, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      hCC, c2, hCR, hRR, hRC, hJJ, hJR, hRJ, hk₀, hkR, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
    rw [← hs]
  all_goals
    simp only [Matrix.add_mul, Matrix.mul_add, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, hJh, Matrix.mul_assoc, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, hCC, c2, hCR, hRR, hRC, hJJ, hJR, hRJ, hk₀, hkR, hkRJ, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
    try abel
end GlobalTheory.CompanionTheory.UnitaryAssembly
