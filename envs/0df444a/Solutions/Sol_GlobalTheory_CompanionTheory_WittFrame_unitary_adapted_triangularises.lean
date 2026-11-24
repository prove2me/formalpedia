-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:39:45.40532+00:00
-- url     : https://prove2.me/submissions/7717dc02-a4b4-4975-a220-17ba5dc31f09

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryExtensionOfBlock
import Theorems.Thm_GlobalTheory_CompanionTheory_WittFrame_unitary_of_blocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WittFrame
namespace GlobalTheory.CompanionTheory.WittFrame
theorem _root_.solution : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ),
    J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' →
    Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 →
    ∀ U₀ ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      ∀ (s : Matrix (Fin n) (Fin n) ℂ) (b b' : Matrix (Fin D) (Fin D) ℂ)
        (t : Matrix (Fin m) (Fin m) ℂ),
        s * C = C * b → s * (R * U₀) = (R * U₀) * t → s * (J * C) = (J * C) * b' →
        b.BlockTriangular id → t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) →
        (Uᴴ * s * U).BlockTriangular id := by
  intro n D m J J' C R hJJ hJh hCC hCJC hRR hJR hCR hsum U₀ hU₀
  have hU : U₀ᴴ * U₀ = 1 := (Matrix.mem_unitaryGroup_iff').1 hU₀
  have hRC : Rᴴ * C = 0 := by
    have := congrArg conjTranspose hCR
    simpa [conjTranspose_mul] using this
  have hRJ : Rᴴ * J = J'ᴴ * Rᴴ := by
    have := congrArg conjTranspose hJR
    simpa [conjTranspose_mul, hJh] using this
  have t1 : trace (C * Cᴴ) = (D : ℂ) := by
    rw [trace_mul_comm, hCC, trace_one]; simp
  have t2 : trace (J * C * Cᴴ * J) = (D : ℂ) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul, t1]
  have t3 : trace (R * Rᴴ) = (m : ℂ) := by
    rw [trace_mul_comm, hRR, trace_one]; simp
  have hcard : D + (m + D) = n := by
    have h := congrArg trace hsum
    rw [trace_add, trace_add, t1, t2, t3, trace_one] at h
    simp only [Fintype.card_fin] at h
    have h' : ((D + D + m : ℕ) : ℂ) = (n : ℂ) := by push_cast; exact h
    have h'' : D + D + m = n := by exact_mod_cast h'
    omega
  refine unitary_of_blocks C (J * C) (R * U₀) hCC ?_ ?_ ?_ ?_ ?_ hcard
  · rw [← Matrix.mul_assoc, hCR, Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, hCJC]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ, hRR, Matrix.one_mul, hU]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ, hRJ, Matrix.mul_assoc, hRC]
    simp
  · rw [conjTranspose_mul, hJh, Matrix.mul_assoc, ← Matrix.mul_assoc J, hJJ, Matrix.one_mul, hCC]
end GlobalTheory.CompanionTheory.WittFrame
