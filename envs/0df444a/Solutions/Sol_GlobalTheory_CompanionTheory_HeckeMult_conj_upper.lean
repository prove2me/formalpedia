-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMult.conj_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:36:59.565863+00:00
-- url     : https://prove2.me/submissions/4c926e06-168c-43e0-ba9c-6d4d416606e5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperLower
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_cc
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_cl
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_lc
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_ll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_cc
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_cl
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_lc
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_ll

set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMult
variable {R : Type} [CommRing R]
variable {K : Type} [Field K] [Algebra R K]
namespace GlobalTheory.CompanionTheory.HeckeMult
theorem _root_.solution {n : ℕ} {I : Ideal R} (ϖ : R) (hϖ : algebraMap R K ϖ ≠ 0) (a : Fin n → ℤ)
    (ha : Antitone a) (U : Matrix (Fin n) (Fin n) R) (hU : CongOne I U)
    (hUt : ∀ i j, j < i → U i j = 0) :
    ∃ V : Matrix (Fin n) (Fin n) R, CongOne I V ∧
      Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) * U.map (algebraMap R K)
        = V.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) := by
  refine ⟨Matrix.of fun i j => U i j * ϖ ^ (a i - a j).toNat, ?_, ?_⟩
  · intro i j
    rw [Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [Matrix.one_apply_ne h.ne, sub_zero]
      have := hU i j
      rw [Matrix.one_apply_ne h.ne, sub_zero] at this
      exact I.mul_mem_right _ this
    · subst h
      simpa using hU i i
    · rw [Matrix.one_apply_ne h.ne', sub_zero, hUt i j h, zero_mul]
      exact I.zero_mem
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, map_pow]
    rcases lt_or_ge j i with h | h
    · simp [hUt i j h]
    · have hnn : 0 ≤ a i - a j := sub_nonneg.mpr (ha h)
      have : (algebraMap R K ϖ) ^ (a i) = (algebraMap R K ϖ) ^ (a i - a j).toNat * (algebraMap R K ϖ) ^ (a j) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← zpow_add₀ hϖ]
        congr 1; ring
      rw [this]; ring
end GlobalTheory.CompanionTheory.HeckeMult
