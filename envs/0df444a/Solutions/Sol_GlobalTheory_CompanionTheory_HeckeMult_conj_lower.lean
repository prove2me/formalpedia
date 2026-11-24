-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMult.conj_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:36:58.523649+00:00
-- url     : https://prove2.me/submissions/3edca82b-6175-4c47-b319-78c91de6581b

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
theorem _root_.solution {n : ℕ} {I : Ideal R} (ϖ : R) (hϖ : algebraMap R K ϖ ≠ 0) (b : Fin n → ℤ)
    (hb : Antitone b) (L : Matrix (Fin n) (Fin n) R) (hL : CongOne I L)
    (hLt : ∀ i j, i < j → L i j = 0) :
    ∃ V : Matrix (Fin n) (Fin n) R, CongOne I V ∧
      L.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (b i))
        = Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (b i)) * V.map (algebraMap R K) := by
  refine ⟨Matrix.of fun i j => L i j * ϖ ^ (b j - b i).toNat, ?_, ?_⟩
  · intro i j
    rw [Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [Matrix.one_apply_ne h.ne, sub_zero, hLt i j h, zero_mul]
      exact I.zero_mem
    · subst h
      simpa using hL i i
    · rw [Matrix.one_apply_ne h.ne', sub_zero]
      have := hL i j
      rw [Matrix.one_apply_ne h.ne', sub_zero] at this
      exact I.mul_mem_right _ this
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, map_pow]
    rcases lt_or_ge i j with h | h
    · simp [hLt i j h]
    · have hnn : 0 ≤ b j - b i := sub_nonneg.mpr (hb h)
      have : (algebraMap R K ϖ) ^ (b j) = (algebraMap R K ϖ) ^ (b j - b i).toNat * (algebraMap R K ϖ) ^ (b i) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← zpow_add₀ hϖ]
        congr 1; ring
      rw [this]; ring
end GlobalTheory.CompanionTheory.HeckeMult
