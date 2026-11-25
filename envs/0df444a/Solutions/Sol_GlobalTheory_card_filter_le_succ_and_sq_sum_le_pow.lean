-- Prove2me | solution 1 for GlobalTheory.card_filter_le_succ_and_sq_sum_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:15.85752+00:00
-- url     : https://prove2.me/submissions/e3bbe934-c24c-4b20-9902-8398765d6716

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterLeSuccAndSqSumLePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (n kk : ℕ) (bv : ℝ), 1 ≤ kk → kk + 1 ≤ n → (n : ℝ) ≤ bv → (univ.filter fun a : Fin n => kk ≤ a.val + 1).card = n + 1 - kk ∧ (18 / 13 : ℝ) ^ 2 + ((n + 1 - kk : ℕ) : ℝ) * (3 * (6 * bv) ^ (n - kk)) ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) := by
  intro n kk bv h1 h2 h3
  refine ⟨?_, ?_⟩
  · have hlt : kk - 1 < n := by omega
    have : (univ.filter fun a : Fin n => kk ≤ a.val + 1) = Finset.Ici (⟨kk - 1, hlt⟩ : Fin n) := by
      ext a
      simp only [mem_filter, mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
      omega
    rw [this, Fin.card_Ici]
    simp only
    omega
  · have e1 : n + 1 - kk = (n - kk) + 1 := by omega
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hM : ((n + 1 - kk : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n + 1 - kk ≤ n)
    have hb : (2 : ℝ) ≤ bv := hn2.trans h3
    have hX : (1 : ℝ) ≤ (6 * bv) ^ (n - kk) := one_le_pow₀ (by linarith)
    have e2 : (6 * bv) ^ (2 * (n + 1 - kk)) = 36 * bv ^ 2 * ((6 * bv) ^ (n - kk)) ^ 2 := by
      rw [e1]; ring
    rw [e2]
    set X := (6 * bv) ^ (n - kk)
    set c := ((n + 1 - kk : ℕ) : ℝ)
    have hX2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ hX
    have hc : c ≤ bv := hM.trans h3
    have h4 : c * X ^ 2 ≤ bv * X ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
    have h5 : (9 * bv + 2) * X ^ 2 ≤ 36 * bv ^ 2 * X ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    nlinarith
end GlobalTheory
