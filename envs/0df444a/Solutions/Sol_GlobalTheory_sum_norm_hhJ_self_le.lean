-- Prove2me | solution 1 for GlobalTheory.sum_norm_hhJ_self_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:19:52.15182+00:00
-- url     : https://prove2.me/submissions/956133ee-c39b-4069-8869-40f3b88cb043

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormHhJSelfLe
import Theorems.Thm_GlobalTheory_hhJ_self_norm_le_sum_sq
import Theorems.Thm_GlobalTheory_hhJ_self_im_eq_zero
import Theorems.Thm_GlobalTheory_hhJ_finsum_finsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (y : Fin n → Fin n → M) (In : Finset (Fin n)) (Cc Cs Nn : ℝ), (∀ s t, s ≠ t → hhJ ε (y s) (y t) = 0) → (∀ s ∈ In, 0 ≤ (hhJ ε (y s) (y s)).re) → ∑ c, ‖(∑ s ∈ In, y s) c‖ ^ 2 ≤ Cc ^ 2 * Nn → (∀ s, s ∉ In → ∑ c, ‖y s c‖ ^ 2 ≤ Cs ^ 2 * Nn) → ∑ s, ‖hhJ ε (y s) (y s)‖ ≤ (Cc ^ 2 + (Inᶜ.card : ℝ) * Cs ^ 2) * Nn := by
  intro M _ _ n ε y In Cc Cs Nn horth hpos hIn hout
  rw [← Finset.sum_add_sum_compl In]
  have h1 : hhJ ε (∑ s ∈ In, y s) (∑ s ∈ In, y s) = ∑ s ∈ In, hhJ ε (y s) (y s) := by
    rw [hhJ_finsum_finsum]
    refine Finset.sum_congr rfl fun s hs => ?_
    exact Finset.sum_eq_single_of_mem s hs fun t _ hts => horth s t (Ne.symm hts)
  have h2 : ∑ s ∈ In, ‖hhJ ε (y s) (y s)‖ = (∑ s ∈ In, hhJ ε (y s) (y s)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← Complex.abs_re_eq_norm.mpr (hhJ_self_im_eq_zero ε (y s)), abs_of_nonneg (hpos s hs)]
  have h3 : ∑ s ∈ In, ‖hhJ ε (y s) (y s)‖ ≤ Cc ^ 2 * Nn := by
    rw [h2, ← h1]
    exact (Complex.re_le_norm _).trans ((hhJ_self_norm_le_sum_sq ε _).trans hIn)
  have h4 : ∑ s ∈ Inᶜ, ‖hhJ ε (y s) (y s)‖ ≤ (Inᶜ.card : ℝ) * (Cs ^ 2 * Nn) := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun s hs => ?_
    exact (hhJ_self_norm_le_sum_sq ε _).trans (hout s (Finset.mem_compl.mp hs))
  calc _ ≤ Cc ^ 2 * Nn + (Inᶜ.card : ℝ) * (Cs ^ 2 * Nn) := add_le_add h3 h4
    _ = _ := by ring
end GlobalTheory
