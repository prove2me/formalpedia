-- Prove2me | solution 1 for GlobalTheory.StableSubset.sum_wt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:25:00.826372+00:00
-- url     : https://prove2.me/submissions/2e443251-9283-4111-a94b-81ffbc094c96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermExistsStableSubsetLe
import Theorems.Thm_GlobalTheory_StableSubset_card_stab_le
import Theorems.Thm_GlobalTheory_StableSubset_card_fix_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.StableSubset
open Finset Equiv
namespace GlobalTheory.StableSubset
theorem _root_.solution {N : ℕ} (A : Finset (Fin N)) (h0 : 0 < A.card) (hN : A.card < N) :
    ∑ σ, wt A σ ≤ 7 * (A.card.factorial * (N - A.card).factorial) := by
  have h1 := card_stab_le A
  have h2 := card_fix_ge A h0 hN
  have h3 : ∑ σ, wt A σ + 4 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A ∧
        (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j).card =
      8 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    unfold wt
    by_cases ha : A.map σ.toEmbedding = A <;>
      by_cases hb : (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j <;> simp only [ha, hb] <;> simp
  omega
end GlobalTheory.StableSubset
