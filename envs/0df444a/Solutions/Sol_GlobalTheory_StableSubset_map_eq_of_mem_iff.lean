-- Prove2me | solution 1 for GlobalTheory.StableSubset.map_eq_of_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:17:41.130889+00:00
-- url     : https://prove2.me/submissions/3f6fa13d-38b9-47df-adc7-22d46c5f6420

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermExistsStableSubsetLe

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
theorem _root_.solution {N : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N))
    (h : ∀ x, x ∈ A → σ x ∈ A) : A.map σ.toEmbedding = A := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
    exact h x hx
  · simp
end GlobalTheory.StableSubset
