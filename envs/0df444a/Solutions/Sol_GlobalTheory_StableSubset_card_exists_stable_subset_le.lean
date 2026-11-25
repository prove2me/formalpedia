-- Prove2me | solution 1 for GlobalTheory.StableSubset.card_exists_stable_subset_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:07:26.859839+00:00
-- url     : https://prove2.me/submissions/14b338b9-6f09-4fe2-89b4-83a7dfcd39a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermExistsStableSubsetLe
import Theorems.Thm_GlobalTheory_StableSubset_sum_wt_le
import Theorems.Thm_GlobalTheory_StableSubset_eight_le_sum_wt

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
theorem _root_.solution : ∀ N a : ℕ, 0 < a → a < N →
    8 * (Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      ∃ A : Finset (Fin N), A.card = a ∧ A.map σ.toEmbedding = A).card ≤ 7 * N.factorial := by
  intro N a h0 hN
  calc _ ≤ ∑ σ : Perm (Fin N), ∑ B ∈ powersetCard a (univ : Finset (Fin N)), wt B σ := by
        rw [Finset.card_filter, Finset.mul_sum]
        refine Finset.sum_le_sum fun σ _ => ?_
        split_ifs with h
        · obtain ⟨A, hA, h⟩ := h
          exact eight_le_sum_wt σ A hA h
        · simp
    _ = ∑ B ∈ powersetCard a (univ : Finset (Fin N)), ∑ σ : Perm (Fin N), wt B σ :=
        Finset.sum_comm
    _ ≤ ∑ B ∈ powersetCard a (univ : Finset (Fin N)),
          7 * (a.factorial * (N - a).factorial) := by
        refine Finset.sum_le_sum fun B hB => ?_
        have hB' : B.card = a := (Finset.mem_powersetCard.1 hB).2
        have := sum_wt_le B (by omega) (by omega)
        rwa [hB'] at this
    _ = 7 * N.factorial := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, ← Nat.choose_mul_factorial_mul_factorial hN.le]
        ring
end GlobalTheory.StableSubset
