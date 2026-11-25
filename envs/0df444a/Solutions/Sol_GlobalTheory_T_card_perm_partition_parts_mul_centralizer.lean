-- Prove2me | solution 1 for GlobalTheory.T.card_perm_partition_parts_mul_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:36:26.970221+00:00
-- url     : https://prove2.me/submissions/d86b31e5-3364-43e5-a757-f15119623951

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermPartitionPartsMulCentralizer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermPartitionPartsMulCentralizerStatement
import Theorems.Thm_GlobalTheory_BadShare_card_perm_partition_parts_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : ℕ) (μ : Multiset ℕ), (∀ d ∈ μ, 0 < d) → μ.sum = N → (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card * ∏ d ∈ μ.toFinset, (d ^ μ.count d * (μ.count d).factorial) = N.factorial := by
  first | exact @GlobalTheory.BadShare.card_perm_partition_parts_mul | exact GlobalTheory.BadShare.card_perm_partition_parts_mul | (intros; apply GlobalTheory.BadShare.card_perm_partition_parts_mul <;> assumption)
end _root_.GlobalTheory.T
