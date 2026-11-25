-- Prove2me | solution 1 for GlobalTheory.NoFixedCharSum.noFixedSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:04:42.764531+00:00
-- url     : https://prove2.me/submissions/16f464e9-aa9d-42aa-bebb-1b07872ee3f4

import Mathlib
import Definitions.Def_Formalism_JacquetSubsetSums_JacquetSubsetSum
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumRepSubgroupEqZero
import Theorems.Thm_GlobalTheory_NoFixedCharSum_sum_rep_subgroup_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NoFixedCharSum
namespace GlobalTheory.NoFixedCharSum
theorem _root_.solution : Formalism.PacketSums.NoFixedSum := by
  intro G V _ _ _ _ τ N _ h x y
  have h0 := sum_rep_subgroup_eq_zero τ N h
  have : ∑ n : N, τ (x * (n : G) * y) = τ x * (∑ n : N, τ (n : G)) * τ y := by
    simp [Finset.mul_sum, Finset.sum_mul, map_mul]
  rw [← map_sum, this, h0]
  simp
end GlobalTheory.NoFixedCharSum
