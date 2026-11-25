-- Prove2me | solution 1 for GlobalTheory.StableSubset.four_le_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:11:59.19447+00:00
-- url     : https://prove2.me/submissions/c0c36fb1-97af-4572-8a3c-7c577e8accde

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
theorem _root_.solution {N : ℕ} (A : Finset (Fin N)) (σ : Perm (Fin N))
    (h : A.map σ.toEmbedding = A) : 4 ≤ wt A σ := by
  unfold wt
  rw [if_pos h]
  split_ifs <;> omega
end GlobalTheory.StableSubset
