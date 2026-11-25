-- Prove2me | solution 1 for GlobalTheory.StableSubset.mem_iff_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:07:13.20967+00:00
-- url     : https://prove2.me/submissions/e14560cf-6979-4775-8d7e-d87715cdf76e

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
    (h : A.map σ.toEmbedding = A) (x : Fin N) : σ x ∈ A ↔ x ∈ A := by
  conv_lhs => rw [← h]
  exact Finset.mem_map' σ.toEmbedding
end GlobalTheory.StableSubset
