-- Prove2me | solution 1 for GlobalTheory.FixedRoots.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:44:41.135904+00:00
-- url     : https://prove2.me/submissions/6cced60a-5e0a-4555-9185-399ac76a92de

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FixedByAutomorphismInField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRingEquivAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemOfForallRingEquivFixed
import Theorems.Thm_GlobalTheory_FixedRoots_coeff_prod_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.FixedRoots
namespace GlobalTheory.FixedRoots
theorem _root_.solution : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (k : Subfield Ω) (S : Finset Ω),
    (∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → ∀ x ∈ S, σ x ∈ S) → ∀ n,
      (∏ x ∈ S, (X - C x)).coeff n ∈ k :=
  fun _ _ _ _ k S hS n => coeff_prod_mem k S hS n
end GlobalTheory.FixedRoots
