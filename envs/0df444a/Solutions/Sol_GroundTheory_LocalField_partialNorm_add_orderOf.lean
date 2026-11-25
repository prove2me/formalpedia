-- Prove2me | solution 1 for GroundTheory.LocalField.partialNorm_add_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:56.432673+00:00
-- url     : https://prove2.me/submissions/bae644f2-534e-4ede-b924-db2cc91c7823

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Theorems.Thm_GroundTheory_LocalField_partialNorm_add
import Theorems.Thm_GroundTheory_LocalField_partialNorm_orderOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable (σ : L ≃ₐ[K] L) (x : Lˣ)
variable {σ}
variable (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1)
include hσ hx
namespace GroundTheory.LocalField
theorem _root_.solution (m : ℕ) :
    partialNorm σ x (m + orderOf σ) = partialNorm σ x m := by
  rw [add_comm, partialNorm_add, partialNorm_orderOf x hσ, hx, pow_orderOf_eq_one, one_smul, one_mul]
end GroundTheory.LocalField
