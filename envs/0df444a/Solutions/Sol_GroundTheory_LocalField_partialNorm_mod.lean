-- Prove2me | solution 1 for GroundTheory.LocalField.partialNorm_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:20.156478+00:00
-- url     : https://prove2.me/submissions/e22c146a-75b4-44c4-bd65-05f87eb70519

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Theorems.Thm_GroundTheory_LocalField_partialNorm_add_orderOf
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable (σ : L ≃ₐ[K] L) (x : Lˣ)
variable {σ}
variable (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1)
include hσ hx
namespace GroundTheory.LocalField
theorem _root_.solution (m : ℕ) : partialNorm σ x (m % orderOf σ) = partialNorm σ x m := by
  conv_rhs => rw [← Nat.mod_add_div m (orderOf σ)]
  induction m / orderOf σ with
  | zero => simp
  | succ q ih => rw [mul_add, mul_one, ← add_assoc, partialNorm_add_orderOf hσ hx, ih]
end GroundTheory.LocalField
