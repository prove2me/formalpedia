-- Prove2me | solution 1 for GroundTheory.LocalField.partialNorm_eq_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:11.199476+00:00
-- url     : https://prove2.me/submissions/cbdec236-ee67-4d90-8523-e845e4468fb6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Theorems.Thm_GroundTheory_LocalField_partialNorm_mod

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
theorem _root_.solution {a b : ℕ} (h : σ ^ a = σ ^ b) :
    partialNorm σ x a = partialNorm σ x b := by
  rw [← partialNorm_mod hσ hx a, ← partialNorm_mod hσ hx b, (pow_eq_pow_iff_modEq.mp h)]
end GroundTheory.LocalField
