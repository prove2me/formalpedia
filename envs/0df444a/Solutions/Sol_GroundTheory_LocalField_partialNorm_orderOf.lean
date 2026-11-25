-- Prove2me | solution 1 for GroundTheory.LocalField.partialNorm_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:21.485355+00:00
-- url     : https://prove2.me/submissions/c2e5c5f2-59cd-40c2-b5c5-946fb00d6a70

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Theorems.Thm_GroundTheory_LocalField_tateNorm_apply


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
namespace GroundTheory.LocalField
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    partialNorm σ x (orderOf σ) = tateNorm (L ≃ₐ[K] L) Lˣ x := by
  rw [partialNorm, ← Fin.prod_univ_eq_prod_range, tateNorm_apply]
  refine Fintype.prod_bijective (fun j : Fin (orderOf σ) => σ ^ (j : ℕ)) ⟨?_, ?_⟩ _ _
    (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 hij)
  · intro g
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := σ) (y := g)).mpr (hσ g)
    refine ⟨⟨k % orderOf σ, Nat.mod_lt _ (orderOf_pos σ)⟩, ?_⟩
    change σ ^ (k % orderOf σ) = g
    rw [pow_mod_orderOf]
    exact hk
end GroundTheory.LocalField
