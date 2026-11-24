-- Prove2me | solution 1 for GlobalTheory.Doubling.leviElt_mem_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:14.480657+00:00
-- url     : https://prove2.me/submissions/2a7303c6-9dab-45a8-afc3-140c654016c6

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_pairVec_mem_antiSub
import Theorems.Thm_GlobalTheory_Doubling_mem_antiSub
import Theorems.Thm_GlobalTheory_Doubling_leviElt_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
variable [Invertible (2 : A)]
namespace GlobalTheory.Doubling
theorem _root_.solution (g : GL n A × GL n A) : leviElt e g ∈ stabGL (antiSub A e) := by
  have h : ∀ g : GL n A × GL n A, ∀ w ∈ antiSub A e, (leviElt e g).1 *ᵥ w ∈ antiSub A e := fun g w hw => by
    obtain ⟨x, rfl⟩ := (mem_antiSub e).1 hw
    rw [leviElt_anti, pairVec_mem_antiSub, neg_neg]
  refine fun w => ⟨h g w, fun hw => ?_⟩
  have := h g⁻¹ _ hw
  rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at this
end GlobalTheory.Doubling
