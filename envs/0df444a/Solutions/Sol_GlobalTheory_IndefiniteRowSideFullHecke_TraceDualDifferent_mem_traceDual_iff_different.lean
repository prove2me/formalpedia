-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff_different
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:55:53.584415+00:00
-- url     : https://prove2.me/submissions/44733fc7-d9c3-444c-9893-1a0c31c29ec3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TraceDualDifferent_mem_traceDual_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
theorem _root_.solution {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) (y : F) :
    y ∈ traceDual M ↔ y ∈ ((differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F))⁻¹ * M⁻¹ := by
  rw [mem_traceDual_iff hM, FractionalIdeal.dual_eq_mul_inv, coeIdeal_differentIdeal ℤ ℚ F (𝓞 F), inv_inv]
end GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
