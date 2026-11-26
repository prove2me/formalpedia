-- Prove2me | solution 1 for MellinDuality.neg_mem_half_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:57.529867+00:00
-- url     : https://prove2.me/submissions/13c2fc6b-5675-456c-a2a8-27b8203787a0

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
public import Theorems.Thm_MellinDuality_odd_p
public import Theorems.Thm_P2M_MellinDuality_val_neg_of_ne_zero__83959e09f3a6
public import Theorems.Thm_MellinDuality_val_pos_of_ne_zero
public import Theorems.Thm_MellinDuality_mem_half_iff

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) : -x ∈ half p ↔ x ∉ half p := by
  rw [mem_half_iff, mem_half_iff, val_neg_of_ne_zero' hx]
  have h1 := ZMod.val_lt x
  have h2 := val_pos_of_ne_zero hx
  obtain ⟨k, hk⟩ := odd_p hp2
  omega
end MellinDuality
