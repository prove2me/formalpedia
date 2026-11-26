-- Prove2me | solution 1 for MellinDuality.val_two_mul_of_mem_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:06.507158+00:00
-- url     : https://prove2.me/submissions/d1b42fbc-db4e-4ae0-a503-4a789b63c07f

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
public import Theorems.Thm_MellinDuality_mem_half_iff

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]
namespace MellinDuality
theorem _root_.solution {n : ZMod p} (hn : n ∈ half p) : (2 * n).val = 2 * n.val := by
  rw [mem_half_iff] at hn
  have : (2 * n : ZMod p) = ((2 * n.val : ℕ) : ZMod p) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.val_natCast_of_lt hn]
end MellinDuality
