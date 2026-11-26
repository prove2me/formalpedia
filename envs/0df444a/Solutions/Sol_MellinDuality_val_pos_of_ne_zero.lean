-- Prove2me | solution 1 for MellinDuality.val_pos_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:52.627653+00:00
-- url     : https://prove2.me/submissions/19492401-9f3d-4093-8108-d103be869cee

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) : 0 < x.val := by
  rw [Nat.pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]; exact hx
end MellinDuality
