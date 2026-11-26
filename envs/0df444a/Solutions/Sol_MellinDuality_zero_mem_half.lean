-- Prove2me | solution 1 for MellinDuality.zero_mem_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:51.114482+00:00
-- url     : https://prove2.me/submissions/34d29c68-39ff-47c9-88b0-0ca70414ad7a

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
namespace MellinDuality
theorem _root_.solution : (0 : ZMod p) ∈ half p := by
  rw [mem_half_iff, ZMod.val_zero]; exact hp.out.pos
end MellinDuality
