-- Prove2me | solution 1 for MellinDuality.apply_neg_one_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:14.352191+00:00
-- url     : https://prove2.me/submissions/a57a0f81-b8fc-4797-9b69-90c412267f99

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]
namespace MellinDuality
theorem _root_.solution (ψ : MulChar (ZMod p) R) : ψ (-1) ^ 2 = 1 := by
  rw [← map_pow, neg_one_sq, map_one]
end MellinDuality
