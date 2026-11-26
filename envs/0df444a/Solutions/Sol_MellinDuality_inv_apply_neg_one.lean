-- Prove2me | solution 1 for MellinDuality.inv_apply_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:29.687803+00:00
-- url     : https://prove2.me/submissions/32ce95a3-6a89-4639-bb17-f637b5bee849

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
theorem _root_.solution (ψ : MulChar (ZMod p) R) : ψ⁻¹ (-1) = ψ (-1) := by
  rw [MulChar.inv_apply', inv_neg, inv_one]
end MellinDuality
