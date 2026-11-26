-- Prove2me | solution 1 for MellinDuality.apply_neg_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:52.10764+00:00
-- url     : https://prove2.me/submissions/ec979db9-9010-4f1f-b6c2-fccd299657d2

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]
namespace MellinDuality
theorem _root_.solution (φ : MulChar (ZMod p) R) (hφ : φ (-1) = -1) (x : ZMod p) :
    φ (-x) = -φ x := by
  rw [neg_eq_neg_one_mul, map_mul, hφ]; ring
end MellinDuality
