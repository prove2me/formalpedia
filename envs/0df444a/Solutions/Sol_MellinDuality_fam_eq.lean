-- Prove2me | solution 1 for MellinDuality.fam_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:45:32.28824+00:00
-- url     : https://prove2.me/submissions/b867c6de-a369-4f99-8f48-8e0603a589d5

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
theorem _root_.solution (χ : MulChar (ZMod p) R) (e : ℕ) (a : ZMod p) :
    fam χ e a = ∑ n ∈ half p, χ n * (parSign n : R) * (parSign (a * n ^ e) : R) := by
  unfold fam parSign
  refine sum_congr rfl fun n _ => ?_
  rw [pow_add]; push_cast; ring
end MellinDuality
