-- Prove2me | solution 1 for MellinDuality.sum_mul_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:10.944461+00:00
-- url     : https://prove2.me/submissions/5eb284cc-55a5-4b7e-8c8f-b38dba906f1d

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
public import Theorems.Thm_MellinDuality_two_ne_zero_zmod

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ x, f x = ∑ y, f (2 * y) :=
  (Fintype.sum_bijective _ (Equiv.mulLeft₀ (2 : ZMod p) (two_ne_zero_zmod hp2)).bijective
    (fun y => f (2 * y)) f fun _ => rfl).symm
end MellinDuality
