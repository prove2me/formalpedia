-- Prove2me | solution 1 for MellinDuality.pow_apply_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:47:06.997705+00:00
-- url     : https://prove2.me/submissions/2e9a0abc-fcb2-4e81-a46f-bd55dc19e5a6

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]
namespace MellinDuality
theorem _root_.solution (ψ : MulChar (ZMod p) R) (k : ℕ) {x : ZMod p} (hx : x ≠ 0) :
    (ψ ^ k) x = ψ x ^ k := by
  simpa using MulChar.pow_apply_coe ψ k (Units.mk0 x hx)
end MellinDuality
