-- Prove2me | solution 1 for MellinDuality.parity_dictionary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:47.832975+00:00
-- url     : https://prove2.me/submissions/5fb0277e-4113-4e98-8895-6d0ecc895bcb

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_fam_one_eq_bandSumPow


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {R : Type*} [CommRing R] (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) {e : ℕ} (he : 1 ≤ e) :
    fam χ e 1 = bandSumPow χ e :=
  fam_one_eq_bandSumPow hp2 χ he
end MellinDuality
