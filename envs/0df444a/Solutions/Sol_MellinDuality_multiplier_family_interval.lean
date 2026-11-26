-- Prove2me | solution 1 for MellinDuality.multiplier_family_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:06:18.050706+00:00
-- url     : https://prove2.me/submissions/aa44a635-da2e-440a-aa6d-972c0c34bf84

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_fam_eq_Icc


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R)
    (a : ZMod p) :
    fam χ 2 a = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) *
      (((-1 : ℤ) ^ ((n : ZMod p).val + (a * (n : ZMod p) ^ 2).val) : ℤ) : R) :=
  fam_eq_Icc hp2 χ a
end MellinDuality
