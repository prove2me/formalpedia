-- Prove2me | solution 1 for MellinDuality.half_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:10.281451+00:00
-- url     : https://prove2.me/submissions/3f7fa662-9c45-4295-8897-4833006068a3

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_bernoulli_form


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {R : Type*} [CommRing R] (hp2 : p ≠ 2) (ψ : MulChar (ZMod p) R) (hψ : ψ (-1) = -1) :
    (p : R) * G ψ = 2 * (1 - 2 * ψ 2) * T ψ :=
  bernoulli_form hp2 ψ hψ
end MellinDuality
