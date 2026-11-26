-- Prove2me | solution 1 for MellinDuality.quadraticChar_of_char_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:38.899546+00:00
-- url     : https://prove2.me/submissions/e6c930e4-4447-4f97-92b9-0d644458e66b

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
public import Theorems.Thm_MellinDuality_isSquare_iff_char

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace MellinDuality
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) (h : χ x = 1 ∨ χ x = -1) :
    quadraticChar (ZMod p) x = 1 :=
  (quadraticChar_one_iff_isSquare hx).2 ((isSquare_iff_char hχ hx).2 h)
end MellinDuality
