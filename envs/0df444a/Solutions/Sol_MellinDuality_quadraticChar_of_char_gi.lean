-- Prove2me | solution 1 for MellinDuality.quadraticChar_of_char_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:39.951818+00:00
-- url     : https://prove2.me/submissions/873cbc49-86b8-4c8a-b895-a7ae5fcd33aa

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
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) (h : χ x = gi ∨ χ x = -gi) :
    quadraticChar (ZMod p) x = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare, isSquare_iff_char hχ hx]
  rintro (h' | h') <;> rcases h with h | h <;> rw [h] at h' <;> revert h' <;> decide
end MellinDuality
