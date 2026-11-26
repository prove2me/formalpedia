-- Prove2me | solution 1 for MellinDuality.quadraticChar_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:18.125388+00:00
-- url     : https://prove2.me/submissions/001916b7-69f8-4ba4-82e0-f32c16958c40

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_sq
public import Theorems.Thm_MellinDuality_quartic_values
public import Theorems.Thm_MellinDuality_quadraticChar_of_char_one
public import Theorems.Thm_MellinDuality_quadraticChar_of_char_gi
attribute [local simp] MellinDuality.gi_re
attribute [local simp] MellinDuality.gi_im

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace MellinDuality
theorem _root_.solution {n : ZMod p} (hn : n ≠ 0) :
    ((quadraticChar (ZMod p) n : ℤ) : GaussianInt) = χ n ^ 2 := by
  rcases quartic_values χ hχ hn with h | h | h | h
  · rw [quadraticChar_of_char_one hχ hn (Or.inl h), h]; simp
  · rw [quadraticChar_of_char_gi hχ hn (Or.inl h), h, gi_sq]; simp
  · rw [quadraticChar_of_char_one hχ hn (Or.inr h), h]; simp
  · rw [quadraticChar_of_char_gi hχ hn (Or.inr h), h, neg_sq, gi_sq]; simp
end MellinDuality
