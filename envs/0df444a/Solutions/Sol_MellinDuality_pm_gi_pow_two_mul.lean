-- Prove2me | solution 1 for MellinDuality.pm_gi_pow_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:27.490098+00:00
-- url     : https://prove2.me/submissions/81c542b5-14e2-4923-bb98-19b8c497efb5

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_sq
attribute [local simp] MellinDuality.gi_re
attribute [local simp] MellinDuality.gi_im

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
namespace MellinDuality
theorem _root_.solution {u : GaussianInt} (hu : u = gi ∨ u = -gi) (j : ℕ) :
    u ^ (2 * j) = (-1) ^ j := by
  have hu2 : u ^ 2 = -1 := by rcases hu with rfl | rfl <;> simp [gi_sq]
  rw [pow_mul, hu2]
end MellinDuality
