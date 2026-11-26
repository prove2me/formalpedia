-- Prove2me | solution 1 for MellinDuality.gi_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:25.233801+00:00
-- url     : https://prove2.me/submissions/46e31a00-ace8-43bb-81d2-1972bd3f7f8b

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_gi_im
attribute [local simp] MellinDuality.gi_re
attribute [local simp] MellinDuality.gi_im

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
namespace MellinDuality
theorem _root_.solution : gi ^ 2 = -1 := by
  rw [Zsqrtd.ext_iff]; simp [sq, gi]
end MellinDuality
