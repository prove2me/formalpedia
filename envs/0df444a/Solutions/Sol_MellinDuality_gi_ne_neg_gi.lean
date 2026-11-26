-- Prove2me | solution 1 for MellinDuality.gi_ne_neg_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:23.701323+00:00
-- url     : https://prove2.me/submissions/dfeedc9e-66c4-47b4-a69b-ad6e90d20a41

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
theorem _root_.solution : gi ≠ -gi := by
  intro h; have := congrArg Zsqrtd.im h; simp at this
end MellinDuality
