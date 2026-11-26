-- Prove2me | solution 1 for MellinDuality.neg_one_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:27.124223+00:00
-- url     : https://prove2.me/submissions/715ebfe3-3f71-47aa-b728-18574dbce97f

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
theorem _root_.solution : (-1 : GaussianInt) ≠ 1 := by
  intro h; have := congrArg Zsqrtd.re h; simp at this
end MellinDuality
