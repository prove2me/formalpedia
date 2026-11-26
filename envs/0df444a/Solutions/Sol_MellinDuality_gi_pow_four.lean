-- Prove2me | solution 1 for MellinDuality.gi_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:12.95956+00:00
-- url     : https://prove2.me/submissions/d5def264-cac7-46b2-b060-0dcd21c34ce7

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
public import Theorems.Thm_MellinDuality_gi_sq

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
namespace MellinDuality
theorem _root_.solution : gi ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, gi_sq]; norm_num
end MellinDuality
