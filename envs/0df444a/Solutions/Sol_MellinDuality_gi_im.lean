-- Prove2me | solution 1 for MellinDuality.gi_im
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:42:52.496345+00:00
-- url     : https://prove2.me/submissions/7533626c-e72e-49a9-8860-0e76f9fabd4c

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
namespace MellinDuality
theorem _root_.solution : gi.im = 1 := rfl
end MellinDuality
