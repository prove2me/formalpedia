-- Prove2me | solution 1 for MellinDuality.quartic_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:08.80921+00:00
-- url     : https://prove2.me/submissions/98edf8c4-9c86-403e-8721-9dd884d07104

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_eq_of_pow_four_eq_one
public import Theorems.Thm_MellinDuality_unit_apply_pow_four
attribute [local simp] MellinDuality.gi_re
attribute [local simp] MellinDuality.gi_im

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
variable {p : ℕ} [hp : Fact p.Prime]
variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ
namespace MellinDuality
theorem _root_.solution {a : ZMod p} (ha : a ≠ 0) :
    χ a = 1 ∨ χ a = gi ∨ χ a = -1 ∨ χ a = -gi :=
  eq_of_pow_four_eq_one (by simpa using unit_apply_pow_four χ hχ (Units.mk0 a ha))
end MellinDuality
