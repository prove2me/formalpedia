-- Prove2me | solution 1 for MellinDuality.unit_apply_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:30.352499+00:00
-- url     : https://prove2.me/submissions/ed77de42-fdb2-458b-a23c-8cff1b1281c9

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) (hχ : orderOf χ = 4)
    (u : (ZMod p)ˣ) : χ u ^ 4 = 1 := by
  rw [← MulChar.pow_apply' χ (by norm_num), ← hχ, pow_orderOf_eq_one, MulChar.one_apply_coe]
end MellinDuality
