-- Prove2me | solution 1 for MellinDuality.gi_pow_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:40.725605+00:00
-- url     : https://prove2.me/submissions/05376f9b-cb98-49ca-b6cd-cb7491cf0b8d

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
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
omit hp hχ
namespace MellinDuality
theorem _root_.solution {u : GaussianInt} (hu : u = gi ∨ u = -gi) (j : ℕ) :
    u ^ j = 1 ↔ 4 ∣ j := by
  have h4 : u ^ 4 = 1 := by rcases hu with rfl | rfl <;> decide
  have key : u ^ j = u ^ (j % 4) := by
    conv_lhs => rw [← Nat.mod_add_div j 4, pow_add, pow_mul, h4, one_pow, mul_one]
  rw [key, Nat.dvd_iff_mod_eq_zero]
  have hlt := Nat.mod_lt j (show 0 < 4 by norm_num)
  interval_cases (j % 4) <;> rcases hu with rfl | rfl <;> decide
end MellinDuality
