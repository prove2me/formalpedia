-- Prove2me | solution 1 for MellinDuality.neg_one_eq_generator_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:30.891812+00:00
-- url     : https://prove2.me/submissions/b44f4349-4a1e-4c2d-a146-938b4a25c905

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
variable {p : ℕ} [hp : Fact p.Prime]
variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ
omit hχ
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hgo : orderOf g = p - 1) :
    ((g ^ ((p - 1) / 2) : (ZMod p)ˣ) : ZMod p) = -1 := by
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le; omega
  set x : (ZMod p)ˣ := g ^ ((p - 1) / 2) with hx
  have hx2 : (x : ZMod p) * x = 1 := by
    rw [← Units.val_mul, ← pow_add, show (p - 1) / 2 + (p - 1) / 2 = p - 1 by
      have := hp.out.eq_one_or_self_of_dvd 2
      rcases Nat.Prime.eq_two_or_odd hp.out with h | h
      · exact absurd h hp2
      · omega, ← hgo, pow_orderOf_eq_one, Units.val_one]
  rcases mul_self_eq_one_iff.1 hx2 with h | h
  · exfalso
    have h1 : x = 1 := Units.ext h
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hgo] at this
    have := Nat.le_of_dvd (by omega) this
    omega
  · exact h
end MellinDuality
