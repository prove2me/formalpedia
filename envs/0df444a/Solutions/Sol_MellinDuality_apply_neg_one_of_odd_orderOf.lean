-- Prove2me | solution 1 for MellinDuality.apply_neg_one_of_odd_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:33.113414+00:00
-- url     : https://prove2.me/submissions/7cbde0d1-cdff-4e48-bc82-c3b8268a4e30

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
theorem _root_.solution {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R)
    (h : Odd (orderOf χ)) : χ (-1) = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : χ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h2 : χ (-1) ^ orderOf χ = 1 := by
    rw [← MulChar.pow_apply' χ (by omega), pow_orderOf_eq_one]
    exact MulChar.one_apply isUnit_one.neg
  rw [hk, pow_succ, pow_mul, h1, one_pow, one_mul] at h2
  exact h2
end MellinDuality
