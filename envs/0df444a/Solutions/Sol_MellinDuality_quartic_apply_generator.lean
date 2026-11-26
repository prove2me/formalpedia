-- Prove2me | solution 1 for MellinDuality.quartic_apply_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:09.846825+00:00
-- url     : https://prove2.me/submissions/cc6d15d2-5010-4430-9cab-99a628a618f2

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
theorem _root_.solution {g : (ZMod p)ˣ} (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) :
    χ g = gi ∨ χ g = -gi := by
  rcases eq_of_pow_four_eq_one (unit_apply_pow_four χ hχ g) with h | h | h | h
  · exfalso
    have : χ ^ 2 = 1 := by
      refine MulChar.ext fun u => ?_; obtain ⟨k, rfl⟩ := hg u
      rw [MulChar.pow_apply' χ (by norm_num), Units.val_pow_eq_pow_val, map_pow, h]; simp
    have := orderOf_dvd_of_pow_eq_one this; rw [hχ] at this; norm_num at this
  · exact Or.inl h
  · exfalso
    have : χ ^ 2 = 1 := by
      refine MulChar.ext fun u => ?_; obtain ⟨k, rfl⟩ := hg u
      rw [MulChar.pow_apply' χ (by norm_num), Units.val_pow_eq_pow_val, map_pow, h,
        ← pow_mul, mul_comm, pow_mul]; simp
    have := orderOf_dvd_of_pow_eq_one this; rw [hχ] at this; norm_num at this
  · exact Or.inr h
end MellinDuality
