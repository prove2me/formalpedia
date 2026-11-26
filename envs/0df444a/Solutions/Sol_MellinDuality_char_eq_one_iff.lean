-- Prove2me | solution 1 for MellinDuality.char_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:28.8329+00:00
-- url     : https://prove2.me/submissions/a0a585e7-36e5-4aa1-9b3e-6f4b531dc3e1

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_exists_generator
public import Theorems.Thm_MellinDuality_quartic_values
public import Theorems.Thm_MellinDuality_quartic_apply_generator
public import Theorems.Thm_MellinDuality_gi_pow_eq_one_iff
attribute [local simp] MellinDuality.gi_re
attribute [local simp] MellinDuality.gi_im

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace MellinDuality
theorem _root_.solution {n : ZMod p} (hn : n ≠ 0) : χ n = 1 ↔ ∃ y : ZMod p, y ^ 4 = n := by
  constructor
  · intro h
    obtain ⟨g, -, hg⟩ := exists_generator (p := p)
    obtain ⟨j, hj⟩ := hg (Units.mk0 n hn)
    have hnj : n = (g : ZMod p) ^ j := by
      have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hj
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
      exact this.symm
    rw [hnj, map_pow, gi_pow_eq_one_iff (quartic_apply_generator χ hχ hg)] at h
    obtain ⟨q, rfl⟩ := h
    exact ⟨(g : ZMod p) ^ q, by rw [hnj, ← pow_mul, mul_comm]⟩
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by rintro rfl; exact hn (by simp)
    rw [map_pow]
    rcases quartic_values χ hχ hy with h | h | h | h <;> rw [h] <;> decide
end MellinDuality
