-- Prove2me | solution 1 for MellinDuality.quartic_apply_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:30.641807+00:00
-- url     : https://prove2.me/submissions/78ec6830-950a-4c66-842e-138e40cd69e2

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_pm_gi_pow_two_mul
public import Theorems.Thm_MellinDuality_exists_generator
public import Theorems.Thm_MellinDuality_quartic_apply_generator
public import Theorems.Thm_MellinDuality_neg_one_eq_generator_pow
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
theorem _root_.solution (hp8 : p % 8 = 5) : χ (-1) = -1 := by
  obtain ⟨g, hgo, hg⟩ := exists_generator (p := p)
  have hp2 : p ≠ 2 := by omega
  rw [← neg_one_eq_generator_pow hp2 hgo, Units.val_pow_eq_pow_val, map_pow,
    show (p - 1) / 2 = 2 * (2 * (p / 8) + 1) by omega,
    pm_gi_pow_two_mul (quartic_apply_generator χ hχ hg)]
  simp [pow_succ, pow_mul]
end MellinDuality
