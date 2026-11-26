-- Prove2me | solution 1 for MellinDuality.quartic_apply_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:59.031743+00:00
-- url     : https://prove2.me/submissions/ce0ab5e4-3184-485d-973e-a91f2dc72014

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
public import Theorems.Thm_MellinDuality_pm_gi_pow_odd
public import Theorems.Thm_MellinDuality_exists_generator
public import Theorems.Thm_MellinDuality_quartic_apply_generator
public import Theorems.Thm_MellinDuality_two_eq_generator_pow_odd

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
variable {p : ℕ} [hp : Fact p.Prime]
variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ
namespace MellinDuality
theorem _root_.solution (hp8 : p % 8 = 5) : χ 2 = gi ∨ χ 2 = -gi := by
  obtain ⟨g, -, hg⟩ := exists_generator (p := p)
  obtain ⟨e, he, h2⟩ := two_eq_generator_pow_odd hp8 hg
  rw [← h2, Units.val_pow_eq_pow_val, map_pow]
  exact pm_gi_pow_odd (quartic_apply_generator χ hχ hg) he
end MellinDuality
