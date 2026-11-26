-- Prove2me | solution 1 for MellinDuality.pm_gi_pow_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:24.708802+00:00
-- url     : https://prove2.me/submissions/d6a43afb-5336-4e10-9ebe-7e4756395468

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_MellinDuality_Basic
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_sq
attribute [local simp] MellinDuality.gi_re
attribute [local simp] MellinDuality.gi_im

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
namespace MellinDuality
theorem _root_.solution {u : GaussianInt} (hu : u = gi ∨ u = -gi) {e : ℕ} (he : Odd e) :
    u ^ e = gi ∨ u ^ e = -gi := by
  obtain ⟨j, rfl⟩ := he
  have hu2 : u ^ 2 = -1 := by rcases hu with rfl | rfl <;> simp [gi_sq]
  rw [pow_succ, pow_mul, hu2]
  rcases neg_one_pow_eq_or GaussianInt j with h | h <;> rw [h] <;> rcases hu with rfl | rfl <;>
    simp
end MellinDuality
