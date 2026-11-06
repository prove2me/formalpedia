-- Prove2me | solution 2 for OAI.SevenEighths.FiniteFourier.exists_nonzero_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:25.066206+00:00
-- url     : https://prove2.me/submissions/994b44ad-9ebf-489d-ae23-9f0c42bd4bfc

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
theorem solution {a : R} (ha : ¬ IsUnit a) :
    ∃ b : R, b ≠ 0 ∧ a * b = 0 := by
  by_contra h
  push_neg at h
  have hinj : Function.Injective (fun x : R => a * x) := by
    intro x y hxy
    by_contra hne
    exact h (x - y) (sub_ne_zero.mpr hne) (by simp only at hxy; rw [mul_sub, hxy, sub_self])
  obtain ⟨b, hb⟩ := Finite.injective_iff_surjective.mp hinj 1
  exact ha (isUnit_iff_exists_inv.mpr ⟨b, hb⟩)
