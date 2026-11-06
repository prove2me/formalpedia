-- Prove2me | solution 1 for OAI.SevenEighths.FiniteFourier.exists_unit_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:43:19.325527+00:00
-- url     : https://prove2.me/submissions/b6579f5c-e572-46fe-a6f4-d6ff6ca54439

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Theorems.Thm_OAI_SevenEighths_FiniteFourier_exists_nonzero_annihilator

set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
namespace OAI.SevenEighths.FiniteFourier
theorem _root_.solution (χ : MulChar R ℂ) (hχ : IsPrimitiveOnIdeals χ)
    {a : R} (ha : ¬ IsUnit a) :
    ∃ u : Rˣ, a * (u : R) = a ∧ χ (u : R) ≠ 1 := by
  obtain ⟨b, hb, hab⟩ := exists_nonzero_annihilator ha
  have hI : Ideal.span ({b} : Set R) ≠ ⊥ := by
    intro hI
    have hbI := Ideal.mem_span_singleton_self b
    rw [hI] at hbI
    exact hb hbI
  obtain ⟨u, hu, hχu⟩ := hχ _ hI
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hu
  refine ⟨u, ?_, hχu⟩
  have hzero : a * ((u : R) - 1) = 0 := by
    rw [hc, ← mul_assoc, hab, zero_mul]
  linear_combination hzero
end OAI.SevenEighths.FiniteFourier
