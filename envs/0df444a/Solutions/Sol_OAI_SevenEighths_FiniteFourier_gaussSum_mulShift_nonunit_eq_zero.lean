-- Prove2me | solution 1 for OAI.SevenEighths.FiniteFourier.gaussSum_mulShift_nonunit_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:43:59.788057+00:00
-- url     : https://prove2.me/submissions/5a0e7d43-d356-45df-9cb9-fbe7775112a0

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Theorems.Thm_OAI_SevenEighths_FiniteFourier_exists_unit_stabilizer

set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
namespace OAI.SevenEighths.FiniteFourier
theorem _root_.solution (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ)
    {a : R} (ha : ¬ IsUnit a) :
    gaussSum χ (ψ.mulShift a) = 0 := by
  obtain ⟨u, hu, hχu⟩ := exists_unit_stabilizer χ hχ ha
  have hshift : (ψ.mulShift a).mulShift (u : R) = ψ.mulShift a := by
    ext x
    simp only [AddChar.mulShift_apply, ← mul_assoc, hu]
  have heq := gaussSum_mulShift χ (ψ.mulShift a) u
  rw [hshift] at heq
  exact eq_zero_of_mul_eq_self_left hχu heq
end OAI.SevenEighths.FiniteFourier
