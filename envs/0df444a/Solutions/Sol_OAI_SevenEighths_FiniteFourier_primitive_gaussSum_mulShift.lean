-- Prove2me | solution 1 for OAI.SevenEighths.FiniteFourier.primitive_gaussSum_mulShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:39.717192+00:00
-- url     : https://prove2.me/submissions/00e48fb2-bc37-4f02-89e0-1aca816487a6

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Theorems.Thm_OAI_SevenEighths_FiniteFourier_gaussSum_mulShift_nonunit_eq_zero

set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
namespace OAI.SevenEighths.FiniteFourier
theorem _root_.solution (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (a : R) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : IsUnit a
  · simpa only [ha.unit_spec] using gaussSum_mulShift_eq χ ψ ha.unit
  · rw [gaussSum_mulShift_nonunit_eq_zero χ hχ ψ ha,
      MulChar.map_nonunit _ ha, zero_mul]
end OAI.SevenEighths.FiniteFourier
