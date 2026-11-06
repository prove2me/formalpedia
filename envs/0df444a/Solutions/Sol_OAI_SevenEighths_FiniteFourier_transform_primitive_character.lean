-- Prove2me | solution 1 for OAI.SevenEighths.FiniteFourier.transform_primitive_character
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:45:28.967217+00:00
-- url     : https://prove2.me/submissions/3f6f1b11-17c9-42e0-a635-6b2b2cc3fe5e

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Theorems.Thm_OAI_SevenEighths_FiniteFourier_primitive_gaussSum_mulShift

set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
namespace OAI.SevenEighths.FiniteFourier
theorem _root_.solution (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (a : R) :
    transform ψ χ a = χ⁻¹ a * gaussSum χ ψ := by
  exact primitive_gaussSum_mulShift χ hχ ψ a
end OAI.SevenEighths.FiniteFourier
