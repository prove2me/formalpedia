-- Prove2me | solution 1 for OAI.SevenEighths.FiniteFourier.primitive_character_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:18.398041+00:00
-- url     : https://prove2.me/submissions/db210369-9bcd-41f5-ac32-e20eb48656ba

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Theorems.Thm_OAI_SevenEighths_FiniteFourier_IsPrimitiveOnIdeals_inv
import Theorems.Thm_OAI_SevenEighths_FiniteFourier_transform_primitive_character
import Theorems.Thm_OAI_SevenEighths_FiniteFourier_primitive_gaussSum_ne_zero

set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
namespace OAI.SevenEighths.FiniteFourier
theorem _root_.solution (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a : R) :
    χ a = (∑ x : R, χ⁻¹ x * ψ (a * x)) / gaussSum χ⁻¹ ψ := by
  apply (eq_div_iff (primitive_gaussSum_ne_zero χ⁻¹ hχ.inv ψ hψ)).mpr
  simpa only [inv_inv, transform] using
    (transform_primitive_character χ⁻¹ hχ.inv ψ a).symm
end OAI.SevenEighths.FiniteFourier
