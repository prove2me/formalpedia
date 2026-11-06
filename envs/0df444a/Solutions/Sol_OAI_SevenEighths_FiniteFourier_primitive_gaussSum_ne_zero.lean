-- Prove2me | solution 1 for OAI.SevenEighths.FiniteFourier.primitive_gaussSum_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:46:58.482922+00:00
-- url     : https://prove2.me/submissions/be986b9e-6d7a-4f0c-b79c-fbf5093f5543

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Theorems.Thm_OAI_SevenEighths_FiniteFourier_primitive_gaussSum_mul_conjugate

set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]
namespace OAI.SevenEighths.FiniteFourier
theorem _root_.solution (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ≠ 0 := by
  intro hzero
  have h := primitive_gaussSum_mul_conjugate χ hχ ψ hψ
  rw [hzero, zero_mul] at h
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) h.symm
end OAI.SevenEighths.FiniteFourier
