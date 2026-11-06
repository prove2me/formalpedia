-- Prove2me | solution 2 for OAI.SevenEighths.HeckeFamily.elementCoeff_add_period_mul
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:33.31934+00:00
-- url     : https://prove2.me/submissions/01ecc9b9-7db2-40ff-9633-f1c99e39d339

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

theorem solution (χ : Character) (z w : O) :
    elementCoeff χ (z + (χ.period : O) * w) = elementCoeff χ z := by
  unfold elementCoeff
  congr 1
  rw [map_add]
  have : Ideal.Quotient.mk χ.modulus ((χ.period : O) * w) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ χ.period_mem)
  rw [this, add_zero]
