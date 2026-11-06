-- Prove2me | solution 2 for OAI.SevenEighths.HeckeFamily.elementCoeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:41.184325+00:00
-- url     : https://prove2.me/submissions/92fa95c8-b262-45d9-b252-4b3210445402

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
    elementCoeff χ (z * w) = elementCoeff χ z * elementCoeff χ w := by
  simp [elementCoeff, map_mul]
