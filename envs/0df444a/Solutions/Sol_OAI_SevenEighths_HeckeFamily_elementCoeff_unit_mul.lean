-- Prove2me | solution 1 for OAI.SevenEighths.HeckeFamily.elementCoeff_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:17.418554+00:00
-- url     : https://prove2.me/submissions/904e20c1-6994-4eb4-b520-190fa2e2b7d2

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_elementCoeff_mul

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace OAI.SevenEighths.HeckeFamily
theorem _root_.solution (χ : Character) (u : Oˣ) (z : O) :
    elementCoeff χ ((u : O) * z) = elementCoeff χ z := by
  rw [elementCoeff_mul]
  have hu : elementCoeff χ (u : O) = 1 := χ.unit_trivial u
  rw [hu, one_mul]
end OAI.SevenEighths.HeckeFamily
