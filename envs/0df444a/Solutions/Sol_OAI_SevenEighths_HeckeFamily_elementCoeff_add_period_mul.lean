-- Prove2me | solution 1 for OAI.SevenEighths.HeckeFamily.elementCoeff_add_period_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:46.225955+00:00
-- url     : https://prove2.me/submissions/61ce4e20-aa3f-416b-911f-7bfcd8b96173

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_elementCoeff_one
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_quotient_period
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


attribute [local simp] OAI.SevenEighths.HeckeFamily.elementCoeff_one

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace OAI.SevenEighths.HeckeFamily
theorem _root_.solution (χ : Character) (z w : O) :
    elementCoeff χ (z + (χ.period : O) * w) = elementCoeff χ z := by
  simp [elementCoeff, map_add, map_mul, quotient_period χ]
end OAI.SevenEighths.HeckeFamily
