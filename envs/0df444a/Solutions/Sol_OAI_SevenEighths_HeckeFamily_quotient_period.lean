-- Prove2me | solution 1 for OAI.SevenEighths.HeckeFamily.quotient_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:53:30.250923+00:00
-- url     : https://prove2.me/submissions/db85e408-eb5c-41f7-b2fd-fade99a71334

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
namespace OAI.SevenEighths.HeckeFamily
theorem _root_.solution (χ : Character) :
    Ideal.Quotient.mk χ.modulus (χ.period : O) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr χ.period_mem
end OAI.SevenEighths.HeckeFamily
