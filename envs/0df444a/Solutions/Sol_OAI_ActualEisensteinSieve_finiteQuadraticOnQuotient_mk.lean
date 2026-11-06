-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.finiteQuadraticOnQuotient_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:51:11.024577+00:00
-- url     : https://prove2.me/submissions/510f5672-9dba-4863-a8fd-8a6d29aee53a

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Theorems.Thm_OAI_ActualEisensteinSieve_finiteQuadratic_congr_mod_product

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ActualEisensteinSieve
namespace OAI.ActualEisensteinSieve
theorem _root_.solution
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) :
    finiteQuadraticOnQuotient P
        (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      ∏ j : ι, localQuadratic (P j) x := by
  classical
  unfold finiteQuadraticOnQuotient
  apply finiteQuadratic_congr_mod_product P
  exact Quotient.out_eq _
end OAI.ActualEisensteinSieve
