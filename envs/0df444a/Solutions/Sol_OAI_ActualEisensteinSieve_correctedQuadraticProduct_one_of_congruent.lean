-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.correctedQuadraticProduct_one_of_congruent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:25.076227+00:00
-- url     : https://prove2.me/submissions/319f2b23-c77c-4aef-a7b9-d5fa9665f5c9

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Theorems.Thm_OAI_ActualEisensteinSieve_correctedQuadraticProduct_congr_mod_conductor

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
    [∀ i, (P i).IsMaximal] (x : O)
    (h : x - 1 ∈ lambdaIdeal * Finset.univ.prod P) :
    correctedQuadraticProduct P x = 1 := by
  have hres : Ideal.Quotient.mk (lambdaIdeal * Finset.univ.prod P) x =
      Ideal.Quotient.mk (lambdaIdeal * Finset.univ.prod P) (1 : O) :=
    Ideal.Quotient.eq.mpr h
  exact (correctedQuadraticProduct_congr_mod_conductor P x 1 hres).trans
    (correctedQuadraticProduct_one P)
end OAI.ActualEisensteinSieve
