-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.finiteQuadratic_congr_mod_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:41:38.731298+00:00
-- url     : https://prove2.me/submissions/711977a1-8a58-4e22-92de-b27b989de9fb

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals

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
    [∀ i, (P i).IsMaximal] (x y : O)
    (h : Ideal.Quotient.mk (Finset.univ.prod P) x =
      Ideal.Quotient.mk (Finset.univ.prod P) y) :
    (∏ j : ι, localQuadratic (P j) x) =
      ∏ j : ι, localQuadratic (P j) y := by
  classical
  have hmem : x - y ∈ Finset.univ.prod P := Ideal.Quotient.eq.mp h
  apply Finset.prod_congr rfl
  intro j _
  apply localQuadratic_congr
  apply Ideal.Quotient.eq.mpr
  exact (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j))) hmem
end OAI.ActualEisensteinSieve
