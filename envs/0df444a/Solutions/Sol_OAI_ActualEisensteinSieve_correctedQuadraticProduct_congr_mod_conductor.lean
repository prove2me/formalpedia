-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.correctedQuadraticProduct_congr_mod_conductor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:59.206767+00:00
-- url     : https://prove2.me/submissions/22bd7abc-8f92-4d09-a394-f7573a7c955f

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
    (h : Ideal.Quotient.mk (lambdaIdeal * Finset.univ.prod P) x =
      Ideal.Quotient.mk (lambdaIdeal * Finset.univ.prod P) y) :
    correctedQuadraticProduct P x = correctedQuadraticProduct P y := by
  classical
  have hmem : x - y ∈ lambdaIdeal * Finset.univ.prod P :=
    Ideal.Quotient.eq.mp h
  have hlambda : Ideal.Quotient.mk lambdaIdeal x =
      Ideal.Quotient.mk lambdaIdeal y :=
    Ideal.Quotient.eq.mpr (Ideal.mul_le_left hmem)
  have hprod : quadraticProduct P x = quadraticProduct P y := by
    unfold quadraticProduct
    apply Finset.prod_congr rfl
    intro j _
    apply localQuadratic_congr
    apply Ideal.Quotient.eq.mpr
    exact (Ideal.mul_le_right.trans
      (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j)))) hmem
  unfold correctedQuadraticProduct
  split_ifs <;> simp [hprod, localQuadratic_congr lambdaIdeal x y hlambda]
end OAI.ActualEisensteinSieve
