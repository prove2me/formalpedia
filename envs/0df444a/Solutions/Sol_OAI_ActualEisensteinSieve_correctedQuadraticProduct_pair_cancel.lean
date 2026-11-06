-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.correctedQuadraticProduct_pair_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:41.470485+00:00
-- url     : https://prove2.me/submissions/4008abd8-70b8-445f-89cc-7a945ff69674

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Theorems.Thm_OAI_ActualEisensteinSieve_lambdaQuadratic_sq_one_of_not_mem

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
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → Ideal O) (Q : κ → Ideal O)
    [∀ i, (P i).IsMaximal] [∀ j, (Q j).IsMaximal]
    (hsame : quadraticProduct P (-1) = quadraticProduct Q (-1))
    (x : O) (hx : x ∉ lambdaIdeal) :
    correctedQuadraticProduct P x * correctedQuadraticProduct Q x =
      quadraticProduct P x * quadraticProduct Q x := by
  by_cases hP : quadraticProduct P (-1) = 1
  · have hQ : quadraticProduct Q (-1) = 1 := hsame.symm.trans hP
    simp [correctedQuadraticProduct, hP, hQ]
  · have hQ : quadraticProduct Q (-1) ≠ 1 := by
      intro h
      exact hP (hsame.trans h)
    simp only [correctedQuadraticProduct, hP, hQ, ite_false]
    have hlamSq := lambdaQuadratic_sq_one_of_not_mem x hx
    calc
      quadraticProduct P x * localQuadratic lambdaIdeal x *
          (quadraticProduct Q x * localQuadratic lambdaIdeal x) =
        (quadraticProduct P x * quadraticProduct Q x) *
          localQuadratic lambdaIdeal x ^ 2 := by ring
      _ = quadraticProduct P x * quadraticProduct Q x := by
        rw [hlamSq, mul_one]
end OAI.ActualEisensteinSieve
