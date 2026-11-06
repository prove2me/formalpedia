-- Prove2me | solution 2 for OAI.ActualEisensteinSieve.lambdaQuadratic_sq_one_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:39.697295+00:00
-- url     : https://prove2.me/submissions/7d00de71-d4e5-4e15-a6f8-9637cc89a44a

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
theorem solution (x : O)
    (hx : x ∉ lambdaIdeal) :
    localQuadratic lambdaIdeal x ^ 2 = 1 := by
  classical
  letI : Field (O ⧸ lambdaIdeal) := Ideal.Quotient.field lambdaIdeal
  letI : Fintype (O ⧸ lambdaIdeal) := Fintype.ofFinite (O ⧸ lambdaIdeal)
  have hne : Ideal.Quotient.mk lambdaIdeal x ≠ 0 := fun h =>
    hx (Ideal.Quotient.eq_zero_iff_mem.mp h)
  change quadraticChar (O ⧸ lambdaIdeal) (Ideal.Quotient.mk lambdaIdeal x) ^ 2 = 1
  exact quadraticChar_sq_one hne
