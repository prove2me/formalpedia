-- Prove2me | solution 1 for GlobalTheory.Nef.RatDilation.coe_comp_C_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:05:12.2699+00:00
-- url     : https://prove2.me/submissions/1fb6c869-7c3d-4105-b714-c38e27295d5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeEqZeroOfSqDvd
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
open Polynomial
open GlobalTheory.Nef.RatDilation
namespace GlobalTheory.Nef.RatDilation
theorem _root_.solution {F : Type} [Field F] (a : F) (f : F[X]) :
    ((f.comp (C a * X) : F[X]) : PowerSeries F) = PowerSeries.rescale a (f : PowerSeries F) := by
  ext n
  rw [PowerSeries.coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe]
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial m c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
    split_ifs with h <;> simp [h, mul_comm]
end GlobalTheory.Nef.RatDilation
