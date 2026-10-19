-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_finite
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T05:37:09.129588+00:00
-- url     : https://prove2.me/submissions/68863049-e23b-43f8-bc4c-7bd20d4b232d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finiteness and formal unramifiedness of the SAME selected
integral norm extensions at every prime away from 104 and nineteen.
Named downstream consumer: finite etale norm fibres and good-prime
unramified Kummer conditions for the order-13 norm maps.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralScalarNineteenFacts
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalPicardLawCommutativity
import Theorems.Thm_MazurTransfer_Order13GoodPrimeLocalScalarInputs_local_unit_nineteen
import Theorems.Thm_MazurTransfer_relative_group_norm_factors_finite_of_invertible_scalar
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeLocalScalarInputs
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeIntegralScalarNineteen
open Order13LocalIntegralCoefficientMaps
theorem solution (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) :
    IsFinite (integralPi q hq).val ∧ IsFinite (integralPiConjugate q hq).val := by
  letI : IsProper (localPicard q hq).toBase := (localPicard_geometry q hq).2.1
  exact MazurTransfer.relative_group_norm_factors_finite_of_invertible_scalar
    (localPicard q hq).toBase (localLaw q hq) (local_law_isCommutative q hq)
    19 (local_unit_nineteen q hne) (integralPi q hq).val (integralPiConjugate q hq).val
    (integralPi q hq).property (integralPiConjugate q hq).property
    (integralPi_comp_integralPiConjugate_eq_local_schemeNsmul q hq)
    (integralPiConjugate_comp_integralPi_eq_local_schemeNsmul q hq)

#print axioms solution
