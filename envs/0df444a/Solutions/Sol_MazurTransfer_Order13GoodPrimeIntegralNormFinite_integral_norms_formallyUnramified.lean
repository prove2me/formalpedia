-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T05:46:40.89148+00:00
-- url     : https://prove2.me/submissions/c8e3e976-5fd3-4d64-9d8b-c2d34d6ef984

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
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeLocalScalarInputs
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeIntegralScalarNineteen
open Order13LocalIntegralCoefficientMaps
theorem solution (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) :
    FormallyUnramified (integralPi q hq).val ∧
      FormallyUnramified (integralPiConjugate q hq).val := by
  have hs := RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
    (localLaw q hq) (local_law_isCommutative q hq) 19 (local_unit_nineteen q hne)
  letI : FormallyUnramified ((integralPi q hq).val ≫ (integralPiConjugate q hq).val) := by
    rw [integralPi_comp_integralPiConjugate_eq_local_schemeNsmul q hq]
    exact hs
  letI : FormallyUnramified ((integralPiConjugate q hq).val ≫ (integralPi q hq).val) := by
    rw [integralPiConjugate_comp_integralPi_eq_local_schemeNsmul q hq]
    exact hs
  exact ⟨FormallyUnramified.of_comp (integralPi q hq).val (integralPiConjugate q hq).val,
    FormallyUnramified.of_comp (integralPiConjugate q hq).val (integralPi q hq).val⟩

#print axioms solution
