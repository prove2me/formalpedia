-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeIntegralNormEtale.integral_norms_etale
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T05:58:33.641996+00:00
-- url     : https://prove2.me/submissions/5476be22-dcf9-4d24-b088-7be80cd15cd5

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finite etale fibres of the SAME selected integral norm
extensions at every prime away from 104 and nineteen. The group law and
multiplication by nineteen are those of the selected local Picard model.
Named downstream consumer: good-prime unramified Kummer conditions.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralScalarNineteenFacts
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalPicardLawCommutativity
import Theorems.Thm_MazurTransfer_Order13GoodPrimeLocalScalarInputs_local_unit_nineteen
import Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralNormFinite_integral_norms_finite
import Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralNormFinite_integral_norms_formallyUnramified
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeLocalScalarInputs
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeIntegralScalarNineteen
open Order13LocalIntegralCoefficientMaps
namespace MazurTransfer.GoodPrimeIntegralNormEtaleScalarProofHelpers20261018
theorem local_scalar_nineteen_finite_and_flat (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) :
    IsFinite ((localLaw q hq).schemeNsmul 19) ∧ Flat ((localLaw q hq).schemeNsmul 19) :=
  RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit
    (localLaw q hq) (localPicard_abelian q hq) (local_law_isCommutative q hq)
    19 (local_unit_nineteen q hne)

theorem local_scalar_nineteen_etale (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) : Etale ((localLaw q hq).schemeNsmul 19) := by
  letI : Smooth (localPicard q hq).toBase := (localPicard_geometry q hq).1
  letI : IsLocallyNoetherian (localPicard q hq).P :=
    LocallyOfFiniteType.isLocallyNoetherian (localPicard q hq).toBase
  letI : IsFinite ((localLaw q hq).schemeNsmul 19) :=
    (local_scalar_nineteen_finite_and_flat q hq hne).1
  letI : Flat ((localLaw q hq).schemeNsmul 19) :=
    (local_scalar_nineteen_finite_and_flat q hq hne).2
  letI : FormallyUnramified ((localLaw q hq).schemeNsmul 19) :=
    RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
      (localLaw q hq) (local_law_isCommutative q hq) 19 (local_unit_nineteen q hne)
  exact Etale.of_formallyUnramified_of_flat ((localLaw q hq).schemeNsmul 19)

end MazurTransfer.GoodPrimeIntegralNormEtaleScalarProofHelpers20261018
open MazurTransfer.GoodPrimeIntegralNormEtaleScalarProofHelpers20261018

theorem solution (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) :
    Etale (integralPi q hq).val ∧ Etale (integralPiConjugate q hq).val := by
  letI : IsFinite (integralPi q hq).val := (MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_finite q hq hne).1
  letI : IsFinite (integralPiConjugate q hq).val := (MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_finite q hq hne).2
  letI : FormallyUnramified (integralPi q hq).val :=
    (MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_formallyUnramified q hq hne).1
  letI : FormallyUnramified (integralPiConjugate q hq).val :=
    (MazurTransfer.Order13GoodPrimeIntegralNormFinite.integral_norms_formallyUnramified q hq hne).2
  letI : Etale ((integralPi q hq).val ≫ (integralPiConjugate q hq).val) := by
    rw [integralPi_comp_integralPiConjugate_eq_local_schemeNsmul q hq]
    exact local_scalar_nineteen_etale q hq hne
  letI : Etale ((integralPiConjugate q hq).val ≫ (integralPi q hq).val) := by
    rw [integralPiConjugate_comp_integralPi_eq_local_schemeNsmul q hq]
    exact local_scalar_nineteen_etale q hq hne
  exact ⟨Etale.of_comp (integralPi q hq).val (integralPiConjugate q hq).val,
    Etale.of_comp (integralPiConjugate q hq).val (integralPi q hq).val⟩

#print axioms solution
