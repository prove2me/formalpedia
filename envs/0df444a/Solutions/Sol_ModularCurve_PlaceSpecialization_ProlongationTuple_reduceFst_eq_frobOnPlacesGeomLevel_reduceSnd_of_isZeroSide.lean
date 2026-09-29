-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/5cf33bcb-66cd-539c-954b-dfdf03c5b5ed

import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_atkinLehnerBar_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open ModularCurve.PlaceSpecialization.ProlongationTuple

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) :
    ∀ c, IsZeroSide P c → P.reduceFst c = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd c) := by
  intro c hc
  have h :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide
      P hqN (ProlongationTuple.atkinLehnerBar N q • c)
      ((ModularCurve.PlaceSpecialization.ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff P hqN c).mpr hc)
  rwa [ModularCurve.PlaceSpecialization.reduceSnd_atkinLehnerBar_smul P hqN c,
    ModularCurve.PlaceSpecialization.reduceFst_atkinLehnerBar_smul P hqN c] at h

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide (solution)
