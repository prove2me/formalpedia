-- Prove2me | solution 1 for ModularCurve.heckeBetaExchangeAt_of_primes_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e7e87b79-a25b-5edc-886e-bfced674f623

import Mathlib
import Definitions.Def_ModularCurve_HeckeNamedInputs
import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
import Theorems.Thm_AlgebraicCurve_finiteAlong_comp
import Theorems.Thm_ModularCurve_towerSubstBar_finiteAlong
import Theorems.Thm_ModularCurve_towerSubstBar_isIntegral
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_ModularCurve_finrankAlong_towerSubstBar_roof
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_modularPolynomialFamily
import Theorems.Thm_ModularCurve_heckeBetaRoof_adjoin_range_union_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeBetaExchangeAt_of_primes_of_ne
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_heckeBetaExchangeAt_of_primes_of_ne.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "dvd_of_eq_roof_beta HeckeBetaExchangeAt heckeBetaBar modularFunctionFieldFull laurentBaseChange towerSubstBar towerSubstBar_congr towerSubstBar_comp_heckeBetaBar HeckeExchangeAt towerSubstBar_finiteAlong towerSubstBar_isIntegral finrankAlong_towerSubstBar_roof finiteAlong_heckeBetaBar_of_prime heckeBetaBarIntegral_of_prime functionFieldGeneration modularPolynomialFamily heckeBetaRoof_adjoin_range_union_eq_top"
p2m_open "ModularCurve"

theorem heckeBetaExchangeAt_of_gen
    (L : Type*) [Field L] [Algebra ℚ L] (N ℓ ℓ' M : ℕ)
    [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M]
    (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') (hM : M = N * ℓ * ℓ')
    (hgen : Algebra.adjoin L
      (Set.range (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2)
        ∪ Set.range (towerSubstBar L (N * ℓ) ℓ' (dvd_of_eq_roof_beta N ℓ ℓ' M hM).1)) = ⊤) :
    HeckeBetaExchangeAt L N ℓ ℓ' M hM := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact ℓ'.Prime := ⟨hℓ'⟩
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : CharZero (laurentBaseChange L (modularFunctionFieldFull N)) :=
    charZero_of_injective_algebraMap (algebraMap L (laurentBaseChange L (modularFunctionFieldFull N))).injective
  have hA : N * (ℓ' * ℓ) ∣ M := ⟨1, by rw [hM]; ring⟩
  have hB : N * (ℓ * ℓ') ∣ M := ⟨1, by rw [hM]; ring⟩
  have hsq : (towerSubstBar L (N * ℓ) ℓ' (dvd_of_eq_roof_beta N ℓ ℓ' M hM).1).comp (heckeBetaBar L N ℓ)
      = (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2).comp (heckeBetaBar L N ℓ') := by
    rw [towerSubstBar_comp_heckeBetaBar L ℓ' ℓ _ hA, towerSubstBar_comp_heckeBetaBar L ℓ ℓ' _ hB]
    exact towerSubstBar_congr L (mul_comm ℓ' ℓ) hA hB
  have hfin : FiniteAlong L ((towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2).comp (heckeBetaBar L N ℓ')) :=
    finiteAlong_comp (heckeBetaBar L N ℓ') (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2)
      (finiteAlong_heckeBetaBar_of_prime L N ℓ') (towerSubstBar_finiteAlong L ℓ (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2)
  have hsep : SeparableAlong L ((towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2).comp (heckeBetaBar L N ℓ')) :=
    separableAlong_of_charZero _
      (RingHom.IsIntegral.trans _ _ (heckeBetaBarIntegral_of_prime L N ℓ')
        (towerSubstBar_isIntegral L ℓ (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2))
  have hLD : finrankAlong L ((towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2).comp (heckeBetaBar L N ℓ'))
      = finrankAlong L (heckeBetaBar L N ℓ') * finrankAlong L (heckeBetaBar L N ℓ) := by
    rw [finrankAlong_comp, finrankAlong_towerSubstBar_roof L N ℓ ℓ' M hM hne]
  intro _ _ hβ hβ' hu hu' D
  exact Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    (heckeBetaBar L N ℓ') (heckeBetaBar L N ℓ)
    (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof_beta N ℓ ℓ' M hM).2)
    (towerSubstBar L (N * ℓ) ℓ' (dvd_of_eq_roof_beta N ℓ ℓ' M hM).1)
    hβ' hβ hu' hu hsq hfin hsep hgen hLD D

open ModularCurve.PhiGen in

theorem heckeBetaExchangeAt_of_primes_of_ne'
    (L : Type*) [Field L] [Algebra ℚ L] (N ℓ ℓ' M : ℕ)
    [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M]
    (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') (hM : M = N * ℓ * ℓ') :
    HeckeBetaExchangeAt L N ℓ ℓ' M hM :=
  heckeBetaExchangeAt_of_gen L N ℓ ℓ' M hℓ hℓ' hne hM
    (heckeBetaRoof_adjoin_range_union_eq_top L N ℓ ℓ' M hℓ hℓ' hne hM (functionFieldGeneration M)
      (modularPolynomialFamily ℓ hℓ).choose (modularPolynomialFamily ℓ' hℓ').choose)

end ModularCurve

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] (N ℓ ℓ' M : ℕ)
    [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M]
    (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') (hM : M = N * ℓ * ℓ') :
    HeckeBetaExchangeAt L N ℓ ℓ' M hM := by
  exact ModularCurve.heckeBetaExchangeAt_of_primes_of_ne' L N ℓ ℓ' M hℓ hℓ' hne hM

end S_ModularCurve_heckeBetaExchangeAt_of_primes_of_ne
end P2MW
export P2MW.S_ModularCurve_heckeBetaExchangeAt_of_primes_of_ne (solution)
