-- Prove2me | solution 1 for ModularCurve.IgusaScheme.isReduced_chartAlgFin_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/04aebd1e-d8f7-5757-876d-142a0e9c74f6

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_Polynomial_squarefree_of_squarefree_map
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_not_dvd
import Theorems.Thm_IsIntegrallyClosed_isReduced_quotient_span_singleton_of_squarefree_minpoly
import Theorems.Thm_ModularCurve_IgusaScheme_exists_mul_mem_adjoin_jFull_jqN
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgFin
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgInf
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_Subalgebra_isReduced_tensor_of_separable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jqN evalAtJ evalAtJ_X ModularPolynomialData jqN_mem modularFunctionFieldFull modularFunctionField_le_full transcendental_jq nonempty_modularPolynomialData ModularPolynomialData.separable_map_ratFunc_of_not_dvd"
p2m_open "ModularCurve"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull jFull_ne_zero mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin chartAlgInf exists_mul_mem_adjoin_jFull_jqN isIntegrallyClosed_chartAlgFin isIntegrallyClosed_chartAlgInf finiteType_chartAlgFin_and_chartAlgInf"
p2m_open "ModularCurve.IgusaScheme"

p2m_open "Polynomial P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.Polynomial IsLocalRing"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)

def jRing : Subalgebra ℤℓ FN := Algebra.adjoin ℤℓ {jFull N}

def jNFull : FN := ⟨jqN N, modularFunctionField_le_full N (jqN_mem N)⟩

@[scoped simp] theorem coe_jNFull : (jNFull N : LaurentSeries ℚ) = jqN N := rfl

theorem algebraMap_ratLocalizedAt_injective :
    Function.Injective (algebraMap ℤℓ ℚ) := Subtype.val_injective

theorem transcendental_jFull : Transcendental ℤℓ (jFull N) := by
  rintro ⟨p, hp0, hp⟩
  apply transcendental_jq
  refine ⟨p.map (algebraMap ℤℓ ℚ), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (algebraMap_ratLocalizedAt_injective ℓ)).mpr hp0
  · have h := congrArg (algebraMap FN (LaurentSeries ℚ)) hp
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂] at h
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap ℚ (LaurentSeries ℚ)).comp (algebraMap ℤℓ ℚ) =
        (algebraMap FN (LaurentSeries ℚ)).comp (algebraMap ℤℓ FN) := by
      refine RingHom.ext fun a => ?_
      change algebraMap ℚ (LaurentSeries ℚ) (a : ℚ) =
        ((algebraMap ℚ FN (a : ℚ) : FN) : LaurentSeries ℚ)
      first
        | rfl
        | exact (IntermediateField.algebraMap_apply _ _).symm
        | simp
    rw [hcomp]
    exact h

def jRingEquiv : ℤℓ[X] ≃ₐ[ℤℓ] jRing N ℓ :=
  (AlgEquiv.ofInjective (aeval (jFull N))
    ((transcendental_iff_injective).mp (transcendental_jFull N ℓ))).trans
    (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval ℤℓ (jFull N)).symm)

@[scoped simp] theorem coe_jRingEquiv (p : ℤℓ[X]) : ((jRingEquiv N ℓ p : jRing N ℓ) : FN) = aeval (jFull N) p := rfl

theorem jRingEquiv_C (a : ℤℓ) : jRingEquiv N ℓ (C a) = algebraMap ℤℓ (jRing N ℓ) a := by
  apply Subtype.ext; simp

scoped instance isPrincipalIdealRing_ZL : IsPrincipalIdealRing ℤℓ := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ

scoped instance isNoetherianRing_jRing : IsNoetherianRing (jRing N ℓ) :=
  isNoetherianRing_of_ringEquiv ℤℓ[X] (jRingEquiv N ℓ).toRingEquiv

scoped instance isIntegrallyClosed_jRing : IsIntegrallyClosed (jRing N ℓ) := by
  haveI : UniqueFactorizationMonoid ℤℓ[X] := inferInstance
  haveI : IsIntegrallyClosed ℤℓ[X] := inferInstance
  exact IsIntegrallyClosed.of_equiv (jRingEquiv N ℓ).toRingEquiv

theorem isPrime_span_natCast_ZL : (Ideal.span {(ℓ : ℤℓ)}).IsPrime := by
  have hirr := GaloisRep.irreducible_natCast_ratLocalizedAt ℓ (Fact.out)
  rw [Ideal.span_singleton_prime hirr.ne_zero]
  exact hirr.prime

theorem isPrime_span_natCast_jRing : (Ideal.span {(ℓ : jRing N ℓ)}).IsPrime := by
  haveI := isPrime_span_natCast_ZL ℓ
  have h1 : (Ideal.map (Polynomial.C : ℤℓ →+* ℤℓ[X]) (Ideal.span {(ℓ : ℤℓ)})).IsPrime :=
    Ideal.isPrime_map_C_of_isPrime
  rw [Ideal.map_span, Set.image_singleton] at h1
  haveI := h1
  have h2 : (Ideal.map ((jRingEquiv N ℓ).toRingEquiv : ℤℓ[X] →+* jRing N ℓ)
      (Ideal.span {Polynomial.C (ℓ : ℤℓ)})).IsPrime :=
    Ideal.map_isPrime_of_equiv (jRingEquiv N ℓ).toRingEquiv
  rw [Ideal.map_span, Set.image_singleton] at h2
  convert h2 using 3
  rw [show Polynomial.C (ℓ : ℤℓ) = (ℓ : ℤℓ[X]) from map_natCast _ ℓ, map_natCast]

end IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jqN evalAtJ evalAtJ_X ModularPolynomialData jqN_mem modularFunctionFieldFull modularFunctionField_le_full transcendental_jq nonempty_modularPolynomialData ModularPolynomialData.separable_map_ratFunc_of_not_dvd"
p2m_open "ModularCurve"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull jFull_ne_zero mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin chartAlgInf exists_mul_mem_adjoin_jFull_jqN isIntegrallyClosed_chartAlgFin isIntegrallyClosed_chartAlgInf finiteType_chartAlgFin_and_chartAlgInf"
p2m_open "ModularCurve.IgusaScheme"

p2m_open "Polynomial P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.Polynomial IsLocalRing"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)

def jElt : jRing N ℓ := ⟨jFull N, Algebra.self_mem_adjoin_singleton _ _⟩

def intPolyToJRing : ℤ[X] →+* jRing N ℓ := (aeval (R := ℤ) (jElt N ℓ)).toRingHom

theorem laurent_algebraMap_intPolyToJRing :
    ((algebraMap FN (LaurentSeries ℚ)).comp
      ((algebraMap (jRing N ℓ) FN).comp (intPolyToJRing N ℓ))) = evalAtJ := by
  apply Polynomial.ringHom_ext
  · intro a; simp
  · simp only [RingHom.comp_apply, intPolyToJRing, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      aeval_X, evalAtJ_X]
    rfl

theorem isIntegral_jNFull : IsIntegral (jRing N ℓ) (jNFull N) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  refine ⟨data.Φ.map (intPolyToJRing N ℓ), data.monic.map _, ?_⟩
  apply Subtype.val_injective
  change algebraMap FN (LaurentSeries ℚ) (Polynomial.eval₂ (algebraMap (jRing N ℓ) FN) (jNFull N)
    (data.Φ.map (intPolyToJRing N ℓ))) = ((0 : FN) : LaurentSeries ℚ)
  rw [Polynomial.eval₂_map, Polynomial.hom_eval₂, laurent_algebraMap_intPolyToJRing]
  simpa using data.eval_eq_zero

theorem aeval_jNFull_map_intPolyToJRing (data : ModularPolynomialData N) :
    Polynomial.aeval (jNFull N) (data.Φ.map (intPolyToJRing N ℓ)) = 0 := by
  apply Subtype.val_injective
  change algebraMap FN (LaurentSeries ℚ) (Polynomial.eval₂ (algebraMap (jRing N ℓ) FN) (jNFull N)
    (data.Φ.map (intPolyToJRing N ℓ))) = ((0 : FN) : LaurentSeries ℚ)
  rw [Polynomial.eval₂_map, Polynomial.hom_eval₂, laurent_algebraMap_intPolyToJRing]
  simpa using data.eval_eq_zero

theorem jNFull_mem_chartAlgFin : jNFull N ∈ chartAlgFin N ℓ := by
  rw [chartAlgFin, mem_chartAlg_iff]
  exact isIntegral_jNFull N ℓ

end IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jqN evalAtJ evalAtJ_X ModularPolynomialData jqN_mem modularFunctionFieldFull modularFunctionField_le_full transcendental_jq nonempty_modularPolynomialData ModularPolynomialData.separable_map_ratFunc_of_not_dvd"
p2m_open "ModularCurve"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull jFull_ne_zero mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin chartAlgInf exists_mul_mem_adjoin_jFull_jqN isIntegrallyClosed_chartAlgFin isIntegrallyClosed_chartAlgInf finiteType_chartAlgFin_and_chartAlgInf"
p2m_open "ModularCurve.IgusaScheme"

p2m_open "Polynomial P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.Polynomial IsLocalRing"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)

abbrev gaussPrime : Ideal (jRing N ℓ) := Ideal.span {(ℓ : jRing N ℓ)}

scoped instance isPrime_gaussPrime : (gaussPrime N ℓ).IsPrime := isPrime_span_natCast_jRing N ℓ

theorem natCast_ell_ne_zero_FN : (ℓ : FN) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ FN) ℓ, _root_.map_ne_zero]
  exact_mod_cast (Fact.out : ℓ.Prime).ne_zero

theorem natCast_ell_ne_zero_jRing : (ℓ : jRing N ℓ) ≠ 0 := by
  intro h
  apply natCast_ell_ne_zero_FN N ℓ
  have h' := congrArg (fun x : jRing N ℓ => (x : FN)) h
  simpa using h'

abbrev GaussRing : Type := Localization.AtPrime (gaussPrime N ℓ)

set_option synthInstance.maxHeartbeats 4000000 in
scoped instance (priority := 10000) algebraJRingGaussRing : Algebra (jRing N ℓ) (GaussRing N ℓ) :=
  inferInstance
scoped instance (priority := 10000) smulJRingGaussRing : SMul (jRing N ℓ) (GaussRing N ℓ) :=
  Algebra.toSMul

scoped instance isDiscreteValuationRing_gaussRing : IsDiscreteValuationRing (GaussRing N ℓ) := by
  apply IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes
    (natCast_ell_ne_zero_jRing N ℓ) (gaussPrime N ℓ)
  have hprim : (Ideal.span {(ℓ : jRing N ℓ)}).IsPrimary :=
    Ideal.IsPrime.isPrimary (isPrime_gaussPrime N ℓ)
  rw [associatedPrimes.eq_singleton_of_isPrimary hprim, Set.mem_singleton_iff]
  exact (Ideal.IsPrime.radical (isPrime_gaussPrime N ℓ)).symm

theorem algebraMap_jRing_apply (x : jRing N ℓ) : algebraMap (jRing N ℓ) FN x = x := rfl

theorem isUnit_algebraMap_primeCompl (s : (gaussPrime N ℓ).primeCompl) :
    IsUnit (algebraMap (jRing N ℓ) FN s) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  apply s.2
  have : (s : jRing N ℓ) = 0 := Subtype.val_injective (by simpa [algebraMap_jRing_apply] using h)
  rw [this]
  exact Ideal.zero_mem _

scoped instance algebraGaussRing : Algebra (GaussRing N ℓ) FN :=
  (IsLocalization.lift (M := (gaussPrime N ℓ).primeCompl) (S := GaussRing N ℓ)
    (g := algebraMap (jRing N ℓ) FN) (isUnit_algebraMap_primeCompl N ℓ)).toAlgebra

scoped instance (priority := 10000) smulGaussRingFN : SMul (GaussRing N ℓ) FN := Algebra.toSMul

theorem algebraMap_gaussRing_eq : algebraMap (GaussRing N ℓ) FN =
    IsLocalization.lift (M := (gaussPrime N ℓ).primeCompl) (S := GaussRing N ℓ)
      (g := algebraMap (jRing N ℓ) FN) (isUnit_algebraMap_primeCompl N ℓ) := rfl

scoped instance isScalarTower_gaussRing : IsScalarTower (jRing N ℓ) (GaussRing N ℓ) FN :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [algebraMap_gaussRing_eq N ℓ]
    exact (IsLocalization.lift_comp (M := (gaussPrime N ℓ).primeCompl)
      (isUnit_algebraMap_primeCompl N ℓ)).symm)

scoped instance faithfulSMul_gaussRing : FaithfulSMul (GaussRing N ℓ) FN := by
  rw [faithfulSMul_iff_algebraMap_injective, algebraMap_gaussRing_eq N ℓ,
    IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    rw [IsLocalization.injective (GaussRing N ℓ) (gaussPrime N ℓ).primeCompl_le_nonZeroDivisors h]
  · intro h
    rw [show x = y from Subtype.val_injective h]

theorem irreducible_algebraMap_natCast_gaussRing :
    Irreducible (algebraMap (jRing N ℓ) (GaussRing N ℓ) ℓ) := by
  refine (IsDiscreteValuationRing.irreducible_iff_uniformizer
    (algebraMap (jRing N ℓ) (GaussRing N ℓ) (ℓ : jRing N ℓ))).mpr ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]

theorem exists_mul_mem_of_gaussRing (x : GaussRing N ℓ) :
    ∃ s ∉ gaussPrime N ℓ, ∃ r : jRing N ℓ,
      algebraMap (jRing N ℓ) (GaussRing N ℓ) r = algebraMap (jRing N ℓ) (GaussRing N ℓ) s * x := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (gaussPrime N ℓ).primeCompl x
  exact ⟨s, s.2, r, (IsLocalization.mk'_spec' (GaussRing N ℓ) r s).symm⟩

theorem isIntegral_gaussRing_jNFull : IsIntegral (GaussRing N ℓ) (jNFull N) :=
  (isIntegral_jNFull N ℓ).tower_top

theorem jRing_le_chartAlgFin : (jRing N ℓ) ≤ chartAlgFin N ℓ := adjoin_le_chartAlg N ℓ _

scoped instance algebraJRingChartFin : Algebra (jRing N ℓ) (chartAlgFin N ℓ) :=
  (Subalgebra.inclusion (jRing_le_chartAlgFin N ℓ)).toRingHom.toAlgebra

scoped instance isScalarTower_jRing_chartFin : IsScalarTower (jRing N ℓ) (chartAlgFin N ℓ) FN :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance faithfulSMul_jRing_chartFin : FaithfulSMul (jRing N ℓ) (chartAlgFin N ℓ) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact Subalgebra.inclusion_injective _

scoped instance faithfulSMul_chartFin : FaithfulSMul (chartAlgFin N ℓ) FN := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact Subtype.val_injective

scoped instance isIntegral_jRing_chartFin : Algebra.IsIntegral (jRing N ℓ) (chartAlgFin N ℓ) := by
  refine ⟨fun a => ?_⟩
  have ha : IsIntegral (jRing N ℓ) (a : FN) := a.2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (jRing N ℓ) (chartAlgFin N ℓ) FN)
    Subtype.val_injective).mp ha

end IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jqN evalAtJ evalAtJ_X ModularPolynomialData jqN_mem modularFunctionFieldFull modularFunctionField_le_full transcendental_jq nonempty_modularPolynomialData ModularPolynomialData.separable_map_ratFunc_of_not_dvd"
p2m_open "ModularCurve"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull jFull_ne_zero mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin chartAlgInf exists_mul_mem_adjoin_jFull_jqN isIntegrallyClosed_chartAlgFin isIntegrallyClosed_chartAlgInf finiteType_chartAlgFin_and_chartAlgInf"
p2m_open "ModularCurve.IgusaScheme"

p2m_open "Polynomial P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.Polynomial IsLocalRing"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)
set_option quotPrecheck false in
local notation "𝔽" => AlgebraicClosure (ZMod ℓ)

scoped instance isPrime_span_ell_int : (Ideal.span {(ℓ : ℤ)}).IsPrime := by
  rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)]
  exact Nat.prime_iff_prime_int.mp Fact.out

scoped instance isLocalization_ZL : IsLocalization.AtPrime ℤℓ (Ideal.span {(ℓ : ℤ)}) :=
  GaloisRep.isLocalization_ratLocalizedAt Fact.out

def psiZL : ℤℓ →+* 𝔽 :=
  IsLocalization.lift (M := (Ideal.span {(ℓ : ℤ)}).primeCompl) (S := ℤℓ)
    (g := Int.castRingHom 𝔽) (by
      intro s
      apply isUnit_iff_ne_zero.mpr
      intro h
      apply s.2
      show (s : ℤ) ∈ Ideal.span {(ℓ : ℤ)}
      rw [Ideal.mem_span_singleton]
      have h' : ((s : ℤ) : 𝔽) = 0 := h
      exact (CharP.intCast_eq_zero_iff 𝔽 ℓ (s : ℤ)).mp h')

theorem psiZL_algebraMap (n : ℤ) : psiZL ℓ (algebraMap ℤ ℤℓ n) = (n : 𝔽) :=
  IsLocalization.lift_eq _ n

theorem psiZL_natCast_ell : psiZL ℓ (ℓ : ℤℓ) = 0 := by
  rw [map_natCast]
  exact CharP.cast_eq_zero 𝔽 ℓ

def psiR : jRing N ℓ →+* Polynomial 𝔽 :=
  (Polynomial.mapRingHom (psiZL ℓ)).comp (jRingEquiv N ℓ).symm.toRingEquiv.toRingHom

theorem psiR_jRingEquiv (p : ℤℓ[X]) : psiR N ℓ (jRingEquiv N ℓ p) = p.map (psiZL ℓ) := by
  change Polynomial.map (psiZL ℓ) ((jRingEquiv N ℓ).symm (jRingEquiv N ℓ p)) = _
  rw [AlgEquiv.symm_apply_apply]

theorem jRingEquiv_X : jRingEquiv N ℓ Polynomial.X = jElt N ℓ := by
  apply Subtype.ext
  simp [jElt]

theorem psiR_jElt : psiR N ℓ (jElt N ℓ) = Polynomial.X := by
  rw [← jRingEquiv_X, psiR_jRingEquiv, Polynomial.map_X]

theorem psiR_ne_zero_of_not_mem {s : jRing N ℓ} (hs : s ∉ gaussPrime N ℓ) : psiR N ℓ s ≠ 0 := by
  intro h
  apply hs
  obtain ⟨p, rfl⟩ := (jRingEquiv N ℓ).surjective s
  rw [psiR_jRingEquiv] at h

  have hcoeff : ∀ n, p.coeff n ∈ Ideal.span {(ℓ : ℤℓ)} := by
    intro n
    have hn : psiZL ℓ (p.coeff n) = 0 := by
      have := congrArg (fun q => Polynomial.coeff q n) h
      simpa [Polynomial.coeff_map] using this

    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective (Ideal.span {(ℓ : ℤ)}).primeCompl (p.coeff n)
    dsimp only at hat
    rw [← hat] at hn ⊢
    rw [psiZL, IsLocalization.lift_mk'] at hn
    simp only [Units.mul_left_eq_zero, eq_intCast] at hn
    have ha : (ℓ : ℤ) ∣ a := (CharP.intCast_eq_zero_iff 𝔽 ℓ a).mp hn
    obtain ⟨b, rfl⟩ := ha
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hp : p ∈ Ideal.map (Polynomial.C : ℤℓ →+* ℤℓ[X]) (Ideal.span {(ℓ : ℤℓ)}) := by
    rw [Ideal.mem_map_C_iff]; exact hcoeff
  rw [Ideal.map_span, Set.image_singleton] at hp

  have := Ideal.mem_map_of_mem ((jRingEquiv N ℓ).toRingEquiv : ℤℓ[X] →+* jRing N ℓ) hp
  rw [Ideal.map_span, Set.image_singleton] at this
  convert this using 2
  · rw [show Polynomial.C (ℓ : ℤℓ) = (ℓ : ℤℓ[X]) from map_natCast _ ℓ, map_natCast]
  all_goals rfl

def psiR' : jRing N ℓ →+* RatFunc 𝔽 := (algebraMap (Polynomial 𝔽) (RatFunc 𝔽)).comp (psiR N ℓ)

theorem isUnit_psiR'_primeCompl (s : (gaussPrime N ℓ).primeCompl) : IsUnit (psiR' N ℓ s) := by
  apply isUnit_iff_ne_zero.mpr
  rw [psiR', RingHom.comp_apply, map_ne_zero_iff _ (IsFractionRing.injective (Polynomial 𝔽) (RatFunc 𝔽))]
  exact psiR_ne_zero_of_not_mem N ℓ s.2

def psi : GaussRing N ℓ →+* RatFunc 𝔽 :=
  IsLocalization.lift (M := (gaussPrime N ℓ).primeCompl) (S := GaussRing N ℓ)
    (g := psiR' N ℓ) (isUnit_psiR'_primeCompl N ℓ)

theorem psi_algebraMap (r : jRing N ℓ) : psi N ℓ (algebraMap (jRing N ℓ) (GaussRing N ℓ) r) = psiR' N ℓ r :=
  IsLocalization.lift_eq _ r

theorem psi_ell : psi N ℓ (algebraMap (jRing N ℓ) (GaussRing N ℓ) ℓ) = 0 := by
  rw [psi_algebraMap, map_natCast, ← map_natCast (algebraMap 𝔽 (RatFunc 𝔽)) ℓ,
    CharP.cast_eq_zero 𝔽 ℓ, map_zero]

theorem psi_comp_intPolyToJRing :
    (psi N ℓ).comp ((algebraMap (jRing N ℓ) (GaussRing N ℓ)).comp (intPolyToJRing N ℓ)) =
      (algebraMap (Polynomial 𝔽) (RatFunc 𝔽)).comp
        (Polynomial.mapRingHom (Int.castRingHom 𝔽)) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, eq_intCast, map_intCast]
  · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_X]
    have hX : intPolyToJRing N ℓ Polynomial.X = jElt N ℓ := by simp [intPolyToJRing]
    rw [hX, psi_algebraMap, psiR', RingHom.comp_apply, psiR_jElt]

end IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"

namespace Polynomial p2m_export "Polynomial" "C scaleRoots scaleRoots_eval₂_eq_zero X coeff_natDegree support coeff_map natDegree_zero aeval_map_algebraMap aeval_def coeff eval₂_reflect_mul_pow lifts_and_natDegree_eq_and_monic monic_scaleRoots_iff eval₂ aeval factor aeval_C map_map reflect map_C map eval₂_X comp_assoc Monic comp algebra coe_mapRingHom separable_map reverse Separable natDegree eval₂_map aeval_mem_adjoin_singleton nontrivial X_ne_zero coeff_scaleRoots pow reverse_eq_zero mem_support_iff natDegree_map map_X aeval_X lifts_iff_coeff_lifts map_dvd eval₂_reverse_mul_pow algebraMap_apply map_ne_zero coeff_eq_zero_of_natDegree_lt mod eval_map ext mapRingHom eval₂_C hom_eval₂ natDegree_map_le ring ringHom_ext lifts transcendental eval₂RingHom eval squarefree_of_squarefree_map" end Polynomial
p2m_open_scoped "Polynomial" in

theorem Polynomial.squarefree_map_mk_of_squarefree_map {O L : Type*} [CommRing O] [CommRing L] [IsDomain L]
    {I : Ideal O} (hI : I.IsMaximal) (ψ : O →+* L) (hψ : ∀ a ∈ I, ψ a = 0)
    {f : Polynomial O} (hf : Squarefree (f.map ψ)) : Squarefree (f.map (Ideal.Quotient.mk I)) := by
  letI : Field (O ⧸ I) := Ideal.Quotient.field I
  apply Polynomial.squarefree_of_squarefree_map (Ideal.Quotient.lift I ψ hψ)
  rwa [Polynomial.map_map, Ideal.Quotient.lift_comp_mk]

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jqN evalAtJ evalAtJ_X ModularPolynomialData jqN_mem modularFunctionFieldFull modularFunctionField_le_full transcendental_jq nonempty_modularPolynomialData ModularPolynomialData.separable_map_ratFunc_of_not_dvd"
p2m_open "ModularCurve"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull jFull_ne_zero mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin chartAlgInf exists_mul_mem_adjoin_jFull_jqN isIntegrallyClosed_chartAlgFin isIntegrallyClosed_chartAlgInf finiteType_chartAlgFin_and_chartAlgInf"
p2m_open "ModularCurve.IgusaScheme"

p2m_open "Polynomial P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.Polynomial IsLocalRing"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)
set_option quotPrecheck false in
local notation "𝔽" => AlgebraicClosure (ZMod ℓ)

theorem psi_mem_ker (a : GaussRing N ℓ)
    (ha : a ∈ Ideal.span {algebraMap (jRing N ℓ) (GaussRing N ℓ) ℓ}) : psi N ℓ a = 0 := by
  rw [Ideal.mem_span_singleton'] at ha
  obtain ⟨b, rfl⟩ := ha
  rw [map_mul, psi_ell, mul_zero]

theorem maximalIdeal_gaussRing :
    IsLocalRing.maximalIdeal (GaussRing N ℓ) = Ideal.span {algebraMap (jRing N ℓ) (GaussRing N ℓ) ℓ} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]

theorem isMaximal_span_algebraMap_ell :
    (Ideal.span {algebraMap (jRing N ℓ) (GaussRing N ℓ) ℓ}).IsMaximal := by
  rw [← maximalIdeal_gaussRing N ℓ]
  infer_instance

noncomputable def PhiO (data : ModularPolynomialData N) : Polynomial (GaussRing N ℓ) :=
  (data.Φ.map (intPolyToJRing N ℓ)).map (algebraMap (jRing N ℓ) (GaussRing N ℓ))

theorem aeval_jNFull_PhiO (data : ModularPolynomialData N) : Polynomial.aeval (jNFull N) (PhiO N ℓ data) = 0 := by
  rw [PhiO, Polynomial.aeval_map_algebraMap]
  exact aeval_jNFull_map_intPolyToJRing N ℓ data

theorem minpoly_dvd_PhiO (data : ModularPolynomialData N) : minpoly (GaussRing N ℓ) (jNFull N) ∣ PhiO N ℓ data :=
  minpoly.isIntegrallyClosed_dvd (isIntegral_gaussRing_jNFull N ℓ) (aeval_jNFull_PhiO N ℓ data)

theorem PhiO_map_psi (data : ModularPolynomialData N) :
    (PhiO N ℓ data).map (psi N ℓ) =
      (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom 𝔽))).map
        (algebraMap (Polynomial 𝔽) (RatFunc 𝔽)) := by
  rw [PhiO, Polynomial.map_map, Polynomial.map_map, RingHom.comp_assoc, psi_comp_intPolyToJRing,
    ← Polynomial.map_map]

theorem squarefree_PhiO_map_psi (data : ModularPolynomialData N) (hℓN : ¬ ℓ ∣ N) :
    Squarefree ((PhiO N ℓ data).map (psi N ℓ)) := by
  rw [PhiO_map_psi]
  exact (ModularPolynomialData.separable_map_ratFunc_of_not_dvd N data ℓ hℓN).squarefree

theorem squarefree_minpoly_map_psi (hℓN : ¬ ℓ ∣ N) :
    Squarefree ((minpoly (GaussRing N ℓ) (jNFull N)).map (psi N ℓ)) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  exact (squarefree_PhiO_map_psi N ℓ data hℓN).squarefree_of_dvd
    (Polynomial.map_dvd _ (minpoly_dvd_PhiO N ℓ data))

end IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jqN evalAtJ evalAtJ_X ModularPolynomialData jqN_mem modularFunctionFieldFull modularFunctionField_le_full transcendental_jq nonempty_modularPolynomialData ModularPolynomialData.separable_map_ratFunc_of_not_dvd"
p2m_open "ModularCurve"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull jFull_ne_zero mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin chartAlgInf exists_mul_mem_adjoin_jFull_jqN isIntegrallyClosed_chartAlgFin isIntegrallyClosed_chartAlgInf finiteType_chartAlgFin_and_chartAlgInf"
p2m_open "ModularCurve.IgusaScheme"

p2m_open "Polynomial P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.Polynomial IsLocalRing"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)

theorem jNFull_eq : jNFull N = ⟨jqN N, modularFunctionField_le_full N (jqN_mem N)⟩ := rfl

theorem adjoin_jFull_jN_le :
    (Algebra.adjoin ℤℓ ({jFull N, jNFull N} : Set FN) : Set FN) ⊆
      (Algebra.adjoin (GaussRing N ℓ) ({jNFull N} : Set FN) : Set FN) := by
  intro x hx
  change x ∈ Algebra.adjoin (GaussRing N ℓ) ({jNFull N} : Set FN)
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    ·
      have : (jFull N : FN) = algebraMap (GaussRing N ℓ) FN (algebraMap (jRing N ℓ) (GaussRing N ℓ) (jElt N ℓ)) := by
        rw [← IsScalarTower.algebraMap_apply]; rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    · exact Algebra.self_mem_adjoin_singleton _ _
  | algebraMap c =>
    have : algebraMap ℤℓ FN c = algebraMap (GaussRing N ℓ) FN
        (algebraMap (jRing N ℓ) (GaussRing N ℓ) (algebraMap ℤℓ (jRing N ℓ) c)) := by
      rw [← IsScalarTower.algebraMap_apply (jRing N ℓ) (GaussRing N ℓ) FN]; rfl
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem exists_pow_ell_mul_mem_adjoin_gaussRing (x : FN) :
    ∃ n : ℕ, algebraMap (GaussRing N ℓ) FN (algebraMap (jRing N ℓ) (GaussRing N ℓ) ℓ) ^ n * x ∈
      Algebra.adjoin (GaussRing N ℓ) ({jNFull N} : Set FN) := by
  obtain ⟨g, hg, hg0, hgx⟩ := exists_mul_mem_adjoin_jFull_jqN N ℓ x
  rw [← jNFull_eq] at hgx

  set g' : jRing N ℓ := ⟨g, hg⟩ with hg'
  have hg'0 : g' ≠ 0 := fun h => hg0 (congrArg Subtype.val h)
  have hirr : Irreducible (ℓ : jRing N ℓ) := by
    have hp : Prime (ℓ : jRing N ℓ) :=
      (Ideal.span_singleton_prime (natCast_ell_ne_zero_jRing N ℓ)).mp (isPrime_gaussPrime N ℓ)
    exact hp.irreducible
  obtain ⟨n, g₀, hg₀, hfac⟩ := WfDvdMonoid.max_power_factor hg'0 hirr
  have hg₀P : g₀ ∉ gaussPrime N ℓ := by rwa [Ideal.mem_span_singleton]

  have hu : IsUnit (algebraMap (jRing N ℓ) (GaussRing N ℓ) g₀) :=
    IsLocalization.map_units (GaussRing N ℓ) (⟨g₀, hg₀P⟩ : (gaussPrime N ℓ).primeCompl)
  obtain ⟨u, hu⟩ := hu
  refine ⟨n, ?_⟩
  have hmem : (g : FN) * x ∈ Algebra.adjoin (GaussRing N ℓ) ({jNFull N} : Set FN) :=
    adjoin_jFull_jN_le N ℓ hgx

  have hgF : (g : FN) = algebraMap (GaussRing N ℓ) FN (algebraMap (jRing N ℓ) (GaussRing N ℓ) ℓ) ^ n *
      algebraMap (GaussRing N ℓ) FN ↑u := by
    rw [hu, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← hfac, ← IsScalarTower.algebraMap_apply]
    rfl
  have key : algebraMap (GaussRing N ℓ) FN (algebraMap (jRing N ℓ) (GaussRing N ℓ) ℓ) ^ n * x =
      algebraMap (GaussRing N ℓ) FN ↑u⁻¹ * ((g : FN) * x) := by
    rw [hgF]
    have huu : algebraMap (GaussRing N ℓ) FN ↑u⁻¹ * algebraMap (GaussRing N ℓ) FN ↑u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination
      (-(algebraMap (GaussRing N ℓ) FN (algebraMap (jRing N ℓ) (GaussRing N ℓ) ℓ) ^ n * x)) * huu
  rw [key]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hmem

end IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jqN evalAtJ evalAtJ_X ModularPolynomialData jqN_mem modularFunctionFieldFull modularFunctionField_le_full transcendental_jq nonempty_modularPolynomialData ModularPolynomialData.separable_map_ratFunc_of_not_dvd"
p2m_open "ModularCurve"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull jFull_ne_zero mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin chartAlgInf exists_mul_mem_adjoin_jFull_jqN isIntegrallyClosed_chartAlgFin isIntegrallyClosed_chartAlgInf finiteType_chartAlgFin_and_chartAlgInf"
p2m_open "ModularCurve.IgusaScheme"

p2m_open "Polynomial P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.Polynomial IsLocalRing"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)

scoped instance isNoetherianRing_chartAlgFin : IsNoetherianRing (chartAlgFin N ℓ) := by
  haveI : Algebra.FiniteType ℤℓ (chartAlgFin N ℓ) := (finiteType_chartAlgFin_and_chartAlgInf N ℓ).1
  exact Algebra.FiniteType.isNoetherianRing ℤℓ (chartAlgFin N ℓ)

theorem isReduced_chartAlgFin_quotient_span_natCast (hℓN : ¬ ℓ ∣ N) :
    IsReduced (↥(chartAlgFin N ℓ) ⧸ Ideal.span {((ℓ : ℕ) : ↥(chartAlgFin N ℓ))}) := by
  haveI : IsIntegrallyClosed (chartAlgFin N ℓ) := isIntegrallyClosed_chartAlgFin N ℓ
  have h1 : (1 : jRing N ℓ) ∉ Ideal.span {(ℓ : jRing N ℓ)} :=
    (Ideal.ne_top_iff_one _).mp (isPrime_gaussPrime N ℓ).ne_top
  have key := IsIntegrallyClosed.isReduced_quotient_span_singleton_of_squarefree_minpoly
    (R := jRing N ℓ) (A := chartAlgFin N ℓ) (O := GaussRing N ℓ) (F := FN)
    (p := (ℓ : jRing N ℓ)) (isPrime_gaussPrime N ℓ) (natCast_ell_ne_zero_jRing N ℓ)
    (irreducible_algebraMap_natCast_gaussRing N ℓ) (exists_mul_mem_of_gaussRing N ℓ)
    (α := jNFull N) (isIntegral_gaussRing_jNFull N ℓ)
    ⟨1, h1, ⟨jNFull N, jNFull_mem_chartAlgFin N ℓ⟩, by simp⟩
    (Polynomial.squarefree_map_mk_of_squarefree_map (isMaximal_span_algebraMap_ell N ℓ)
      (psi N ℓ) (psi_mem_ker N ℓ) (squarefree_minpoly_map_psi N ℓ hℓN))
    (exists_pow_ell_mul_mem_adjoin_gaussRing N ℓ)
  first | exact key | simpa [map_natCast] using key

end IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jqN evalAtJ evalAtJ_X ModularPolynomialData jqN_mem modularFunctionFieldFull modularFunctionField_le_full transcendental_jq nonempty_modularPolynomialData ModularPolynomialData.separable_map_ratFunc_of_not_dvd"
p2m_open "ModularCurve"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull jFull_ne_zero mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin chartAlgInf exists_mul_mem_adjoin_jFull_jqN isIntegrallyClosed_chartAlgFin isIntegrallyClosed_chartAlgInf finiteType_chartAlgFin_and_chartAlgInf"
p2m_open "ModularCurve.IgusaScheme"

p2m_open "Polynomial P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.Polynomial IsLocalRing"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)
set_option quotPrecheck false in
local notation "𝔽" => AlgebraicClosure (ZMod ℓ)

abbrev jInv : FN := (jFull N)⁻¹

theorem jInv_ne_zero : jInv N ≠ 0 := inv_ne_zero (jFull_ne_zero N)

theorem transcendental_jInv : Transcendental ℤℓ (jInv N) := by
  rintro ⟨p, hp0, hp⟩
  apply transcendental_jFull N ℓ
  letI : Invertible (jInv N) := invertibleOfNonzero (jInv_ne_zero N)
  refine ⟨p.reverse, fun h => hp0 (Polynomial.reverse_eq_zero.mp h), ?_⟩
  have key := Polynomial.eval₂_reverse_mul_pow (algebraMap ℤℓ FN) (jInv N) p
  rw [Polynomial.aeval_def] at hp
  have h2 : Polynomial.eval₂ (algebraMap ℤℓ FN) (⅟ (jInv N)) p.reverse = 0 := by
    rcases mul_eq_zero.mp (key.trans hp) with h | h
    · exact h
    · exact absurd h (pow_ne_zero _ (jInv_ne_zero N))
  rwa [invOf_eq_inv, inv_inv, ← Polynomial.aeval_def] at h2

def jInvRing : Subalgebra ℤℓ FN := Algebra.adjoin ℤℓ {jInv N}

def jInvRingEquiv : ℤℓ[X] ≃ₐ[ℤℓ] jInvRing N ℓ :=
  (AlgEquiv.ofInjective (aeval (jInv N))
    ((transcendental_iff_injective).mp (transcendental_jInv N ℓ))).trans
    (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval ℤℓ (jInv N)).symm)

@[scoped simp] theorem coe_jInvRingEquiv (p : ℤℓ[X]) :
    ((jInvRingEquiv N ℓ p : jInvRing N ℓ) : FN) = aeval (jInv N) p := rfl

theorem algebraMap_jInvRing_apply (x : jInvRing N ℓ) : algebraMap (jInvRing N ℓ) FN x = x := rfl

scoped instance isNoetherianRing_jInvRing : IsNoetherianRing (jInvRing N ℓ) :=
  isNoetherianRing_of_ringEquiv ℤℓ[X] (jInvRingEquiv N ℓ).toRingEquiv

scoped instance isIntegrallyClosed_jInvRing : IsIntegrallyClosed (jInvRing N ℓ) := by
  haveI : UniqueFactorizationMonoid ℤℓ[X] := inferInstance
  haveI : IsIntegrallyClosed ℤℓ[X] := inferInstance
  exact IsIntegrallyClosed.of_equiv (jInvRingEquiv N ℓ).toRingEquiv

theorem isPrime_span_natCast_jInvRing : (Ideal.span {(ℓ : jInvRing N ℓ)}).IsPrime := by
  haveI := isPrime_span_natCast_ZL ℓ
  have h1 : (Ideal.map (Polynomial.C : ℤℓ →+* ℤℓ[X]) (Ideal.span {(ℓ : ℤℓ)})).IsPrime :=
    Ideal.isPrime_map_C_of_isPrime
  rw [Ideal.map_span, Set.image_singleton] at h1
  haveI := h1
  have h2 : (Ideal.map ((jInvRingEquiv N ℓ).toRingEquiv : ℤℓ[X] →+* jInvRing N ℓ)
      (Ideal.span {Polynomial.C (ℓ : ℤℓ)})).IsPrime :=
    Ideal.map_isPrime_of_equiv (jInvRingEquiv N ℓ).toRingEquiv
  rw [Ideal.map_span, Set.image_singleton] at h2
  convert h2 using 3
  rw [show Polynomial.C (ℓ : ℤℓ) = (ℓ : ℤℓ[X]) from map_natCast _ ℓ, map_natCast]

theorem natCast_ell_ne_zero_jInvRing : (ℓ : jInvRing N ℓ) ≠ 0 := by
  intro h
  apply natCast_ell_ne_zero_FN N ℓ
  have h' := congrArg (fun x : jInvRing N ℓ => (x : FN)) h
  simpa using h'

def jInvElt : jInvRing N ℓ := ⟨jInv N, Algebra.self_mem_adjoin_singleton _ _⟩

@[scoped simp] theorem coe_jInvElt : (jInvElt N ℓ : FN) = jInv N := rfl

theorem jInvRingEquiv_X : jInvRingEquiv N ℓ Polynomial.X = jInvElt N ℓ := by
  apply Subtype.ext
  simp [jInvElt]

theorem psiR_natCast_ell : psiR N ℓ (ℓ : jRing N ℓ) = 0 := by
  rw [map_natCast]
  exact CharP.cast_eq_zero _ ℓ

theorem jElt_notMem_gaussPrime : jElt N ℓ ∉ gaussPrime N ℓ := by
  intro h
  rw [Ideal.mem_span_singleton'] at h
  obtain ⟨t, ht⟩ := h
  have := congrArg (psiR N ℓ) ht
  rw [map_mul, psiR_natCast_ell, mul_zero, psiR_jElt] at this
  exact Polynomial.X_ne_zero this.symm

def jUnit : (GaussRing N ℓ)ˣ :=
  (IsLocalization.map_units (GaussRing N ℓ)
    (⟨jElt N ℓ, jElt_notMem_gaussPrime N ℓ⟩ : (gaussPrime N ℓ).primeCompl)).unit

theorem coe_jUnit : (jUnit N ℓ : GaussRing N ℓ) = algebraMap (jRing N ℓ) (GaussRing N ℓ) (jElt N ℓ) :=
  rfl

theorem algebraMap_jUnit : algebraMap (GaussRing N ℓ) FN (jUnit N ℓ) = jFull N := by
  rw [coe_jUnit, ← IsScalarTower.algebraMap_apply]; rfl

theorem algebraMap_jUnit_inv : algebraMap (GaussRing N ℓ) FN ↑(jUnit N ℓ)⁻¹ = jInv N := by
  rw [map_units_inv, algebraMap_jUnit]

def zlToGauss : ℤℓ →+* GaussRing N ℓ :=
  (algebraMap (jRing N ℓ) (GaussRing N ℓ)).comp (algebraMap ℤℓ (jRing N ℓ))

def jInvRingToGauss : jInvRing N ℓ →+* GaussRing N ℓ :=
  (Polynomial.eval₂RingHom (zlToGauss N ℓ) (↑(jUnit N ℓ)⁻¹ : GaussRing N ℓ)).comp
    (jInvRingEquiv N ℓ).symm.toRingEquiv.toRingHom

theorem jInvRingToGauss_jInvRingEquiv (p : ℤℓ[X]) :
    jInvRingToGauss N ℓ (jInvRingEquiv N ℓ p) = p.eval₂ (zlToGauss N ℓ) ↑(jUnit N ℓ)⁻¹ := by
  change Polynomial.eval₂ _ _ ((jInvRingEquiv N ℓ).symm (jInvRingEquiv N ℓ p)) = _
  rw [AlgEquiv.symm_apply_apply]

theorem algebraMap_zlToGauss (a : ℤℓ) : algebraMap (GaussRing N ℓ) FN (zlToGauss N ℓ a) = algebraMap ℤℓ FN a := by
  rw [zlToGauss, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem algebraMap_comp_jInvRingToGauss :
    (algebraMap (GaussRing N ℓ) FN).comp (jInvRingToGauss N ℓ) = algebraMap (jInvRing N ℓ) FN := by
  have h : ((algebraMap (GaussRing N ℓ) FN).comp (jInvRingToGauss N ℓ)).comp
        (jInvRingEquiv N ℓ).toRingEquiv.toRingHom =
      (algebraMap (jInvRing N ℓ) FN).comp (jInvRingEquiv N ℓ).toRingEquiv.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change algebraMap (GaussRing N ℓ) FN (jInvRingToGauss N ℓ (jInvRingEquiv N ℓ (C a))) =
        ((jInvRingEquiv N ℓ (C a) : jInvRing N ℓ) : FN)
      rw [jInvRingToGauss_jInvRingEquiv, Polynomial.eval₂_C, coe_jInvRingEquiv, aeval_C, algebraMap_zlToGauss]
    · change algebraMap (GaussRing N ℓ) FN (jInvRingToGauss N ℓ (jInvRingEquiv N ℓ X)) =
        ((jInvRingEquiv N ℓ X : jInvRing N ℓ) : FN)
      rw [jInvRingToGauss_jInvRingEquiv, Polynomial.eval₂_X, coe_jInvRingEquiv, aeval_X, algebraMap_jUnit_inv]
  refine RingHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := (jInvRingEquiv N ℓ).surjective x
  exact RingHom.congr_fun h p

scoped instance (priority := 10000) algebraJInvRingGaussRing : Algebra (jInvRing N ℓ) (GaussRing N ℓ) :=
  (jInvRingToGauss N ℓ).toAlgebra

scoped instance (priority := 10000) smulJInvRingGaussRing : SMul (jInvRing N ℓ) (GaussRing N ℓ) :=
  Algebra.toSMul

theorem algebraMap_jInvRing_gaussRing :
    algebraMap (jInvRing N ℓ) (GaussRing N ℓ) = jInvRingToGauss N ℓ := rfl

scoped instance isScalarTower_jInvRing_gaussRing : IsScalarTower (jInvRing N ℓ) (GaussRing N ℓ) FN :=
  IsScalarTower.of_algebraMap_eq' (algebraMap_comp_jInvRingToGauss N ℓ).symm

theorem jInvRingToGauss_natCast :
    jInvRingToGauss N ℓ (ℓ : jInvRing N ℓ) = algebraMap (jRing N ℓ) (GaussRing N ℓ) ℓ := by
  rw [map_natCast, map_natCast]

theorem jInvRingToGauss_jInvElt : jInvRingToGauss N ℓ (jInvElt N ℓ) = ↑(jUnit N ℓ)⁻¹ := by
  rw [← jInvRingEquiv_X, jInvRingToGauss_jInvRingEquiv, Polynomial.eval₂_X]

theorem notMem_span_of_isUnit {y : jInvRing N ℓ} (hy : IsUnit (jInvRingToGauss N ℓ y)) :
    y ∉ Ideal.span {(ℓ : jInvRing N ℓ)} := by
  intro h
  rw [Ideal.mem_span_singleton'] at h
  obtain ⟨t, rfl⟩ := h
  rw [map_mul, jInvRingToGauss_natCast] at hy
  have hmem : jInvRingToGauss N ℓ t * algebraMap (jRing N ℓ) (GaussRing N ℓ) ℓ ∈
      IsLocalRing.maximalIdeal (GaussRing N ℓ) := by
    rw [maximalIdeal_gaussRing N ℓ]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem) hy

theorem aeval_jFull_mul_jInv_pow (p : ℤℓ[X]) {d : ℕ} (hd : p.natDegree ≤ d) :
    aeval (jFull N) p * (jInv N) ^ d = aeval (jInv N) (reflect d p) := by
  letI : Invertible (jFull N) := invertibleOfNonzero (jFull_ne_zero N)
  have h := Polynomial.eval₂_reflect_mul_pow (algebraMap ℤℓ FN) (jFull N) d p hd
  rw [invOf_eq_inv] at h
  rw [Polynomial.aeval_def, Polynomial.aeval_def, ← h, mul_assoc, ← mul_pow,
    mul_inv_cancel₀ (jFull_ne_zero N), one_pow, mul_one]

theorem algebraMap_gaussRing_injective : Function.Injective (algebraMap (GaussRing N ℓ) FN) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mp inferInstance

theorem exists_mul_mem_of_gaussRing_inv (x : GaussRing N ℓ) :
    ∃ s ∉ Ideal.span {(ℓ : jInvRing N ℓ)}, ∃ r : jInvRing N ℓ,
      algebraMap (jInvRing N ℓ) (GaussRing N ℓ) r =
        algebraMap (jInvRing N ℓ) (GaussRing N ℓ) s * x := by
  obtain ⟨s, hs, r, hrs⟩ := exists_mul_mem_of_gaussRing N ℓ x
  obtain ⟨ps, rfl⟩ := (jRingEquiv N ℓ).surjective s
  obtain ⟨pr, rfl⟩ := (jRingEquiv N ℓ).surjective r
  refine ⟨jInvRingEquiv N ℓ (reflect (max ps.natDegree pr.natDegree) ps), ?_,
    jInvRingEquiv N ℓ (reflect (max ps.natDegree pr.natDegree) pr), ?_⟩
  · apply notMem_span_of_isUnit
    have heq : jInvRingToGauss N ℓ (jInvRingEquiv N ℓ (reflect (max ps.natDegree pr.natDegree) ps)) =
        ↑((jUnit N ℓ)⁻¹ ^ max ps.natDegree pr.natDegree) *
          algebraMap (jRing N ℓ) (GaussRing N ℓ) (jRingEquiv N ℓ ps) := by
      apply algebraMap_gaussRing_injective N ℓ
      rw [map_mul, ← algebraMap_jInvRing_gaussRing, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply, Units.val_pow_eq_pow_val, map_pow, algebraMap_jUnit_inv,
        algebraMap_jInvRing_apply, algebraMap_jRing_apply, coe_jInvRingEquiv, coe_jRingEquiv,
        ← aeval_jFull_mul_jInv_pow N ℓ ps (le_max_left _ _), mul_comm]
    rw [heq]
    exact (Units.isUnit _).mul
      (IsLocalization.map_units (GaussRing N ℓ) (⟨_, hs⟩ : (gaussPrime N ℓ).primeCompl))
  · apply algebraMap_gaussRing_injective N ℓ
    have hrsF := congrArg (algebraMap (GaussRing N ℓ) FN) hrs
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      algebraMap_jRing_apply, algebraMap_jRing_apply, coe_jRingEquiv, coe_jRingEquiv] at hrsF
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      algebraMap_jInvRing_apply, algebraMap_jInvRing_apply, coe_jInvRingEquiv, coe_jInvRingEquiv,
      ← aeval_jFull_mul_jInv_pow N ℓ pr (le_max_right _ _),
      ← aeval_jFull_mul_jInv_pow N ℓ ps (le_max_left _ _), hrsF]
    ring

theorem jInvRing_le_chartAlgInf : (jInvRing N ℓ) ≤ chartAlgInf N ℓ := adjoin_le_chartAlg N ℓ _

scoped instance algebraJInvRingChartInf : Algebra (jInvRing N ℓ) (chartAlgInf N ℓ) :=
  (Subalgebra.inclusion (jInvRing_le_chartAlgInf N ℓ)).toRingHom.toAlgebra

scoped instance isScalarTower_jInvRing_chartInf : IsScalarTower (jInvRing N ℓ) (chartAlgInf N ℓ) FN :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance faithfulSMul_jInvRing_chartInf : FaithfulSMul (jInvRing N ℓ) (chartAlgInf N ℓ) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact Subalgebra.inclusion_injective _

scoped instance faithfulSMul_chartInf : FaithfulSMul (chartAlgInf N ℓ) FN := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact Subtype.val_injective

scoped instance isIntegral_jInvRing_chartInf : Algebra.IsIntegral (jInvRing N ℓ) (chartAlgInf N ℓ) := by
  refine ⟨fun a => ?_⟩
  have ha : IsIntegral (jInvRing N ℓ) (a : FN) := a.2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (jInvRing N ℓ) (chartAlgInf N ℓ) FN)
    Subtype.val_injective).mp ha

scoped instance isNoetherianRing_chartAlgInf : IsNoetherianRing (chartAlgInf N ℓ) := by
  haveI : Algebra.FiniteType ℤℓ (chartAlgInf N ℓ) := (finiteType_chartAlgFin_and_chartAlgInf N ℓ).2
  exact Algebra.FiniteType.isNoetherianRing ℤℓ (chartAlgInf N ℓ)

def intPolyToFN : ℤ[X] →+* FN := (algebraMap (jRing N ℓ) FN).comp (intPolyToJRing N ℓ)

theorem intPolyToFN_eq_aeval_map (c : ℤ[X]) :
    intPolyToFN N ℓ c = aeval (jFull N) (c.map (algebraMap ℤ ℤℓ)) := by
  have h : intPolyToFN N ℓ = (aeval (jFull N)).toRingHom.comp (mapRingHom (algebraMap ℤ ℤℓ)) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [intPolyToFN, intPolyToJRing]
    · simp only [intPolyToFN, intPolyToJRing, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, aeval_X, coe_mapRingHom, Polynomial.map_X]
      rfl
  rw [h]
  rfl

theorem intPolyToFN_mul_jInv_pow_mem (c : ℤ[X]) {d : ℕ} (hd : c.natDegree ≤ d) :
    intPolyToFN N ℓ c * jInv N ^ d ∈ jInvRing N ℓ := by
  rw [intPolyToFN_eq_aeval_map, aeval_jFull_mul_jInv_pow N ℓ _ (natDegree_map_le.trans hd)]
  exact aeval_mem_adjoin_singleton ℤℓ (jInv N)

def PhiF (data : ModularPolynomialData N) : Polynomial FN := data.Φ.map (intPolyToFN N ℓ)

theorem PhiF_monic (data : ModularPolynomialData N) : (PhiF N ℓ data).Monic := data.monic.map _

theorem eval_jNFull_PhiF (data : ModularPolynomialData N) : (PhiF N ℓ data).eval (jNFull N) = 0 := by
  rw [PhiF, eval_map, intPolyToFN, ← Polynomial.eval₂_map, ← Polynomial.aeval_def]
  exact aeval_jNFull_map_intPolyToJRing N ℓ data

def coeffDegBound (data : ModularPolynomialData N) : ℕ :=
  data.Φ.support.sup fun b => (data.Φ.coeff b).natDegree

theorem natDegree_coeff_le (data : ModularPolynomialData N) (b : ℕ) :
    (data.Φ.coeff b).natDegree ≤ coeffDegBound N data := by
  by_cases hb : b ∈ data.Φ.support
  · exact Finset.le_sup (f := fun b => (data.Φ.coeff b).natDegree) hb
  · have : data.Φ.coeff b = 0 := by simpa [Polynomial.mem_support_iff] using hb
    rw [this, natDegree_zero]
    exact Nat.zero_le _

theorem isIntegral_jInvRing_jInv_pow_mul_jNFull (data : ModularPolynomialData N) :
    IsIntegral (jInvRing N ℓ) (jInv N ^ coeffDegBound N data * jNFull N) := by
  have hQmonic : ((PhiF N ℓ data).scaleRoots (jInv N ^ coeffDegBound N data)).Monic :=
    (monic_scaleRoots_iff _).mpr (PhiF_monic N ℓ data)
  have hQeval : ((PhiF N ℓ data).scaleRoots (jInv N ^ coeffDegBound N data)).eval
      (jInv N ^ coeffDegBound N data * jNFull N) = 0 := by
    have := scaleRoots_eval₂_eq_zero (RingHom.id FN) (s := jInv N ^ coeffDegBound N data)
      (p := PhiF N ℓ data) (r := jNFull N) (eval_jNFull_PhiF N ℓ data)
    simpa using this
  have hn : (PhiF N ℓ data).natDegree = data.Φ.natDegree := (data.monic).natDegree_map _
  have hlifts : (PhiF N ℓ data).scaleRoots (jInv N ^ coeffDegBound N data) ∈
      Polynomial.lifts (algebraMap (jInvRing N ℓ) FN) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    suffices h : ((PhiF N ℓ data).scaleRoots (jInv N ^ coeffDegBound N data)).coeff i ∈ jInvRing N ℓ from
      ⟨⟨_, h⟩, rfl⟩
    rw [coeff_scaleRoots, hn]
    rcases lt_or_ge i data.Φ.natDegree with hi | hi
    · rw [PhiF, Polynomial.coeff_map]
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hi
      rw [hk, show i + k + 1 - i = k + 1 by omega, pow_succ, ← mul_assoc, mul_right_comm]
      exact Subalgebra.mul_mem _ (intPolyToFN_mul_jInv_pow_mem N ℓ _ (natDegree_coeff_le N data i))
        (Subalgebra.pow_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤℓ (jInv N)) _) _)
    · rw [Nat.sub_eq_zero_of_le hi, pow_zero, mul_one]
      rcases hi.eq_or_lt with h | h
      · rw [← h, ← hn, (PhiF_monic N ℓ data).coeff_natDegree]
        exact Subalgebra.one_mem _
      · rw [PhiF, coeff_eq_zero_of_natDegree_lt ((data.monic.natDegree_map (intPolyToFN N ℓ)).symm ▸ h)]
        exact Subalgebra.zero_mem _
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlifts hQmonic
  refine ⟨q, hqm, ?_⟩
  rw [← eval_map, hq]
  exact hQeval

theorem jInv_pow_mul_jNFull_mem_chartAlgInf (data : ModularPolynomialData N) :
    jInv N ^ coeffDegBound N data * jNFull N ∈ chartAlgInf N ℓ := by
  rw [chartAlgInf, mem_chartAlg_iff]
  exact isIntegral_jInvRing_jInv_pow_mul_jNFull N ℓ data

theorem jInvElt_pow_notMem (M : ℕ) : jInvElt N ℓ ^ M ∉ Ideal.span {(ℓ : jInvRing N ℓ)} := by
  apply notMem_span_of_isUnit
  rw [map_pow, jInvRingToGauss_jInvElt]
  exact (Units.isUnit _).pow _

theorem isReduced_chartAlgInf_quotient_span_natCast (hℓN : ¬ ℓ ∣ N) :
    IsReduced (↥(chartAlgInf N ℓ) ⧸ Ideal.span {((ℓ : ℕ) : ↥(chartAlgInf N ℓ))}) := by
  haveI : IsIntegrallyClosed (chartAlgInf N ℓ) := isIntegrallyClosed_chartAlgInf N ℓ
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have e : algebraMap (jInvRing N ℓ) (GaussRing N ℓ) (ℓ : jInvRing N ℓ) =
      algebraMap (jRing N ℓ) (GaussRing N ℓ) (ℓ : jRing N ℓ) := by rw [map_natCast, map_natCast]
  have hpO := irreducible_algebraMap_natCast_gaussRing N ℓ
  rw [← e] at hpO
  have hsq := Polynomial.squarefree_map_mk_of_squarefree_map (O := GaussRing N ℓ) (L := RatFunc 𝔽)
    (f := minpoly (GaussRing N ℓ) (jNFull N)) (isMaximal_span_algebraMap_ell N ℓ)
    (psi N ℓ) (psi_mem_ker N ℓ) (squarefree_minpoly_map_psi N ℓ hℓN)
  rw [← e] at hsq
  have hgen := exists_pow_ell_mul_mem_adjoin_gaussRing N ℓ
  rw [← e] at hgen
  have key := IsIntegrallyClosed.isReduced_quotient_span_singleton_of_squarefree_minpoly
    (R := jInvRing N ℓ) (A := chartAlgInf N ℓ) (O := GaussRing N ℓ) (F := FN)
    (p := (ℓ : jInvRing N ℓ)) (isPrime_span_natCast_jInvRing N ℓ) (natCast_ell_ne_zero_jInvRing N ℓ)
    hpO (exists_mul_mem_of_gaussRing_inv N ℓ)
    (α := jNFull N) (isIntegral_gaussRing_jNFull N ℓ)
    ⟨jInvElt N ℓ ^ coeffDegBound N data, jInvElt_pow_notMem N ℓ _,
      ⟨_, jInv_pow_mul_jNFull_mem_chartAlgInf N ℓ data⟩, by simp [jInvElt]⟩
    hsq hgen
  first | exact key | simpa [map_natCast] using key

end IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"

p2m_open_scoped "Polynomial" in

theorem Polynomial.separable_map_mk_of_separable_map {O L : Type*} [CommRing O] [CommRing L] [Nontrivial L]
    {I : Ideal O} (hI : I.IsMaximal) (ψ : O →+* L) (hψ : ∀ a ∈ I, ψ a = 0)
    {f : Polynomial O} (hf : (f.map ψ).Separable) : (f.map (Ideal.Quotient.mk I)).Separable := by
  letI : Field (O ⧸ I) := Ideal.Quotient.field I
  apply (Polynomial.separable_map (Ideal.Quotient.lift I ψ hψ)).mp
  rwa [Polynomial.map_map, Ideal.Quotient.lift_comp_mk]

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jqN evalAtJ evalAtJ_X ModularPolynomialData jqN_mem modularFunctionFieldFull modularFunctionField_le_full transcendental_jq nonempty_modularPolynomialData ModularPolynomialData.separable_map_ratFunc_of_not_dvd"
p2m_open "ModularCurve"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull jFull_ne_zero mem_chartAlg_iff adjoin_le_chartAlg chartAlgFin chartAlgInf exists_mul_mem_adjoin_jFull_jqN isIntegrallyClosed_chartAlgFin isIntegrallyClosed_chartAlgInf finiteType_chartAlgFin_and_chartAlgInf"
p2m_open "ModularCurve.IgusaScheme"

p2m_open "Polynomial P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.Polynomial IsLocalRing"
open scoped TensorProduct

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)
set_option quotPrecheck false in
local notation "𝔽" => AlgebraicClosure (ZMod ℓ)

def zlToZMod : ℤℓ →+* ZMod ℓ :=
  IsLocalization.lift (M := (Ideal.span {(ℓ : ℤ)}).primeCompl) (S := ℤℓ)
    (g := Int.castRingHom (ZMod ℓ)) (by
      intro s
      apply isUnit_iff_ne_zero.mpr
      intro h
      apply s.2
      show (s : ℤ) ∈ Ideal.span {(ℓ : ℤ)}
      rw [Ideal.mem_span_singleton]
      have h' : ((s : ℤ) : ZMod ℓ) = 0 := h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp h')

theorem zlToZMod_algebraMap (n : ℤ) : zlToZMod ℓ (algebraMap ℤ ℤℓ n) = (n : ZMod ℓ) :=
  IsLocalization.lift_eq _ n

theorem zlToZMod_surjective : Function.Surjective (zlToZMod ℓ) := by
  intro x
  refine ⟨algebraMap ℤ ℤℓ (x.val : ℤ), ?_⟩
  rw [zlToZMod_algebraMap]
  simp

theorem ker_zlToZMod : RingHom.ker (zlToZMod ℓ) = Ideal.span {(ℓ : ℤℓ)} := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective (Ideal.span {(ℓ : ℤ)}).primeCompl x
    dsimp only at hat
    rw [← hat] at hx ⊢
    rw [zlToZMod, IsLocalization.lift_mk'] at hx
    simp only [Units.mul_left_eq_zero, eq_intCast] at hx
    have ha : (ℓ : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a ℓ).mp hx
    obtain ⟨b, rfl⟩ := ha
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
    exact ZMod.natCast_self ℓ

theorem separable_minpoly_map_psi (hℓN : ¬ ℓ ∣ N) :
    ((minpoly (GaussRing N ℓ) (jNFull N)).map (psi N ℓ)).Separable := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hsep : ((PhiO N ℓ data).map (psi N ℓ)).Separable := by
    rw [PhiO_map_psi]
    exact ModularPolynomialData.separable_map_ratFunc_of_not_dvd N data ℓ hℓN
  exact hsep.of_dvd (Polynomial.map_dvd _ (minpoly_dvd_PhiO N ℓ data))

theorem algebraMap_zl_eq_comp (k : Type) [Field k] [CharP k ℓ] [Algebra ℤℓ k] :
    algebraMap ℤℓ k = (ZMod.castHom (dvd_refl ℓ) k).comp (zlToZMod ℓ) := by
  apply IsLocalization.ringHom_ext (Ideal.span {(ℓ : ℤ)}).primeCompl
  exact RingHom.ext_int _ _

theorem isReduced_chartAlgFin_tensor (hℓN : ¬ ℓ ∣ N)
    (k : Type) [Field k] [CharP k ℓ] [Algebra ℤℓ k] :
    IsReduced (k ⊗[ℤℓ] chartAlgFin N ℓ) := by
  haveI : IsIntegrallyClosed (chartAlgFin N ℓ) := isIntegrallyClosed_chartAlgFin N ℓ
  haveI : IsPrincipalIdealRing ℤℓ := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ
  letI : Algebra ℤℓ (ZMod ℓ) := (zlToZMod ℓ).toAlgebra
  letI : Algebra (ZMod ℓ) k := ZMod.algebra k ℓ
  haveI : IsScalarTower ℤℓ (ZMod ℓ) k := IsScalarTower.of_algebraMap_eq' (algebraMap_zl_eq_comp ℓ k)
  have e1 : algebraMap ℤℓ (jRing N ℓ) (ℓ : ℤℓ) = (ℓ : jRing N ℓ) := map_natCast _ _
  have e1' : algebraMap (jRing N ℓ) (GaussRing N ℓ) (algebraMap ℤℓ (jRing N ℓ) ℓ) =
      algebraMap (jRing N ℓ) (GaussRing N ℓ) ℓ := by rw [e1]
  have hpO := irreducible_algebraMap_natCast_gaussRing N ℓ
  rw [← e1'] at hpO
  have hO : ∀ x : GaussRing N ℓ, ∃ s ∉ Ideal.span {algebraMap ℤℓ (jRing N ℓ) ℓ}, ∃ r : jRing N ℓ,
      algebraMap (jRing N ℓ) (GaussRing N ℓ) r = algebraMap (jRing N ℓ) (GaussRing N ℓ) s * x := by
    rw [e1]
    exact exists_mul_mem_of_gaussRing N ℓ
  have h1 : (1 : jRing N ℓ) ∉ Ideal.span {(ℓ : jRing N ℓ)} :=
    (Ideal.ne_top_iff_one _).mp (isPrime_gaussPrime N ℓ).ne_top
  have hαA : ∃ s ∉ Ideal.span {algebraMap ℤℓ (jRing N ℓ) ℓ}, (s : FN) * jNFull N ∈ chartAlgFin N ℓ := by
    rw [e1]
    refine ⟨1, h1, ?_⟩
    simpa using jNFull_mem_chartAlgFin N ℓ
  have hmax : (Ideal.span {algebraMap (jRing N ℓ) (GaussRing N ℓ) (algebraMap ℤℓ (jRing N ℓ) ℓ)}).IsMaximal := by
    rw [e1']
    exact isMaximal_span_algebraMap_ell N ℓ
  have hψ : ∀ a ∈ Ideal.span {algebraMap (jRing N ℓ) (GaussRing N ℓ) (algebraMap ℤℓ (jRing N ℓ) ℓ)},
      psi N ℓ a = 0 := by
    rw [e1']
    exact psi_mem_ker N ℓ

  refine @Subalgebra.isReduced_tensor_of_separable ℤℓ FN (GaussRing N ℓ) (ZMod ℓ) _ _ _ (ℓ : ℤℓ)
    (GaloisRep.irreducible_natCast_ratLocalizedAt ℓ Fact.out) _ _ (jRing N ℓ) (chartAlgFin N ℓ)
    (jRingEquiv N ℓ) (adjoin_le_chartAlg N ℓ _) (fun a => a.2) _ (isIntegrallyClosed_chartAlgFin N ℓ)
    _ _ _ _ _ _ _ hpO hO (jNFull N) (isIntegral_gaussRing_jNFull N ℓ) hαA ?_ ?_
    _ _ (zlToZMod_surjective ℓ) (ker_zlToZMod ℓ) k _ _ _ _
  · haveI := hmax
    letI := Ideal.Quotient.field
      (Ideal.span {algebraMap (jRing N ℓ) (GaussRing N ℓ) (algebraMap ℤℓ (jRing N ℓ) ℓ)})
    apply (Polynomial.separable_map (Ideal.Quotient.lift _ (psi N ℓ) hψ)).mp
    rw [Polynomial.map_map, Ideal.Quotient.lift_comp_mk]
    exact separable_minpoly_map_psi N ℓ hℓN
  · rw [e1']
    exact exists_pow_ell_mul_mem_adjoin_gaussRing N ℓ

theorem isReduced_chartAlgInf_tensor (hℓN : ¬ ℓ ∣ N)
    (k : Type) [Field k] [CharP k ℓ] [Algebra ℤℓ k] :
    IsReduced (k ⊗[ℤℓ] chartAlgInf N ℓ) := by
  haveI : IsIntegrallyClosed (chartAlgInf N ℓ) := isIntegrallyClosed_chartAlgInf N ℓ
  haveI : IsPrincipalIdealRing ℤℓ := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ
  letI : Algebra ℤℓ (ZMod ℓ) := (zlToZMod ℓ).toAlgebra
  letI : Algebra (ZMod ℓ) k := ZMod.algebra k ℓ
  haveI : IsScalarTower ℤℓ (ZMod ℓ) k := IsScalarTower.of_algebraMap_eq' (algebraMap_zl_eq_comp ℓ k)
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have e2 : algebraMap ℤℓ (jInvRing N ℓ) (ℓ : ℤℓ) = (ℓ : jInvRing N ℓ) := map_natCast _ _
  have e : algebraMap (jInvRing N ℓ) (GaussRing N ℓ) (algebraMap ℤℓ (jInvRing N ℓ) (ℓ : ℤℓ)) =
      algebraMap (jRing N ℓ) (GaussRing N ℓ) (ℓ : jRing N ℓ) := by rw [e2, map_natCast, map_natCast]
  have hpO := irreducible_algebraMap_natCast_gaussRing N ℓ
  rw [← e] at hpO
  have hO : ∀ x : GaussRing N ℓ, ∃ s ∉ Ideal.span {algebraMap ℤℓ (jInvRing N ℓ) ℓ}, ∃ r : jInvRing N ℓ,
      algebraMap (jInvRing N ℓ) (GaussRing N ℓ) r = algebraMap (jInvRing N ℓ) (GaussRing N ℓ) s * x := by
    rw [e2]
    exact exists_mul_mem_of_gaussRing_inv N ℓ
  have hαA : ∃ s ∉ Ideal.span {algebraMap ℤℓ (jInvRing N ℓ) ℓ}, (s : FN) * jNFull N ∈ chartAlgInf N ℓ := by
    rw [e2]
    refine ⟨jInvElt N ℓ ^ coeffDegBound N data, jInvElt_pow_notMem N ℓ _, ?_⟩
    simpa [jInvElt] using jInv_pow_mul_jNFull_mem_chartAlgInf N ℓ data
  have hmax : (Ideal.span {algebraMap (jInvRing N ℓ) (GaussRing N ℓ)
      (algebraMap ℤℓ (jInvRing N ℓ) ℓ)}).IsMaximal := by
    rw [e]
    exact isMaximal_span_algebraMap_ell N ℓ
  have hψ : ∀ a ∈ Ideal.span {algebraMap (jInvRing N ℓ) (GaussRing N ℓ) (algebraMap ℤℓ (jInvRing N ℓ) ℓ)},
      psi N ℓ a = 0 := by
    rw [e]
    exact psi_mem_ker N ℓ
  refine @Subalgebra.isReduced_tensor_of_separable ℤℓ FN (GaussRing N ℓ) (ZMod ℓ) _ _ _ (ℓ : ℤℓ)
    (GaloisRep.irreducible_natCast_ratLocalizedAt ℓ Fact.out) _ _ (jInvRing N ℓ) (chartAlgInf N ℓ)
    (jInvRingEquiv N ℓ) (adjoin_le_chartAlg N ℓ _) (fun a => a.2) _ (isIntegrallyClosed_chartAlgInf N ℓ)
    _ _ _ _ _ _ _ hpO hO (jNFull N) (isIntegral_gaussRing_jNFull N ℓ) hαA ?_ ?_
    _ _ (zlToZMod_surjective ℓ) (ker_zlToZMod ℓ) k _ _ _ _
  · haveI := hmax
    letI := Ideal.Quotient.field
      (Ideal.span {algebraMap (jInvRing N ℓ) (GaussRing N ℓ) (algebraMap ℤℓ (jInvRing N ℓ) ℓ)})
    apply (Polynomial.separable_map (Ideal.Quotient.lift _ (psi N ℓ) hψ)).mp
    rw [Polynomial.map_map, Ideal.Quotient.lift_comp_mk]
    exact separable_minpoly_map_psi N ℓ hℓN
  · rw [e]
    exact exists_pow_ell_mul_mem_adjoin_gaussRing N ℓ

end IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"

open scoped TensorProduct in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve _root_.ModularCurve.IgusaScheme _root_.P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (k : Type) [Field k] [CharP k ℓ] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) k] :
    IsReduced (k ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ)) :=
  ModularCurve.IgusaScheme.isReduced_chartAlgFin_tensor N ℓ hℓN k

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor.ModularCurve"

end S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_isReduced_chartAlgFin_tensor (solution)
