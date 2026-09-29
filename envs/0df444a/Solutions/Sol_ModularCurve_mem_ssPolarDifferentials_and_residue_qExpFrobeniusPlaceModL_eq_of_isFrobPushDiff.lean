-- Prove2me | solution 1 for ModularCurve.mem_ssPolarDifferentials_and_residue_qExpFrobeniusPlaceModL_eq_of_isFrobPushDiff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/2d8bf309-f2c0-5293-8812-b1d8592c6fbc

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Theorems.Thm_ModularCurve_hasSimpleResidue_qExpFrobeniusPlaceModL_of_isFrobPushDiff
import Theorems.Thm_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Theorems.Thm_ModularCurve_essFiniteType_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_ssPolarDifferentials_and_residue_qExpFrobeniusPlaceModL_eq_of_isFrobPushDiff
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.baseAut_x1ArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

open scoped MatrixGroups
open AlgebraicCurve

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

    (res : ↥(ModularCurve.ssPolarDifferentials K Γ p) →ₗ[K]
      (AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ) → K))
    (hres : ∀ (ω : ↥(ModularCurve.ssPolarDifferentials K Γ p))
      (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)),
      v ∈ ModularCurve.ssPlacesQExp K Γ p →
        v.HasSimpleResidue (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) (res ω v))
    (hres0 : ∀ (ω : ↥(ModularCurve.ssPolarDifferentials K Γ p))
      (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)),
      v ∉ ModularCurve.ssPlacesQExp K Γ p → res ω v = 0)
    (C : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])
    (hC : ModularCurve.IsFrobPushDiff K Γ p C) :
    (∀ ω : ↥(ModularCurve.ssPolarDifferentials K Γ p),
        C (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) ∈ ModularCurve.ssPolarDifferentials K Γ p) ∧
    (∀ (ω ω' : ↥(ModularCurve.ssPolarDifferentials K Γ p)),
        (ω' : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) = C (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) →
        ∀ v ∈ ModularCurve.ssPlacesQExp K Γ p,
          res ω' (ModularCurve.qExpFrobeniusPlaceModL K Γ p v) = res ω v) := by
  classical
  haveI : Algebra.EssFiniteType K ↥(ModularCurve.qExpFunctionFieldC K Γ) := ModularCurve.essFiniteType_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI : AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K Γ) := ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI : AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(ModularCurve.qExpFunctionFieldC K Γ)) := AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  have hkey := fun (ω : ↥(ModularCurve.ssPolarDifferentials K Γ p)) =>
    ModularCurve.hasSimpleResidue_qExpFrobeniusPlaceModL_of_isFrobPushDiff K p Γ hT C hC (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) ω.2
  have hSS := ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq K p Γ
  refine ⟨fun ω => (hkey ω).1, ?_⟩
  intro ω ω' hω' v hv
  have hΦv : ModularCurve.qExpFrobeniusPlaceModL K Γ p v ∈ ModularCurve.ssPlacesQExp K Γ p := by
    rw [← hSS]
    exact ⟨v, hv, rfl⟩
  have h1 : AlgebraicCurve.Place.HasSimpleResidue (ModularCurve.qExpFrobeniusPlaceModL K Γ p v)
      (ω' : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) (res ω v) := by
    rw [hω']
    exact (hkey ω).2 v hv (res ω v) (hres ω v hv)
  have h2 : AlgebraicCurve.Place.HasSimpleResidue (ModularCurve.qExpFrobeniusPlaceModL K Γ p v)
      (ω' : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) (res ω' (ModularCurve.qExpFrobeniusPlaceModL K Γ p v)) :=
    hres ω' _ hΦv
  obtain ⟨a, -, huniq⟩ := AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt
    (ModularCurve.qExpFrobeniusPlaceModL K Γ p v) (ω' : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) h2.hasSimplePoleAt
  exact (huniq _ h2).trans (huniq _ h1).symm

end S_ModularCurve_mem_ssPolarDifferentials_and_residue_qExpFrobeniusPlaceModL_eq_of_isFrobPushDiff
end P2MW
export P2MW.S_ModularCurve_mem_ssPolarDifferentials_and_residue_qExpFrobeniusPlaceModL_eq_of_isFrobPushDiff (solution)
