-- Prove2me | solution 1 for ModularCurve.hasSimpleResidue_qExpFrobeniusPlaceModL_of_isFrobPushDiff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0be3c053-ad63-53ff-8015-ef9d0c7cf8ad

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional
import Theorems.Thm_ModularCurve_exists_frobeniusSemilinear_transport_kaehler_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartierLaws
import Theorems.Thm_AlgebraicCurve_cartierOperator_existsUnique
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_hasSimpleResidue_qExpFrobeniusPlaceModL_of_isFrobPushDiff
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.baseAut_x1ArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct MatrixGroups

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (C : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])
    (hC : ModularCurve.IsFrobPushDiff K Γ p C)
    (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K]) (hω : ω ∈ ModularCurve.ssPolarDifferentials K Γ p) :
    C ω ∈ ModularCurve.ssPolarDifferentials K Γ p ∧
      ∀ v ∈ ModularCurve.ssPlacesQExp K Γ p, ∀ r : K,
        AlgebraicCurve.Place.HasSimpleResidue v ω r →
          AlgebraicCurve.Place.HasSimpleResidue (ModularCurve.qExpFrobeniusPlaceModL K Γ p v) (C ω) r := by
  classical
  obtain ⟨x, -, htr, hfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI : AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K Γ) := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  haveI := hfd
  obtain ⟨𝒞, ⟨h1, h2, h3⟩, -⟩ := AlgebraicCurve.cartierOperator_existsUnique (K := K) (F := ↥(ModularCurve.qExpFunctionFieldC K Γ)) p x
  obtain ⟨σΩ, -, hσΘ, hσpl⟩ := ModularCurve.exists_frobeniusSemilinear_transport_kaehler_qExpFunctionFieldC K p Γ hT
  have hCpl := fun v ω' => AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional
    (K := K) (F := ↥(ModularCurve.qExpFunctionFieldC K Γ)) p x 𝒞 h1 h2 h3 v ω'
  have hQ := fun ω' n => ModularCurve.coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartierLaws (K := K) p (ModularCurve.qExpFunctionFieldC K Γ) x 𝒞 h1 h2 h3 ω' n
  have hinj := ModularCurve.diffQExp_qExpFunctionFieldC_injective K Γ hT

  have hCeq : ∀ ω' : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K], C ω' = σΩ (𝒞 ω') := by
    intro ω'
    apply hinj
    ext n
    rw [hC ω', ModularCurve.coeff_qDecimate, hσΘ, ← ModularCurve.qExpansionDiffAlong_val_eq_diffQExp,
      ← ModularCurve.qExpansionDiffAlong_val_eq_diffQExp, hQ, mul_comm]

  have hbij := ModularCurve.qExpFrobeniusPlaceModL_bijective K p Γ
  have himg := ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq K p Γ
  have hss : ∀ v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ),
      v ∈ ModularCurve.ssPlacesQExp K Γ p ↔ ModularCurve.qExpFrobeniusPlaceModL K Γ p v ∈ ModularCurve.ssPlacesQExp K Γ p := by
    intro v
    constructor
    · intro hv
      rw [← himg]
      exact ⟨v, hv, rfl⟩
    · intro hv
      rw [← himg] at hv
      obtain ⟨v', hv', he⟩ := hv
      rwa [← hbij.1 he]
  refine ⟨?_, ?_⟩
  · rw [ModularCurve.mem_ssPolarDifferentials_iff] at hω ⊢
    intro w
    rw [hCeq]
    obtain ⟨v₀, rfl⟩ := hbij.2 w
    constructor
    · intro hw
      have hv₀ : v₀ ∉ ModularCurve.ssPlacesQExp K Γ p := fun h => hw ((hss v₀).1 h)
      exact (hσpl v₀ (𝒞 ω)).1 ((hCpl v₀ ω).1 ((hω v₀).1 hv₀))
    · intro hw
      have hv₀ : v₀ ∈ ModularCurve.ssPlacesQExp K Γ p := (hss v₀).2 hw
      exact (hσpl v₀ (𝒞 ω)).2.1 ((hCpl v₀ ω).2.1 ((hω v₀).2 hv₀))
  · intro v hv r hr
    obtain ⟨s, hs, hres⟩ := (hCpl v ω).2.2 r hr
    have h := (hσpl v (𝒞 ω)).2.2 s hres
    rw [hCeq, ← hs]
    exact h

end S_ModularCurve_hasSimpleResidue_qExpFrobeniusPlaceModL_of_isFrobPushDiff
end P2MW
export P2MW.S_ModularCurve_hasSimpleResidue_qExpFrobeniusPlaceModL_of_isFrobPushDiff (solution)
