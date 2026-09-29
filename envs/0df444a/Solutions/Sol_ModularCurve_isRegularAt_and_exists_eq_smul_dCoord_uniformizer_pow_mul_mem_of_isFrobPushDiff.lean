-- Prove2me | solution 1 for ModularCurve.isRegularAt_and_exists_eq_smul_dCoord_uniformizer_pow_mul_mem_of_isFrobPushDiff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ab001947-8411-5a54-a2fb-b6d7a8998c92

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_exists_eq_smul_dCoord_and_uniformizer_pow_mul_mem_of_cartierLaws
import Theorems.Thm_ModularCurve_exists_frobeniusSemilinear_transport_kaehler_poleOrder_qExpFunctionFieldC
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

namespace P2MW.S_ModularCurve_isRegularAt_and_exists_eq_smul_dCoord_uniformizer_pow_mul_mem_of_isFrobPushDiff
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
    (n : ℕ) (ω : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])
    (hreg : ∀ v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ),
      v ∉ ModularCurve.ssPlacesQExp K Γ p → v.IsRegularAt ω)
    (hpole : ∀ v ∈ ModularCurve.ssPlacesQExp K Γ p, ∃ f : ↥(ModularCurve.qExpFunctionFieldC K Γ),
      ω = f • v.dCoord ∧ v.uniformizer ^ n * f ∈ v.toValuationSubring) :
    (∀ v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ),
        v ∉ ModularCurve.ssPlacesQExp K Γ p → v.IsRegularAt (C ω)) ∧
      (∀ v ∈ ModularCurve.ssPlacesQExp K Γ p, ∃ g : ↥(ModularCurve.qExpFunctionFieldC K Γ),
        C ω = g • v.dCoord ∧ v.uniformizer ^ ((n + p - 1) / p) * g ∈ v.toValuationSubring) := by
  classical

  obtain ⟨x, -, htr, hfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI : AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  haveI := hfd

  obtain ⟨𝒞, ⟨h1, h2, h3⟩, -⟩ := AlgebraicCurve.cartierOperator_existsUnique (K := K) (F := ↥(ModularCurve.qExpFunctionFieldC K Γ)) p x
  obtain ⟨σΩ, -, hσΘ, hσpl⟩ := ModularCurve.exists_frobeniusSemilinear_transport_kaehler_poleOrder_qExpFunctionFieldC K p Γ hT
  have hCpl := fun v ω' => AlgebraicCurve.Place.exists_eq_smul_dCoord_and_uniformizer_pow_mul_mem_of_cartierLaws
    (K := K) (F := ↥(ModularCurve.qExpFunctionFieldC K Γ)) p x 𝒞 h1 h2 h3 v ω'
  have hQ := fun ω' m => ModularCurve.coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartierLaws (K := K) p
    (ModularCurve.qExpFunctionFieldC K Γ) x 𝒞 h1 h2 h3 ω' m
  have hinj := ModularCurve.diffQExp_qExpFunctionFieldC_injective K Γ hT

  have hCeq : ∀ ω' : Ω[↥(ModularCurve.qExpFunctionFieldC K Γ)⁄K], C ω' = σΩ (𝒞 ω') := by
    intro ω'
    apply hinj
    ext m
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

  have key : ∀ (v₀ : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)) (m : ℕ)
      (f : ↥(ModularCurve.qExpFunctionFieldC K Γ)), ω = f • v₀.dCoord → v₀.uniformizer ^ m * f ∈ v₀.toValuationSubring →
      ∃ g : ↥(ModularCurve.qExpFunctionFieldC K Γ),
        C ω = g • (ModularCurve.qExpFrobeniusPlaceModL K Γ p v₀).dCoord ∧
          (ModularCurve.qExpFrobeniusPlaceModL K Γ p v₀).uniformizer ^ ((m + p - 1) / p) * g ∈
            (ModularCurve.qExpFrobeniusPlaceModL K Γ p v₀).toValuationSubring := by
    intro v₀ m f hf hm
    obtain ⟨g₁, hg₁, hm₁⟩ := hCpl v₀ ω m f hf hm
    obtain ⟨g₂, hg₂, hm₂⟩ := hσpl v₀ (𝒞 ω) ((m + p - 1) / p) g₁ hg₁ hm₁
    exact ⟨g₂, by rw [hCeq, hg₂], hm₂⟩
  refine ⟨?_, ?_⟩
  ·
    intro w hw
    obtain ⟨v₀, rfl⟩ := hbij.2 w
    have hv₀ : v₀ ∉ ModularCurve.ssPlacesQExp K Γ p := fun h => hw ((hss v₀).1 h)
    obtain ⟨f, hf, hωf⟩ := hreg v₀ hv₀
    obtain ⟨g, hg, hgm⟩ := key v₀ 0 f hωf (by rw [pow_zero, one_mul]; exact hf)
    refine ⟨g, ?_, hg⟩
    have h0 : (0 + p - 1) / p = 0 := Nat.div_eq_of_lt (by have := (Fact.out : p.Prime).one_lt; omega)
    rw [h0, pow_zero, one_mul] at hgm
    exact hgm
  ·
    intro w hw
    obtain ⟨v₀, rfl⟩ := hbij.2 w
    have hv₀ : v₀ ∈ ModularCurve.ssPlacesQExp K Γ p := (hss v₀).2 hw
    obtain ⟨f, hωf, hf⟩ := hpole v₀ hv₀
    exact key v₀ n f hωf hf

end S_ModularCurve_isRegularAt_and_exists_eq_smul_dCoord_uniformizer_pow_mul_mem_of_isFrobPushDiff
end P2MW
export P2MW.S_ModularCurve_isRegularAt_and_exists_eq_smul_dCoord_uniformizer_pow_mul_mem_of_isFrobPushDiff (solution)
