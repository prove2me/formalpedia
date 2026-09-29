-- Prove2me | solution 1 for ModularCurve.xHFunctionFieldBar_div_sup_adjoin_qExpand_eq_xHFunctionFieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/74e62104-1d10-54bf-9d3c-3846e6b38423

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Theorems.Thm_ModularCurve_laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_eq_laurentBaseChange_xHTopFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_xHFunctionFieldBar_div_sup_adjoin_qExpand_eq_xHFunctionFieldBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem gammaH_div_inf_gamma0_eq_gammaH (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 M = CohCarrier.GammaH M H := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  apply le_antisymm
  · rintro A ⟨hA', hA0⟩
    obtain ⟨hA0', hu'⟩ := CohCarrier.mem_GammaH_iff.mp hA'
    rw [mem_infSubgroup_iff] at hu'
    obtain ⟨d, hdH, hd⟩ := hu'
    refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩

    set u : (ZMod M)ˣ := CohCarrier.gamma0Units M ⟨A, hA0⟩ with hu
    have hred : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d := by
      rw [hd]
      ext
      rw [ZMod.unitsMap_def]
      show (ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p))) ((u : (ZMod M)ˣ) : ZMod M) = _
      rw [hu, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
      simp [CongruenceSubgroup.Gamma0Map]
    have hker : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (u * d⁻¹) = 1 := by
      rw [map_mul, map_inv, hred, mul_inv_cancel]
    have h := H.mul_mem (hHp _ hker) hdH
    rwa [inv_mul_cancel_right] at h
  · intro A hA
    exact ⟨ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM hA, CohCarrier.GammaH_le_Gamma0 H hA⟩

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ⊔
        IntermediateField.adjoin (AlgebraicClosure ℚ)
          (⇑(qExpand (AlgebraicClosure ℚ) p) '' (xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) :
            Set (LaurentSeries (AlgebraicClosure ℚ)))) =
      xHFunctionFieldBar M H := by
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (M / p) := neZero_div p M hpM
  have htop := ModularCurve.laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_eq_laurentBaseChange_xHTopFunctionFieldC
    (AlgebraicClosure ℚ) (M / p) p (infSubgroup p M H hpM)

  have hΓ : CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * p) = CohCarrier.GammaH M H := by
    rw [Nat.div_mul_cancel hpM]; exact gammaH_div_inf_gamma0_eq_gammaH p M H hpM hHp
  have hF : xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p) = xHFunctionField M H := by
    show qExpFunctionFieldC ℚ _ = qExpFunctionFieldC ℚ _
    rw [hΓ]
  rw [hF] at htop
  exact htop

end S_ModularCurve_xHFunctionFieldBar_div_sup_adjoin_qExpand_eq_xHFunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_xHFunctionFieldBar_div_sup_adjoin_qExpand_eq_xHFunctionFieldBar (solution)
