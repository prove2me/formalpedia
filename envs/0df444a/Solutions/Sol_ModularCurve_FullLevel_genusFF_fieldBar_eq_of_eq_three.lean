-- Prove2me | solution 1 for ModularCurve.FullLevel.genusFF_fieldBar_eq_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/b6737a86-2259-579a-9134-7ab40184f953

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_Matrix_SpecialLinearGroup_three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq
import Theorems.Thm_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq
import Theorems.Thm_ModularCurve_FullLevel_two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix"
p2m_attr_erase "simp" "ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.LevelN.coe_jGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one"

set_option autoImplicit false

p2m_open "AlgebraicCurve~genus ModularCurve P2MW.S_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three.ModularCurve.FullLevel CongruenceSubgroup"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset dedekindPsi coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange cuspCount jqModC map_jqModC two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le jqModC_mem_intFormRatiosC finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index FullLevel.two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq FullLevel.two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "dvd_sq_mul levelH mem_levelH_iff fieldBar two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq"
namespace GenusBar3
p2m_open "ModularCurve.FullLevel ModularCurve"

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

abbrev Γ : Subgroup SL(2, ℤ) := CohCarrier.GammaH (q ^ 2 * M') (levelH q M')

theorem gamma1_le : CongruenceSubgroup.Gamma1 (q ^ 2 * M') ≤ Γ q M' := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨ha, hd, hc⟩ := hA
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨(CongruenceSubgroup.Gamma0_mem).mpr hc, ?_⟩
  rw [mem_levelH_iff]
  have hval : (CohCarrier.gamma0Units (q ^ 2 * M') ⟨A, (CongruenceSubgroup.Gamma0_mem).mpr hc⟩ : ZMod (q ^ 2 * M')) = 1 := by
    rw [CohCarrier.val_gamma0Units]
    exact hd
  have h1 : CohCarrier.gamma0Units (q ^ 2 * M') ⟨A, (CongruenceSubgroup.Gamma0_mem).mpr hc⟩ = 1 := Units.ext hval
  rw [h1, map_one]

theorem mem_gamma1_q_of_mem {A : SL(2, ℤ)} (hA : A ∈ Γ q M') : A ∈ CongruenceSubgroup.Gamma1 q := by
  rw [CohCarrier.mem_GammaH_iff] at hA
  obtain ⟨h0, hH⟩ := hA
  rw [mem_levelH_iff] at hH

  have hd : ((A 1 1 : ℤ) : ZMod q) = 1 := by
    have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hH
    simpa [ZMod.unitsMap, CohCarrier.val_gamma0Units, CongruenceSubgroup.Gamma0Map, ZMod.castHom_apply,
      ZMod.cast_intCast (dvd_sq_mul q M')] using this

  have hc : ((A 1 0 : ℤ) : ZMod q) = 0 := by
    have hc' : ((A 1 0 : ℤ) : ZMod (q ^ 2 * M')) = 0 := (CongruenceSubgroup.Gamma0_mem).mp h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc' ⊢
    exact (Int.natCast_dvd_natCast.mpr (dvd_sq_mul q M')).trans hc'

  have hdet := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two] at hdet
  have ha : ((A 0 0 : ℤ) : ZMod q) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod q)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hd, hc, mul_one, mul_zero, sub_zero] at this
    exact this
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨ha, hd, hc⟩

set_option linter.unusedSectionVars false

theorem sq_trace_lt_four_or_eq_of_smul_eq (γ : SL(2, ℤ)) (τ : UpperHalfPlane) (hτ : γ • τ = τ) :
    (γ 0 0 + γ 1 1) ^ 2 < 4 ∨ γ = 1 ∨ γ = -1 := by

  set g : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hg
  have hgij : ∀ i j, g i j = ((γ i j : ℤ) : ℝ) := fun i j => by
    simp [hg, Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL]
  have hfix : g • τ = τ := hτ
  have hdet : g.val.det = 1 := by
    rw [Matrix.det_fin_two]
    simp only [hgij]
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hdetpos : 0 < g.val.det := by rw [hdet]; exact one_pos
  by_cases hgc : g ∈ Subgroup.center (GL (Fin 2) ℝ)
  ·
    right
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hgc
    obtain ⟨r, hr⟩ := hgc
    have h00 : ((γ 0 0 : ℤ) : ℝ) = r := by rw [← hgij]; simp [← hr]
    have h11 : ((γ 1 1 : ℤ) : ℝ) = r := by rw [← hgij]; simp [← hr]
    have h01 : ((γ 0 1 : ℤ) : ℝ) = 0 := by rw [← hgij]; simp [← hr]
    have h10 : ((γ 1 0 : ℤ) : ℝ) = 0 := by rw [← hgij]; simp [← hr]
    have e01 : γ 0 1 = 0 := by exact_mod_cast h01
    have e10 : γ 1 0 = 0 := by exact_mod_cast h10
    have e0011 : γ 0 0 = γ 1 1 := by exact_mod_cast h00.trans h11.symm
    have hd := γ.2
    rw [Matrix.det_fin_two, e01, e10, ← e0011, mul_zero, sub_zero] at hd
    have hsq : γ 0 0 = 1 ∨ γ 0 0 = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hsq with h1 | h1
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, e01, e10, ← e0011]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, e01, e10, ← e0011]
  · left
    have hell := UpperHalfPlane.isElliptic_of_exists_smul_eq_self hdetpos hgc ⟨τ, hfix⟩
    have h' : g.val.discr < 0 := hell
    rw [Matrix.discr_fin_two, Matrix.trace_fin_two, hdet] at h'
    have h'' : (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 < 4 := by
      push_cast
      rw [← hgij 0 0, ← hgij 1 1]
      linarith
    exact_mod_cast h''

theorem eq_one_or_eq_neg_one_of_nine_dvd_of_smul_eq (γ : SL(2, ℤ)) (h9 : (9 : ℤ) ∣ γ 1 0)
    (τ : UpperHalfPlane) (hτ : γ • τ = τ) : γ = 1 ∨ γ = -1 := by
  rcases sq_trace_lt_four_or_eq_of_smul_eq γ τ hτ with hlt | h | h
  · exfalso
    set t : ℤ := γ 0 0 + γ 1 1 with ht
    have ht1 : -1 ≤ t ∧ t ≤ 1 := by constructor <;> nlinarith
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet

    have hd : γ 1 1 = t - γ 0 0 := by omega
    obtain ⟨k, hk⟩ := h9
    have hmod : ((γ 0 0 : ℤ) : ZMod 9) * ((t : ℤ) - (γ 0 0 : ℤ)) = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod 9)) hdet
      rw [hd, hk] at this
      push_cast at this
      have h90 : (9 : ZMod 9) = 0 := by decide
      rw [h90, zero_mul, mul_zero, sub_zero] at this
      exact this
    have hcases : t = -1 ∨ t = 0 ∨ t = 1 := by omega
    have key1 : ∀ x : ZMod 9, x * (-1 - x) ≠ 1 := by decide
    have key2 : ∀ x : ZMod 9, x * (0 - x) ≠ 1 := by decide
    have key3 : ∀ x : ZMod 9, x * (1 - x) ≠ 1 := by decide
    rcases hcases with ht' | ht' | ht'
    · rw [ht'] at hmod; push_cast at hmod; exact key1 _ hmod
    · rw [ht'] at hmod; push_cast at hmod; exact key2 _ hmod
    · rw [ht'] at hmod; push_cast at hmod; exact key3 _ hmod
  · exact Or.inl h
  · exact Or.inr h

theorem hfree (hq3 : q = 3) :
    ∀ γ : SL(2, ℤ), (γ ∈ Γ q M' ∨ -γ ∈ Γ q M') → ∀ τ : UpperHalfPlane, γ • τ = τ → γ = 1 ∨ γ = -1 := by
  intro γ hγ τ hτ
  refine eq_one_or_eq_neg_one_of_nine_dvd_of_smul_eq γ ?_ τ hτ

  have h9c : ∀ A : SL(2, ℤ), A ∈ Γ q M' → (9 : ℤ) ∣ A 1 0 := by
    intro A hA
    rw [CohCarrier.mem_GammaH_iff] at hA
    have hc' : ((A 1 0 : ℤ) : ZMod (q ^ 2 * M')) = 0 := (CongruenceSubgroup.Gamma0_mem).mp hA.1
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc'
    refine dvd_trans ?_ hc'
    subst hq3
    exact ⟨(M' : ℤ), by push_cast; ring⟩
  rcases hγ with h | h
  · exact h9c γ h
  · have := h9c (-γ) h
    rwa [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, dvd_neg] at this

noncomputable def yj : ↥(ModularCurve.laurentBaseChange ℚ̄ (ModularCurve.qExpFunctionFieldC ℚ (Γ q M'))) :=
  ⟨coeffEmb ℚ̄ (jqModC ℚ),
    coeffEmb_mem_laurentBaseChange ℚ̄ (intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ (Γ q M')))⟩

theorem yj_coe :
    ((yj q M' : ↥(ModularCurve.laurentBaseChange ℚ̄ (ModularCurve.qExpFunctionFieldC ℚ (Γ q M')))) :
      LaurentSeries ℚ̄) = jqModC ℚ̄ := by
  show coeffEmb ℚ̄ (jqModC ℚ) = _
  exact map_jqModC _

scoped instance finiteIndex_Γ : (Γ q M').FiniteIndex := by
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  haveI : (CongruenceSubgroup.Gamma1 (q ^ 2 * M')).FiniteIndex := inferInstance
  exact Subgroup.finiteIndex_of_le (gamma1_le q M')

theorem main (hq3 : q = 3) (hqM' : ¬ q ∣ M') :
    (AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') : ℚ) =
      1 + (q : ℚ) * ((q : ℚ) ^ 2 - 1) * dedekindPsi M' / 24 -
        ((q : ℚ) ^ 2 - 1) * ((∑ d ∈ M'.divisors, Nat.totient (Nat.gcd d (M' / d)) : ℕ) : ℚ) / 4 := by
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩

  change (AlgebraicCurve.genusFF ℚ̄
      ↥(ModularCurve.laurentBaseChange ℚ̄ (ModularCurve.qExpFunctionFieldC ℚ (Γ q M'))) : ℚ) = _
  have hfull := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
    ℚ̄ (q ^ 2 * M') (levelH q M') (yj q M') (yj_coe q M')
  have hfid := ModularCurve.two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
    (q ^ 2 * M') (Γ q M') (gamma1_le q M') (yj q M') (yj_coe q M')
  rw [hfull] at hfid
  obtain ⟨hZ0, hZ1, hP⟩ := ModularCurve.natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
    (q ^ 2 * M') (Γ q M') (gamma1_le q M') (yj q M') (yj_coe q M') hfull
  obtain ⟨h3, h2⟩ :=
    Matrix.SpecialLinearGroup.three_mul_natCard_doubleCoset_eq_index_and_two_mul_of_forall_smul_eq
      (Γ q M') (hfree q M' hq3)
  have hidx := ModularCurve.FullLevel.two_mul_index_gammaH_levelH_sup_zpowers_neg_one_eq q (by omega) M' hqM'
  have hdc := ModularCurve.FullLevel.two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq q (by omega) M' hqM'
  unfold cuspCount at hdc

  have hq1 : ((q ^ 2 - 1 : ℕ) : ℚ) = (q : ℚ) ^ 2 - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (Fact.out : q.Prime).pos), Nat.cast_pow, Nat.cast_one]
  have e1 := congrArg (fun n : ℕ => (n : ℚ)) hfid
  have e2 := congrArg (fun n : ℕ => (n : ℚ)) hZ0
  have e3 := congrArg (fun n : ℕ => (n : ℚ)) hZ1
  have e4 := congrArg (fun n : ℕ => (n : ℚ)) hP
  have e5 := congrArg (fun n : ℕ => (n : ℚ)) h3
  have e6 := congrArg (fun n : ℕ => (n : ℚ)) h2
  have e7 := congrArg (fun n : ℕ => (n : ℚ)) hidx
  have e8 := congrArg (fun n : ℕ => (n : ℚ)) hdc
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hq1] at e1 e2 e3 e4 e5 e6 e7 e8
  linear_combination (1 / 2 : ℚ) * e1 - (1 / 2 : ℚ) * e2 - (1 / 2 : ℚ) * e3 - (1 / 2 : ℚ) * e4
    - (1 / 6 : ℚ) * e5 - (1 / 4 : ℚ) * e6 + (1 / 24 : ℚ) * e7 - (1 / 4 : ℚ) * e8

end ModularCurve.FullLevel.GenusBar3
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three.ModularCurve P2MW.S_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three.ModularCurve.FullLevel.GenusBar3"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three.ModularCurve P2MW.S_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three.ModularCurve"

open ModularCurve.FullLevel.GenusBar3 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    (AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') : ℚ) =
      1 + (q : ℚ) * ((q : ℚ) ^ 2 - 1) * dedekindPsi M' / 24 -
        ((q : ℚ) ^ 2 - 1) * ((∑ d ∈ M'.divisors, Nat.totient (Nat.gcd d (M' / d)) : ℕ) : ℚ) / 4 :=
  ModularCurve.FullLevel.GenusBar3.main q M' hq3 hqM'

end S_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three (solution)
