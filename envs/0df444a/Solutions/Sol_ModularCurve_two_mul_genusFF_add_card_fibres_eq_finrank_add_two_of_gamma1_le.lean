-- Prove2me | solution 1 for ModularCurve.two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d6bc4896-535c-5a30-85ee-8a1ba31c0d2f

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le
import Theorems.Thm_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open ModularCurve CongruenceSubgroup AlgebraicCurve
open scoped MatrixGroups

open IntermediateField in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) :
    2 * AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) // P.ord y < 0} +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) // 0 < P.ord y} +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) // 0 < P.ord (y - 1728)} =
      Module.finrank
          ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) + 2 := by
  classical

  haveI hKc : CharZero (AlgebraicClosure ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective

  haveI : (Gamma1 M).FiniteIndex := (CongruenceSubgroup.Gamma1_is_congruence M).finiteIndex
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hT1 : ModularGroup.T ∈ Gamma1 M := by
    rw [← ModularCurve.GammaH_bot M]; exact ModularCurve.translation_mem_GammaH M ⊥
  have hT : ModularGroup.T ∈ Γ := hΓ hT1

  obtain ⟨htr, hfin⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      (AlgebraicClosure ℚ) Γ hT y hy
  haveI := hfin

  have hle := ModularCurve.two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le M Γ hΓ y hy
  refine le_antisymm hle ?_

  obtain ⟨S0, hS0mem, hS0sum⟩ :=
    AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed (AlgebraicClosure ℚ) y htr hfin 0
  obtain ⟨S1, hS1mem, hS1sum⟩ :=
    AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed (AlgebraicClosure ℚ) y htr hfin 1728
  obtain ⟨Si, hSimem, hSisum⟩ :=
    AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed (AlgebraicClosure ℚ) y htr hfin
  have h0 : (y - algebraMap (AlgebraicClosure ℚ) _ (0 : AlgebraicClosure ℚ)) = y := by
    rw [map_zero, sub_zero]
  have h1728 : (algebraMap (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (1728 : AlgebraicClosure ℚ)) = (1728 : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ))) := by
    exact map_ofNat _ 1728
  simp only [h0] at hS0mem hS0sum

  have cSi : Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            P.ord y < 0} = Si.card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun P => (hSimem P).symm))]
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  have cS0 : Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            0 < P.ord y} = S0.card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun P => (hS0mem P).symm))]
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  have cS1 : Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            0 < P.ord (y - 1728)} = S1.card := by
    have e : ∀ P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)),
        0 < P.ord (y - 1728) ↔ P ∈ S1 := by
      intro P; rw [hS1mem P, h1728]
    rw [Nat.card_congr (Equiv.subtypeEquivRight e)]
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro P hP0 hP1
    have hy0 : 0 < P.ord y := (hS0mem P).mp hP0
    have hy1 : 0 < P.ord (y - algebraMap (AlgebraicClosure ℚ) _ (1728 : AlgebraicClosure ℚ)) := (hS1mem P).mp hP1
    have hc : P.ord (algebraMap (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
          (1728 : AlgebraicClosure ℚ)) = 0 := AlgebraicCurve.Place.ord_algebraMap P _
    have hc0 : (algebraMap (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
          (1728 : AlgebraicClosure ℚ)) ≠ 0 := by
      rw [map_ne_zero]; norm_num
    have hg0 : y - algebraMap (AlgebraicClosure ℚ) _ (1728 : AlgebraicClosure ℚ) ≠ 0 := by
      intro h; rw [h, AlgebraicCurve.Place.ord_zero] at hy1; exact lt_irrefl _ hy1
    have hlt : P.ord (algebraMap (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
          (1728 : AlgebraicClosure ℚ)) <
        P.ord (y - algebraMap (AlgebraicClosure ℚ) _ (1728 : AlgebraicClosure ℚ)) := by rw [hc]; exact hy1
    have hsum := AlgebraicCurve.Place.ord_add_eq_of_lt P hc0 hg0 hlt
    rw [add_sub_cancel, hc] at hsum
    rw [hsum] at hy0
    exact lt_irrefl _ hy0

  haveI : CharZero ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({y} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  have hsep : Algebra.IsSeparable
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({y} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))))
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField

  have hst := AlgebraicCurve.sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable (AlgebraicClosure ℚ) y htr hfin hsep
    (S0 ∪ S1) (fun P => if P ∈ S0 then 0 else 1728)
    (by
      intro P hP
      rcases Finset.mem_union.mp hP with h | h
      · simp only [h, if_true, map_zero, sub_zero]; exact (hS0mem P).mp h
      · have hn : P ∉ S0 := fun h' => Finset.disjoint_left.mp hdisj h' h
        simp only [hn, if_false]; exact (hS1mem P).mp h)
    Si (fun P hP => (hSimem P).mp hP)

  have eA : ∀ P ∈ S0, (P.ord (y - algebraMap (AlgebraicClosure ℚ) _
        ((fun P => if P ∈ S0 then (0 : AlgebraicClosure ℚ) else 1728) P)) - 1) = P.ord y - 1 := by
    intro P hP
    simp only [hP, if_true, map_zero, sub_zero]
  have eB : ∀ P ∈ S1, (P.ord (y - algebraMap (AlgebraicClosure ℚ) _
        ((fun P => if P ∈ S0 then (0 : AlgebraicClosure ℚ) else 1728) P)) - 1) =
      P.ord (y - algebraMap (AlgebraicClosure ℚ) _ (1728 : AlgebraicClosure ℚ)) - 1 := by
    intro P hP
    have hn : P ∉ S0 := fun h' => Finset.disjoint_left.mp hdisj h' hP
    simp only [hn, if_false]
  rw [Finset.sum_union hdisj, Finset.sum_congr rfl eA, Finset.sum_congr rfl eB] at hst
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hst
  rw [hS0sum, hS1sum, hSisum] at hst

  rw [cSi, cS0, cS1]
  omega

end S_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
end P2MW
export P2MW.S_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le (solution)
