-- Prove2me | solution 1 for ModularCurve.JOne.exists_le_inertiaSubgroupIn_finiteIndex_forall_apply_eq_self_of_pow_eq_one_forall_smul_eq_self_of_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9743c79e-52f6-5024-89cf-06aa7a979e88

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_JOne_exists_finiteDimensional_smul_eq_self_of_torsion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JOne_exists_le_inertiaSubgroupIn_finiteIndex_forall_apply_eq_self_of_pow_eq_one_forall_smul_eq_self_of_torsion
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false

theorem solution
    (M q : ℕ) [NeZero M] (hq : 0 < q) (P : ValuationSubring (AlgebraicClosure ℚ)) (m : ℕ) (hm : 0 < m) :
    ∃ I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), I ≤ P.inertiaSubgroupIn ℚ ∧
      (∀ σ ∈ I, ∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ) ∧
      (I.subgroupOf (P.inertiaSubgroupIn ℚ)).FiniteIndex ∧
      ∀ σ ∈ I, ∀ z : ModularCurve.JOne M, (m : ℤ) • z = 0 → σ • z = z := by
  classical
  obtain ⟨L, hLfd, hL⟩ := ModularCurve.JOne.exists_finiteDimensional_smul_eq_self_of_torsion M m hm
  haveI := hLfd

  haveI hG : IsGalois ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (@AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ))
      inferInstance inferInstance
    rfl
  have hSfin : Set.Finite (↑(Polynomial.nthRootsFinset q (1 : AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ)) :=
    Finset.finite_toSet _
  haveI := hSfin.to_subtype
  have hint : ∀ x ∈ (↑(Polynomial.nthRootsFinset q (1 : AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ)),
      IsIntegral ℚ x := by
    intro x hx
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hq] at hx
    refine ⟨Polynomial.X ^ q - Polynomial.C 1, Polynomial.monic_X_pow_sub_C (1 : ℚ) hq.ne', ?_⟩
    simp [hx]
  haveI : FiniteDimensional ℚ
      (IntermediateField.adjoin ℚ (↑(Polynomial.nthRootsFinset q (1 : AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hidx : (L ⊔ IntermediateField.adjoin ℚ
      (↑(Polynomial.nthRootsFinset q (1 : AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))).fixingSubgroup.FiniteIndex := by
    refine ⟨?_⟩
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  refine ⟨P.inertiaSubgroupIn ℚ ⊓ (L ⊔ IntermediateField.adjoin ℚ
      (↑(Polynomial.nthRootsFinset q (1 : AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))).fixingSubgroup,
    inf_le_left, ?_, ?_, ?_⟩
  · intro σ hσ ζ hζ
    have hζS : ζ ∈ (↑(Polynomial.nthRootsFinset q (1 : AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ)) := by
      rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hq]
      exact hζ
    have h1 : ζ ∈ L ⊔ IntermediateField.adjoin ℚ
        (↑(Polynomial.nthRootsFinset q (1 : AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ)) :=
      (le_sup_right : IntermediateField.adjoin ℚ _ ≤ L ⊔ IntermediateField.adjoin ℚ _)
        (IntermediateField.subset_adjoin ℚ _ hζS)
    exact (IntermediateField.mem_fixingSubgroup_iff _ σ).1 (Subgroup.mem_inf.1 hσ).2 ζ h1
  · rw [Subgroup.inf_subgroupOf_left]
    haveI := hidx
    infer_instance
  · intro σ hσ z hz
    exact hL σ (fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ σ).1 (Subgroup.mem_inf.1 hσ).2 x
      ((le_sup_left : L ≤ L ⊔ IntermediateField.adjoin ℚ _) hx)) z hz

end S_ModularCurve_JOne_exists_le_inertiaSubgroupIn_finiteIndex_forall_apply_eq_self_of_pow_eq_one_forall_smul_eq_self_of_torsion
end P2MW
export P2MW.S_ModularCurve_JOne_exists_le_inertiaSubgroupIn_finiteIndex_forall_apply_eq_self_of_pow_eq_one_forall_smul_eq_self_of_torsion (solution)
