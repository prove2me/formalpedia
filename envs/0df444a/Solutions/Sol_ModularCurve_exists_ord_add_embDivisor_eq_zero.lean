-- Prove2me | solution 1 for ModularCurve.exists_ord_add_embDivisor_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/34283c4d-951a-5365-85d6-b39c39eb6910

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Theorems.Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ord_add_embDivisor_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.jqNModC_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace BpfSol

end BpfSol

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ i : Fin r, w.ord (s i) + embDivisor N w = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hne : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hmem : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := fun i =>
    hs.2 ▸ Submodule.subset_span ⟨i, rfl⟩

  have hge1 : ∀ i, 1 ≤ w.ord (s i) + embDivisor N w := by
    intro i
    rcases (mem_riemannRochSpace_iff.mp (hmem i)) w with h0 | hle
    · exact absurd h0 (hne i)
    · have h0 : 0 ≤ w.ord (s i) + embDivisor N w := by linarith
      rcases lt_or_eq_of_le h0 with hlt | heq
      · exact hlt
      · exact absurd heq.symm (hcon i)

  have hmem' : ∀ i, s i ∈ riemannRochSpace (embDivisor N - Finsupp.single w (1 : ℤ)) := by
    intro i
    rw [mem_riemannRochSpace_iff]
    intro v
    rcases (mem_riemannRochSpace_iff.mp (hmem i)) v with h0 | hle
    · exact Or.inl h0
    · refine Or.inr ?_
      rcases eq_or_ne v w with hvw | hvw
      · subst hvw
        have := hge1 i
        simp only [Finsupp.sub_apply, Finsupp.single_eq_same]
        linarith
      · simp only [Finsupp.sub_apply, Finsupp.single_eq_of_ne hvw, sub_zero]
        exact hle
  have hspan : riemannRochSpace (embDivisor N) ≤
      riemannRochSpace (embDivisor N - Finsupp.single w (1 : ℤ)) := by
    rw [← hs.2]
    exact Submodule.span_le.mpr (by rintro x ⟨i, rfl⟩; exact hmem' i)
  by_cases hw : w = cuspInftyBar N
  ·
    subst hw
    haveI hco : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      ModularCurve.isCurveOver_modularFunctionFieldBar N
    haveI hcd : HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) :=
      ModularCurve.hasCanonicalDivisor_modularFunctionFieldBar N
    haveI hess : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      ModularCurve.essFiniteType_modularFunctionFieldBar N
    haveI hdcg : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.DCoordGenerates :=
      AlgebraicCurve.dCoordGenerates_of_isCurveOver
    obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])

    have hmono : riemannRochSpace (embDivisor N - Finsupp.single (cuspInftyBar N) (1 : ℤ)) ≤
        riemannRochSpace (embDivisor N) := by
      intro f hf
      rw [mem_riemannRochSpace_iff] at hf ⊢
      intro v
      rcases hf v with h0 | hle
      · exact Or.inl h0
      · refine Or.inr ?_
        rcases eq_or_ne v (cuspInftyBar N) with hvw | hvw
        · subst hvw
          simp only [Finsupp.sub_apply, Finsupp.single_eq_same] at hle
          linarith
        · simp only [Finsupp.sub_apply, Finsupp.single_eq_of_ne hvw, sub_zero] at hle
          exact hle
    have heqL : riemannRochSpace (embDivisor N) =
        riemannRochSpace (embDivisor N - Finsupp.single (cuspInftyBar N) (1 : ℤ)) :=
      le_antisymm hspan hmono

    have hdegE : Divisor.degree (embDivisor N) = (embDegree N : ℤ) := by
      simp only [embDivisor]
      rw [map_zsmul, Divisor.degree_single, ModularCurve.deg_eq_one_modularFunctionFieldBar N, Nat.cast_one, mul_one,
        smul_eq_mul, mul_one]
    have hdegE' : Divisor.degree (embDivisor N - Finsupp.single (cuspInftyBar N) (1 : ℤ))
        = (embDegree N : ℤ) - 1 := by
      rw [map_sub, hdegE, Divisor.degree_single, ModularCurve.deg_eq_one_modularFunctionFieldBar N, Nat.cast_one, mul_one]

    have hg : AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)
        = genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      ModularCurve.genus_eq_genusFF_modularFunctionFieldBar N
    have hdval : (embDegree N : ℤ)
        = 2 * (AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) + 1 := by
      rw [embDegree, hg]
      push_cast
      ring

    have hcanE : Divisor.degree (canonicalDivisorOf hω - embDivisor N) < 0 := by
      rw [map_sub, ModularCurve.degree_canonicalDivisorOf_modularFunctionFieldBar N hω, hdegE]
      linarith [hdval]
    have hcanE' : Divisor.degree (canonicalDivisorOf hω
        - (embDivisor N - Finsupp.single (cuspInftyBar N) (1 : ℤ))) < 0 := by
      rw [map_sub, ModularCurve.degree_canonicalDivisorOf_modularFunctionFieldBar N hω, hdegE']
      linarith [hdval]

    have hRR := ModularCurve.functionFieldRiemannRoch_modularFunctionFieldBar N hω (embDivisor N)
    have hRR' := ModularCurve.functionFieldRiemannRoch_modularFunctionFieldBar N hω
      (embDivisor N - Finsupp.single (cuspInftyBar N) (1 : ℤ))
    rw [AlgebraicCurve.ell_eq_zero_of_degree_neg hcanE] at hRR
    rw [AlgebraicCurve.ell_eq_zero_of_degree_neg hcanE'] at hRR'

    have hellEq : ell (embDivisor N) = ell (embDivisor N - Finsupp.single (cuspInftyBar N) (1 : ℤ)) := by
      unfold ell LSpace
      rw [heqL]
    rw [hdegE] at hRR
    rw [hdegE'] at hRR'
    rw [hellEq] at hRR
    omega
  ·
    have h1 : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace (embDivisor N) := by
      rw [mem_riemannRochSpace_iff]
      intro v
      refine Or.inr ?_
      rw [Place.ord_one]
      simp only [embDivisor]
      rcases eq_or_ne v (cuspInftyBar N) with hvw | hvw
      · subst hvw
        simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
        omega
      · simp [Finsupp.single_eq_of_ne hvw]
    have h1' := hspan h1
    rw [mem_riemannRochSpace_iff] at h1'
    rcases h1' w with h0 | hle
    · exact one_ne_zero h0
    · rw [Place.ord_one, Finsupp.sub_apply, Finsupp.single_eq_same] at hle
      have hEw : embDivisor N w = 0 := by
        simp only [embDivisor]
        simp [Finsupp.single_eq_of_ne hw]
      rw [hEw] at hle
      omega

#print axioms solution

end S_ModularCurve_exists_ord_add_embDivisor_eq_zero
end P2MW
export P2MW.S_ModularCurve_exists_ord_add_embDivisor_eq_zero (solution)
