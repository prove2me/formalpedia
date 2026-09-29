-- Prove2me | solution 1 for ModularCurve.exists_mem_riemannRochSpace_mul_eq_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/042d051e-6c4c-56b7-8f67-7d49a69ff5b9

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_ModularCurve_exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_cuspInftyBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_riemannRochSpace_mul_eq_of_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.jqNModC_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (N : ℕ) [NeZero N]
    (f : modularFunctionFieldBar N) (hf : f ≠ 0) :
    ∃ n : ℕ, ∃ u g : modularFunctionFieldBar N,
      u ≠ 0 ∧ u ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) ∧
      g ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) ∧ f * u = g := by
  classical
  obtain ⟨g₀, hg₀⟩ := ModularCurve.exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree N
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf
  set c := cuspInftyBar N with hc

  set Dneg : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    (D.filter (fun v => v ≠ c)).mapRange (fun z => min z 0) (by simp) with hDneg
  have hDneg_apply : ∀ v, Dneg v = if v ≠ c then min (D v) 0 else 0 := by
    intro v
    rw [hDneg, Finsupp.mapRange_apply, Finsupp.filter_apply]
    split_ifs <;> simp
  set m : ℕ := g₀ + (-(Divisor.degree Dneg)).toNat with hm
  set D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    (m : ℤ) • Finsupp.single c 1 + Dneg with hD'
  have hD'_apply : ∀ v, D' v = (if v = c then (m : ℤ) else 0) + Dneg v := by
    intro v
    rw [hD', Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hv : v = c
    · rw [if_pos hv.symm, if_pos hv, mul_one]
    · rw [if_neg (fun h => hv h.symm), if_neg hv, mul_zero]
  have hdegc : c.deg = 1 := ModularCurve.deg_cuspInftyBar N
  have hdeg' : (g₀ : ℤ) ≤ D'.degree := by
    have hcalc : D'.degree = (m : ℤ) + Dneg.degree := by
      rw [hD', map_add, map_zsmul, Divisor.degree_single, hdegc]
      simp
    rw [hcalc, hm]
    have h1 : -(Divisor.degree Dneg) ≤ ((-(Divisor.degree Dneg)).toNat : ℤ) := Int.self_le_toNat _
    push_cast
    omega
  obtain ⟨u, hu, hunot⟩ := hg₀ D' hdeg' c
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hunot (zero_mem _)
  have hu' := mem_riemannRochSpace_iff.mp hu
  refine ⟨m + (-(D c)).toNat, u, f * u, hu0, ?_, ?_, rfl⟩
  · rw [mem_riemannRochSpace_iff]
    intro v
    rcases hu' v with h | h
    · exact Or.inl h
    right
    rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    rw [hD'_apply, hDneg_apply] at h
    by_cases hv : v = c
    · rw [if_pos hv, if_neg (not_not_intro hv), add_zero] at h
      rw [if_pos hv.symm, mul_one]
      push_cast
      omega
    · rw [if_neg hv, if_pos hv, zero_add] at h
      rw [if_neg (fun h' => hv h'.symm), mul_zero, neg_zero]
      have : min (D v) 0 ≤ 0 := min_le_right _ _
      omega
  · rw [mem_riemannRochSpace_iff]
    intro v
    right
    rw [v.ord_mul hf hu0, ← hD v, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    rcases hu' v with h | h
    · exact absurd h hu0
    rw [hD'_apply, hDneg_apply] at h
    by_cases hv : v = c
    · subst hv
      rw [if_pos rfl, if_neg (not_not_intro rfl), add_zero] at h
      rw [if_pos rfl, mul_one]
      have h2 : -(D (cuspInftyBar N)) ≤ ((-(D (cuspInftyBar N))).toNat : ℤ) := Int.self_le_toNat _
      push_cast
      omega
    · rw [if_neg hv, if_pos hv, zero_add] at h
      rw [if_neg (fun h' => hv h'.symm), mul_zero, neg_zero]
      have h3 : min (D v) 0 ≤ D v := min_le_left _ _
      omega

end S_ModularCurve_exists_mem_riemannRochSpace_mul_eq_of_ne_zero
end P2MW
export P2MW.S_ModularCurve_exists_mem_riemannRochSpace_mul_eq_of_ne_zero (solution)
