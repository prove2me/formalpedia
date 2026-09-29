-- Prove2me | solution 1 for ModularCurve.isOfFinAddOrder_jZeroC_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/fe6405ca-2e9f-5cda-930b-424678236375

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_isOfFinAddOrder_jZeroC_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isOfFinAddOrder_jZeroC_residueField
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_isOfFinAddOrder_jZeroC_residueField.ModularCurve IsLocalRing Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroC isOfFinAddOrder_jZeroC_of_isAlgebraic"
p2m_open "ModularCurve"

theorem isAlgebraic_zmod_residueField (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField A) ℓ] :
    letI := ZMod.algebra (ResidueField A) ℓ
    Algebra.IsAlgebraic (ZMod ℓ) (ResidueField A) := by
  letI := ZMod.algebra (ResidueField A) ℓ
  refine ⟨fun y => ?_⟩
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y

  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ
    all_goals first | rfl | skip
  haveI : IsScalarTower ℤ ℚ (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq fun n => by simp
  have hxQ : IsAlgebraic ℚ (x : AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isAlgebraic _
  obtain ⟨p₀, hp₀0, hp₀x⟩ := hxQ
  set p : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) p₀ with hpdef
  have hp0 : p ≠ 0 := fun h =>
    hp₀0 (IsFractionRing.integerNormalization_eq_zero_iff.mp h)
  have hpx : aeval (x : AlgebraicClosure ℚ) p = 0 := by
    obtain ⟨b, -, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p₀
    have h1 : aeval (x : AlgebraicClosure ℚ) (p.map (algebraMap ℤ ℚ)) = 0 := by
      rw [hpdef, hb]
      simp only [Algebra.smul_def, map_mul, hp₀x, mul_zero]
    rwa [aeval_map_algebraMap] at h1

  set p₁ := p.primPart with hp₁
  have hprim : p₁.IsPrimitive := p.isPrimitive_primPart
  have hp₁x : aeval (x : AlgebraicClosure ℚ) p₁ = 0 := by
    have hc : p.content ≠ 0 := fun h => hp0 (content_eq_zero_iff.mp h)
    have hfac := p.eq_C_content_mul_primPart
    rw [hfac, map_mul, aeval_C, mul_eq_zero] at hpx
    rcases hpx with h | h
    · exact absurd h (by rw [eq_intCast]; exact_mod_cast hc)
    · exact h

  have hp₁xA : aeval x p₁ = 0 := by
    apply Subtype.val_injective
    have h := aeval_algHom_apply (A.toSubring.subtype.toIntAlgHom) x p₁

    change ((aeval x p₁ : A) : AlgebraicClosure ℚ) = ((0 : A) : AlgebraicClosure ℚ)
    rw [ZeroMemClass.coe_zero, ← hp₁x]
    exact h.symm
  have hres : aeval (residue A x) p₁ = 0 := by
    rw [show residue A x = (residue A).toIntAlgHom x from rfl, aeval_algHom_apply, hp₁xA, map_zero]

  set q := p₁.map (algebraMap ℤ (ZMod ℓ)) with hq
  have hq0 : q ≠ 0 := by
    intro h
    have hdvd : C (ℓ : ℤ) ∣ p₁ := by
      rw [C_dvd_iff_dvd_coeff]
      intro n
      have hn : ((p₁.coeff n : ℤ) : ZMod ℓ) = 0 := by
        have := congrArg (fun r => coeff r n) h
        simpa only [hq, coeff_map, eq_intCast, coeff_zero] using this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp hn
    have hu := hprim (ℓ : ℤ) hdvd
    rw [Int.isUnit_iff] at hu
    rcases hu with hu | hu
    · have := (Fact.out : ℓ.Prime).one_lt; omega
    · have : (0 : ℤ) ≤ ℓ := Int.natCast_nonneg ℓ; omega
  refine ⟨q, hq0, ?_⟩
  rw [hq, aeval_def, eval₂_map,
    RingHom.ext_int ((algebraMap (ZMod ℓ) (ResidueField A)).comp (algebraMap ℤ (ZMod ℓ)))
      (algebraMap ℤ (ResidueField A)), ← aeval_def]
  exact hres

theorem isOfFinAddOrder_jZeroC_residueField' (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓp : ¬ ℓ ∣ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField ↥A) ℓ] (u : JZeroC (IsLocalRing.ResidueField ↥A) p) :
    IsOfFinAddOrder u := by
  letI := ZMod.algebra (ResidueField A) ℓ
  haveI := isAlgebraic_zmod_residueField ℓ A
  exact isOfFinAddOrder_jZeroC_of_isAlgebraic ℓ (ResidueField A) p hℓp u

end ModularCurve

theorem solution
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField ↥A) ℓ]
    (u : JZeroC (IsLocalRing.ResidueField ↥A) p) : IsOfFinAddOrder u :=
  ModularCurve.isOfFinAddOrder_jZeroC_residueField' p ℓ hℓp A hA u

end S_ModularCurve_isOfFinAddOrder_jZeroC_residueField
end P2MW
export P2MW.S_ModularCurve_isOfFinAddOrder_jZeroC_residueField (solution)
