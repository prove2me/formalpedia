-- Prove2me | solution 1 for ModularCurve.JZero.exists_ord_div_sub_evalAt_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/83c89943-bac9-554a-850d-08d060bcc8b9

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_JZero_exists_regVal_chord_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_ord_div_sub_evalAt_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_exists_ord_div_sub_evalAt_eq_one.AlgebraicCurve Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "pivotIndex evalVec Place Place.ord_zero Place.evalAt regVal"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField adicValuation adicValuation_ne_zero adicValuation_coe ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible algebraMap_mem' toValuationSubring IsRational residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt isUnit_mk_of_ord_eq_zero evalAt_mul_of_mem evalAt_algebraMap_eq mem_toValuationSubring_of_ord_nonneg_alt isRational_iff_deg_eq_one"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.c3a_adicValuation_le_exp_neg_iff (f : F) (n : ℤ) :
    v.adicValuation f ≤ WithZero.exp (-n) ↔ f = 0 ∨ n ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hne := v.adicValuation_ne_zero hf
    rw [← WithZero.log_le_iff_le_exp hne]
    simp only [hf, false_or, ord]
    omega

p2m_export "AlgebraicCurve.Place" "c3a_adicValuation_le_exp_neg_iff"

private theorem _root_.AlgebraicCurve.Place.c3a_adicValuation_algebraMap_le_one (c : K) : v.adicValuation (algebraMap K F c) ≤ 1 := by
  have h : algebraMap K F c = ((⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) : F) := rfl
  rw [h, v.adicValuation_coe]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _

p2m_export "AlgebraicCurve.Place" "c3a_adicValuation_algebraMap_le_one"
end AlgebraicCurve.Place

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "pivotIndex evalVec Place Place.ord_zero Place.evalAt regVal" namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField adicValuation adicValuation_ne_zero adicValuation_coe ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible algebraMap_mem' toValuationSubring IsRational residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt isUnit_mk_of_ord_eq_zero evalAt_mul_of_mem evalAt_algebraMap_eq mem_toValuationSubring_of_ord_nonneg_alt isRational_iff_deg_eq_one" end AlgebraicCurve.Place
namespace AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.exists_ord_eq_one_of_ord_sum_eq_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {ι : Type*} (s : Finset ι) (c : ι → K) (f : ι → F)
    (hf : ∀ i ∈ s, f i = 0 ∨ 1 ≤ v.ord (f i))
    (h : v.ord (∑ i ∈ s, algebraMap K F (c i) * f i) = 1) :
    ∃ i ∈ s, v.ord (f i) = 1 := by
  classical
  by_contra hcon
  push Not at hcon

  have hterm : ∀ i ∈ s,
      v.adicValuation (algebraMap K F (c i) * f i) ≤ WithZero.exp (-(2 : ℤ)) := by
    intro i hi
    rcases hf i hi with h0 | h1
    · simp [h0]
    · have h2 : (2 : ℤ) ≤ v.ord (f i) := by
        have := hcon i hi
        omega
      rw [map_mul]
      calc v.adicValuation (algebraMap K F (c i)) * v.adicValuation (f i)
          ≤ 1 * WithZero.exp (-(2 : ℤ)) :=
            mul_le_mul' (v.c3a_adicValuation_algebraMap_le_one (c i))
              ((v.c3a_adicValuation_le_exp_neg_iff (f i) 2).mpr (Or.inr h2))
        _ = WithZero.exp (-(2 : ℤ)) := one_mul _

  have hsum := (v.c3a_adicValuation_le_exp_neg_iff _ 2).mp (v.adicValuation.map_sum_le hterm)
  rcases hsum with h0 | h2
  · rw [h0, AlgebraicCurve.Place.ord_zero] at h
    exact zero_ne_one h
  · omega

end AlgebraicCurve.Place
p2m_export "" "AlgebraicCurve.Place.exists_ord_eq_one_of_ord_sum_eq_one"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "pivotIndex evalVec Place Place.ord_zero Place.evalAt regVal"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField adicValuation adicValuation_ne_zero adicValuation_coe ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible algebraMap_mem' toValuationSubring IsRational residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt isUnit_mk_of_ord_eq_zero evalAt_mul_of_mem evalAt_algebraMap_eq mem_toValuationSubring_of_ord_nonneg_alt isRational_iff_deg_eq_one"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.c3a_mem_of_evalAt_ne_zero {f : F} (h : v.evalAt f ≠ 0) : f ∈ v.toValuationSubring := by
  by_contra hf
  apply h
  unfold Place.evalAt
  rw [dif_neg hf]

p2m_export "AlgebraicCurve.Place" "c3a_mem_of_evalAt_ne_zero"
private theorem _root_.AlgebraicCurve.Place.c3a_isUnit_of_evalAt_ne_zero {f : F} (h : v.evalAt f ≠ 0) :
    IsUnit (⟨f, v.c3a_mem_of_evalAt_ne_zero h⟩ : v.toValuationSubring) := by
  by_contra hu
  apply h
  rw [v.evalAt_of_mem (v.c3a_mem_of_evalAt_ne_zero h),
    (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu),
    ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

p2m_export "AlgebraicCurve.Place" "c3a_isUnit_of_evalAt_ne_zero"
private theorem _root_.AlgebraicCurve.Place.c3a_ord_eq_zero_of_evalAt_ne_zero {f : F} (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have hu := v.c3a_isUnit_of_evalAt_ne_zero h
  have h0 := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at h0
  exact h0

p2m_export "AlgebraicCurve.Place" "c3a_ord_eq_zero_of_evalAt_ne_zero"
private theorem _root_.AlgebraicCurve.Place.c3a_adicValuation_le_one_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.adicValuation f ≤ 1 := by
  have h : f = ((⟨f, hf⟩ : v.toValuationSubring) : F) := rfl
  rw [h, v.adicValuation_coe]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _

p2m_export "AlgebraicCurve.Place" "c3a_adicValuation_le_one_of_mem"
private theorem _root_.AlgebraicCurve.Place.c3a_algebraMap_residueField (c : K) :
    algebraMap K v.ResidueField c
      = IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring c) := by
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c,
    IsLocalRing.ResidueField.algebraMap_eq]

p2m_export "AlgebraicCurve.Place" "c3a_algebraMap_residueField"

private theorem _root_.AlgebraicCurve.Place.c3a_sub_evalAt_zero_or_one_le_ord (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    f - algebraMap K F (v.evalAt f) = 0 ∨ 1 ≤ v.ord (f - algebraMap K F (v.evalAt f)) := by
  rcases eq_or_ne (f - algebraMap K F (v.evalAt f)) 0 with h0 | hne
  · exact Or.inl h0
  · right
    have hgmem : f - algebraMap K F (v.evalAt f) ∈ v.toValuationSubring :=
      sub_mem hf (v.algebraMap_mem' _)
    have hmk : (⟨f - algebraMap K F (v.evalAt f), hgmem⟩ : v.toValuationSubring)
        = ⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) :=
      Subtype.ext (by simp [v.coe_algebraMap])
    have hmax : (⟨f - algebraMap K F (v.evalAt f), hgmem⟩ : v.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
      rw [hmk, ← IsLocalRing.residue_eq_zero_iff, map_sub, ← v.c3a_algebraMap_residueField,
        v.algebraMap_evalAt hv hf, sub_self]
    have hnonneg : 0 ≤ v.ord (f - algebraMap K F (v.evalAt f)) := by
      rcases (v.c3a_adicValuation_le_exp_neg_iff _ 0).mp
          (by simpa using v.c3a_adicValuation_le_one_of_mem hgmem) with h | h
      · exact absurd h hne
      · exact h
    have hne0 : v.ord (f - algebraMap K F (v.evalAt f)) ≠ 0 := by
      intro h0
      exact (IsLocalRing.mem_maximalIdeal _).mp hmax (v.isUnit_mk_of_ord_eq_zero hne h0)
    omega

p2m_export "AlgebraicCurve.Place" "c3a_sub_evalAt_zero_or_one_le_ord"
end AlgebraicCurve.Place

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_exists_ord_div_sub_evalAt_eq_one.AlgebraicCurve AlgebraicCurve.Place P2MW.S_ModularCurve_JZero_exists_ord_div_sub_evalAt_eq_one.AlgebraicCurve.Place ModularCurve"

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "pivotIndex evalVec Place Place.ord_zero Place.evalAt regVal" end AlgebraicCurve
p2m_open_scoped "AlgebraicCurve" in

theorem AlgebraicCurve.c3a_exists_ord_div_sub_evalAt_eq_one_of_regVal_ne_zero
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (hs0 : ∀ j, s j ≠ 0) (w : Place (AlgebraicClosure ℚ) F) (hv : w.IsRational)
    (t : F) (ht : w.ord t = 1) (p : Fin r × Fin r)
    (hreg : regVal s w t 1 1 (evalVec s w p.1 • s p.2 - evalVec s w p.2 • s p.1) ≠ 0)
    (i : Fin r) (hi : ∀ j, w.ord (s i) ≤ w.ord (s j)) :
    ∃ j, w.ord (s j * (s i)⁻¹ - algebraMap (AlgebraicClosure ℚ) F (w.evalAt (s j * (s i)⁻¹))) = 1 := by
  classical
  have hr : 0 < r := Fin.pos i
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, ord_zero] at ht
    exact zero_ne_one ht
  unfold regVal at hreg
  rw [dif_pos hr, pow_one, pow_one] at hreg

  have hpiv : ∀ j, w.ord (s (pivotIndex s w hr)) ≤ w.ord (s j) := by
    have hex : ∃ i : Fin r, ∀ j : Fin r, w.ord (s i) ≤ w.ord (s j) := ⟨i, hi⟩
    unfold pivotIndex
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  have hpi : w.ord (s (pivotIndex s w hr)) = w.ord (s i) :=
    le_antisymm (hpiv i) (hi _)

  have hg0 : (evalVec s w p.1 • s p.2 - evalVec s w p.2 • s p.1) * (s (pivotIndex s w hr))⁻¹
      * t⁻¹ ≠ 0 := by
    intro h
    apply hreg
    rw [h, ← map_zero (algebraMap (AlgebraicClosure ℚ) F), w.evalAt_algebraMap_eq]
  have hchord0 : evalVec s w p.1 • s p.2 - evalVec s w p.2 • s p.1 ≠ 0 := by
    intro h
    apply hg0
    rw [h, zero_mul, zero_mul]
  have hgord := w.c3a_ord_eq_zero_of_evalAt_ne_zero hreg
  rw [w.ord_mul (mul_ne_zero hchord0 (inv_ne_zero (hs0 _))) (inv_ne_zero ht0),
    w.ord_mul hchord0 (inv_ne_zero (hs0 _)), w.ord_inv, w.ord_inv, ht, hpi] at hgord
  have h1 : w.ord ((evalVec s w p.1 • s p.2 - evalVec s w p.2 • s p.1) * (s i)⁻¹) = 1 := by
    rw [w.ord_mul hchord0 (inv_ne_zero (hs0 i)), w.ord_inv]
    omega

  have hZ : ∀ j, s j * (s i)⁻¹ ∈ w.toValuationSubring := fun j =>
    w.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 j) (inv_ne_zero (hs0 i)))
      (by rw [w.ord_mul (hs0 j) (inv_ne_zero (hs0 i)), w.ord_inv]; linarith [hi j])
  have hZpiv : s i * (s (pivotIndex s w hr))⁻¹ ∈ w.toValuationSubring :=
    w.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 i) (inv_ne_zero (hs0 _)))
      (by rw [w.ord_mul (hs0 i) (inv_ne_zero (hs0 _)), w.ord_inv, hpi]; simp)

  have hev : ∀ j, evalVec s w j
      = w.evalAt (s j * (s i)⁻¹) * w.evalAt (s i * (s (pivotIndex s w hr))⁻¹) := by
    intro j
    unfold evalVec
    rw [dif_pos hr]
    have hsplit : s j * (s (pivotIndex s w hr))⁻¹
        = (s j * (s i)⁻¹) * (s i * (s (pivotIndex s w hr))⁻¹) := by
      rw [mul_assoc, ← mul_assoc (s i)⁻¹, inv_mul_cancel₀ (hs0 i), one_mul]
    rw [hsplit, w.evalAt_mul_of_mem hv (hZ j) hZpiv]

  set u : AlgebraicClosure ℚ := w.evalAt (s i * (s (pivotIndex s w hr))⁻¹) with hu
  set b₁ : AlgebraicClosure ℚ := w.evalAt (s p.1 * (s i)⁻¹) with hb₁
  set b₂ : AlgebraicClosure ℚ := w.evalAt (s p.2 * (s i)⁻¹) with hb₂
  set cvec : Fin 2 → AlgebraicClosure ℚ := ![-(u * b₂), u * b₁] with hcvec
  set fvec : Fin 2 → F :=
    ![s p.1 * (s i)⁻¹ - algebraMap (AlgebraicClosure ℚ) F b₁,
      s p.2 * (s i)⁻¹ - algebraMap (AlgebraicClosure ℚ) F b₂] with hfvec
  have hident : (evalVec s w p.1 • s p.2 - evalVec s w p.2 • s p.1) * (s i)⁻¹
      = ∑ k : Fin 2, algebraMap (AlgebraicClosure ℚ) F (cvec k) * fvec k := by
    rw [Fin.sum_univ_two]
    simp only [hcvec, hfvec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Algebra.smul_def, hev, map_mul, map_neg]
    ring
  have hcomb : w.ord (∑ k ∈ (Finset.univ : Finset (Fin 2)),
      algebraMap (AlgebraicClosure ℚ) F (cvec k) * fvec k) = 1 := by
    rw [← hident]
    exact h1
  have hfv : ∀ k ∈ (Finset.univ : Finset (Fin 2)), fvec k = 0 ∨ 1 ≤ w.ord (fvec k) := by
    intro k _
    fin_cases k
    · simpa [hfvec, hb₁] using w.c3a_sub_evalAt_zero_or_one_le_ord hv (hZ p.1)
    · simpa [hfvec, hb₂] using w.c3a_sub_evalAt_zero_or_one_le_ord hv (hZ p.2)
  obtain ⟨k, -, hk⟩ := w.exists_ord_eq_one_of_ord_sum_eq_one Finset.univ cvec fvec hfv hcomb
  fin_cases k
  · exact ⟨p.1, by simpa [hfvec, hb₁] using hk⟩
  · exact ⟨p.2, by simpa [hfvec, hb₂] using hk⟩

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (i : Fin r) (hi : ∀ j, w.ord (s i) ≤ w.ord (s j)) :
    ∃ j, w.ord (s j * (s i)⁻¹
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (w.evalAt (s j * (s i)⁻¹))) = 1 := by
  have hv : w.IsRational :=
    (w.isRational_iff_deg_eq_one).mpr (ModularCurve.deg_eq_one_modularFunctionFieldBar N w)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ1 : w.ord (π : modularFunctionFieldBar N) = 1 := w.ord_coe_irreducible hπ
  obtain ⟨p, hreg⟩ := ModularCurve.JZero.exists_regVal_chord_ne_zero N s hs w _ hπ1
  exact AlgebraicCurve.c3a_exists_ord_div_sub_evalAt_eq_one_of_regVal_ne_zero s
    (fun j => hs.1.ne_zero j) w hv _ hπ1 p hreg i hi

#print axioms solution

end S_ModularCurve_JZero_exists_ord_div_sub_evalAt_eq_one
end P2MW
export P2MW.S_ModularCurve_JZero_exists_ord_div_sub_evalAt_eq_one (solution)
