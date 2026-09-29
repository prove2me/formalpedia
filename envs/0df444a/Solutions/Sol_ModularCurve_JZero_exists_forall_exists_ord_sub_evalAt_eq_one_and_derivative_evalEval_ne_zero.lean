-- Prove2me | solution 1 for ModularCurve.JZero.exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8bfa8928-6a8b-5b07-85f0-ad18f411b53d

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_Transcendental_exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne
import Theorems.Thm_AlgebraicCurve_Place_eval_leadingCoeff_ne_zero_of_forall_mem_toValuationSubring
import Theorems.Thm_ModularCurve_JZero_exists_ord_div_sub_evalAt_eq_one
import Theorems.Thm_LinearMap_exists_int_forall_apply_ne
import Theorems.Thm_LinearMap_exists_int_forall_apply_notMem
import Theorems.Thm_ModularCurve_JZero_chordVec_ne_zero_of_ne
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_ModularCurve_JZero_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_JZero_exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero.ModularCurve Polynomial"

namespace Transcendental p2m_export "Transcendental" "exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero" end Transcendental
p2m_open_scoped "Transcendental" in
theorem Transcendental.exists_irreducible_isIntegral_evalEval_eq_zero_and_derivative_ne_zero
    {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] (x₀ : F)
    [FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x₀} : Set F)) F]
    {z : F} (hz : Transcendental (AlgebraicClosure ℚ) z) (y : F) :
    ∃ G : Polynomial (Polynomial (AlgebraicClosure ℚ)), Irreducible G ∧
      (∀ n n', IsIntegral ℤ ((G.coeff n).coeff n')) ∧
      (G.map (Polynomial.mapRingHom (algebraMap (AlgebraicClosure ℚ) F))).evalEval z y = 0 ∧
      ((Polynomial.derivative G).map (Polynomial.mapRingHom
        (algebraMap (AlgebraicClosure ℚ) F))).evalEval z y ≠ 0 := by
  classical
  obtain ⟨G₀, hirr, hrel, hder⟩ :=
    Transcendental.exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero x₀ hz y

  let S : Finset (AlgebraicClosure ℚ) :=
    G₀.support.biUnion fun n => ((G₀.coeff n).support.image fun n' => (G₀.coeff n).coeff n')
  haveI : Algebra.IsAlgebraic ℤ (AlgebraicClosure ℚ) := by
    haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    exact Algebra.IsAlgebraic.trans ℤ ℚ (AlgebraicClosure ℚ)
  obtain ⟨m, hm0, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ S
  have hmK : (m : AlgebraicClosure ℚ) ≠ 0 := Int.cast_ne_zero.mpr hm0
  have hmF : algebraMap (AlgebraicClosure ℚ) F (m : AlgebraicClosure ℚ) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) F).injective).mpr hmK
  refine ⟨C (C (m : AlgebraicClosure ℚ)) * G₀, ?_, ?_, ?_, ?_⟩
  · exact (irreducible_isUnit_mul (isUnit_C.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hmK)))).mpr hirr
  · intro n n'
    rw [coeff_C_mul, coeff_C_mul]
    by_cases hn : n ∈ G₀.support
    · by_cases hn' : n' ∈ (G₀.coeff n).support
      · have := hint _ (Finset.mem_biUnion.mpr ⟨n, hn, Finset.mem_image.mpr ⟨n', hn', rfl⟩⟩)
        rw [Algebra.smul_def, eq_intCast] at this
        exact this
      · rw [notMem_support_iff.mp hn', mul_zero]
        exact isIntegral_zero
    · rw [notMem_support_iff.mp hn, coeff_zero, mul_zero]
      exact isIntegral_zero
  · simp only [Polynomial.map_mul, evalEval_mul, hrel, mul_zero]
  · rw [derivative_C_mul]
    simp only [Polynomial.map_mul, Polynomial.map_C, coe_mapRingHom, evalEval_mul, evalEval_C, eval_C]
    exact mul_ne_zero hmF hder

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_JZero_exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero.ModularCurve Polynomial IsLocalRing"
open scoped Polynomial.Bivariate

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "pivotIndex evalVec chordVec Place Place.ord_zero HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.evalAt_one"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg adicValuation adicValuation_ne_zero adicValuation_coe ord ord_zero ord_mul ord_inv ord_coe_unit algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt evalAt_one derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne eval_leadingCoeff_ne_zero_of_forall_mem_toValuationSubring isRational_iff_deg_eq_one ord_nonneg_of_mem mem_of_ord_nonneg evalAt_mul evalAt_algebraMap evalAt_ne_zero"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem c3e_algebraMap_residueField (c : K) :
    algebraMap K v.ResidueField c = residue v.toValuationSubring (algebraMap K v.toValuationSubring c) := by
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c, ResidueField.algebraMap_eq]

private theorem _root_.AlgebraicCurve.Place.c3e_residue_mk (hv : v.IsRational) (a : v.toValuationSubring) :
    residue v.toValuationSubring a = algebraMap K v.ResidueField (v.evalAt (a : F)) := by
  rw [v.algebraMap_evalAt hv a.2]

p2m_export "AlgebraicCurve.Place" "c3e_residue_mk"

private theorem _root_.AlgebraicCurve.Place.c3e_hom_evalEval {S : Type*} [CommRing S] (φ : v.toValuationSubring →+* S)
    (P : K[X][Y]) (a b : v.toValuationSubring) :
    φ ((P.map (mapRingHom (algebraMap K v.toValuationSubring))).evalEval a b)
      = (P.map (mapRingHom (φ.comp (algebraMap K v.toValuationSubring)))).evalEval (φ a) (φ b) := by
  rw [← map_mapRingHom_evalEval φ, Polynomial.map_map, mapRingHom_comp]

p2m_export "AlgebraicCurve.Place" "c3e_hom_evalEval"
private theorem _root_.AlgebraicCurve.Place.c3e_coe_evalEval (P : K[X][Y]) (a b : v.toValuationSubring) :
    (((P.map (mapRingHom (algebraMap K v.toValuationSubring))).evalEval a b : v.toValuationSubring) : F)
      = (P.map (mapRingHom (algebraMap K F))).evalEval (a : F) (b : F) := by
  have h := v.c3e_hom_evalEval (algebraMap v.toValuationSubring F) P a b
  rw [← IsScalarTower.algebraMap_eq K v.toValuationSubring F] at h
  exact h

p2m_export "AlgebraicCurve.Place" "c3e_coe_evalEval"
private theorem _root_.AlgebraicCurve.Place.c3e_evalEval_mem (P : K[X][Y]) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring) :
    (P.map (mapRingHom (algebraMap K F))).evalEval z y ∈ v.toValuationSubring := by
  rw [← v.c3e_coe_evalEval P ⟨z, hz⟩ ⟨y, hy⟩]
  exact SetLike.coe_mem _

p2m_export "AlgebraicCurve.Place" "c3e_evalEval_mem"

private theorem _root_.AlgebraicCurve.Place.c3e_evalAt_evalEval (hv : v.IsRational) (P : K[X][Y]) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring) :
    v.evalAt ((P.map (mapRingHom (algebraMap K F))).evalEval z y)
      = P.evalEval (v.evalAt z) (v.evalAt y) := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (v.c3e_evalEval_mem P hz hy)]
  have hmk : (⟨(P.map (mapRingHom (algebraMap K F))).evalEval z y, v.c3e_evalEval_mem P hz hy⟩
        : v.toValuationSubring)
      = (P.map (mapRingHom (algebraMap K v.toValuationSubring))).evalEval ⟨z, hz⟩ ⟨y, hy⟩ :=
    Subtype.ext (by rw [c3e_coe_evalEval])
  rw [hmk, ← ResidueField.algebraMap_eq, c3e_hom_evalEval,
    ← IsScalarTower.algebraMap_eq K v.toValuationSubring v.ResidueField,
    ResidueField.algebraMap_eq, v.c3e_residue_mk hv, v.c3e_residue_mk hv,
    map_mapRingHom_evalEval]

p2m_export "AlgebraicCurve.Place" "c3e_evalAt_evalEval"

private theorem _root_.AlgebraicCurve.Place.c3e_sum_smul_mem {ι : Type*} (S : Finset ι) (f : ι → F) (c : ι → K)
    (hf : ∀ l ∈ S, f l ∈ v.toValuationSubring) :
    (∑ l ∈ S, c l • f l) ∈ v.toValuationSubring := by
  refine Subring.sum_mem _ fun l hl => ?_
  rw [Algebra.smul_def]
  exact mul_mem (v.algebraMap_mem' _) (hf l hl)

p2m_export "AlgebraicCurve.Place" "c3e_sum_smul_mem"

private theorem _root_.AlgebraicCurve.Place.c3e_evalAt_add (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

p2m_export "AlgebraicCurve.Place" "c3e_evalAt_add"

private theorem _root_.AlgebraicCurve.Place.c3e_evalAt_smul (hv : v.IsRational) (a : K) {f : F}
    (hf : f ∈ v.toValuationSubring) : v.evalAt (a • f) = a * v.evalAt f := by
  rw [Algebra.smul_def, v.evalAt_mul hv (v.algebraMap_mem' a) hf, v.evalAt_algebraMap]

p2m_export "AlgebraicCurve.Place" "c3e_evalAt_smul"

private theorem _root_.AlgebraicCurve.Place.c3e_evalAt_sum_smul (hv : v.IsRational) {ι : Type*} (S : Finset ι) (f : ι → F)
    (c : ι → K) (hf : ∀ l ∈ S, f l ∈ v.toValuationSubring) :
    v.evalAt (∑ l ∈ S, c l • f l) = ∑ l ∈ S, c l * v.evalAt (f l) := by
  induction S using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ← map_zero (algebraMap K F), v.evalAt_algebraMap]
  | cons a S ha ih =>
    have hf' : ∀ l ∈ S, f l ∈ v.toValuationSubring := fun l hl => hf l (Finset.mem_cons_of_mem hl)
    have ha' : c a • f a ∈ v.toValuationSubring := by
      simpa only [Algebra.smul_def] using mul_mem (v.algebraMap_mem' (c a)) (hf a (Finset.mem_cons_self a S))
    rw [Finset.sum_cons, Finset.sum_cons, v.c3e_evalAt_add hv ha' (v.c3e_sum_smul_mem S f c hf'),
      v.c3e_evalAt_smul hv (c a) (hf a (Finset.mem_cons_self a S)), ih hf']

p2m_export "AlgebraicCurve.Place" "c3e_evalAt_sum_smul"

theorem c3e_finite_setOf_ord_ne_zero [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    {w : Place K F | w.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine (D.support.finite_toSet).subset fun w hw => ?_
  rw [Finset.mem_coe, Finsupp.mem_support_iff, hD]
  exact hw

private theorem _root_.AlgebraicCurve.Place.c3e_ord_pos_of_evalAt_eq_zero (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f = 0) : 0 < v.ord f := by
  have h1 : 0 ≤ v.ord f := v.ord_nonneg_of_mem hf
  have h2 : v.ord f ≠ 0 := fun h0 => v.evalAt_ne_zero hv hf0 h0 h
  omega

p2m_export "AlgebraicCurve.Place" "c3e_ord_pos_of_evalAt_eq_zero"

private theorem _root_.AlgebraicCurve.Place.c3e_mem_of_isIntegral (Q : Place K F) {g : F} (hg : IsIntegral K g) :
    g ∈ Q.toValuationSubring := by
  have hint : IsIntegral Q.toValuationSubring g := hg.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact hy ▸ y.2

p2m_export "AlgebraicCurve.Place" "c3e_mem_of_isIntegral"

private theorem _root_.AlgebraicCurve.Place.ord_eq_zero_of_isAlgebraic (Q : Place K F) {g : F} (hg : IsAlgebraic K g) : Q.ord g = 0 := by
  rcases eq_or_ne g 0 with rfl | hne
  · exact Q.ord_zero
  have hmem : g ∈ Q.toValuationSubring := Q.c3e_mem_of_isIntegral hg.isIntegral
  have hmem' : g⁻¹ ∈ Q.toValuationSubring :=
    Q.c3e_mem_of_isIntegral (IsAlgebraic.inv_iff.mpr hg).isIntegral
  have hu : IsUnit (⟨g, hmem⟩ : Q.toValuationSubring) :=
    isUnit_iff_exists_inv.mpr ⟨⟨g⁻¹, hmem'⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩
  have h := Q.ord_coe_unit hu.unit
  rwa [IsUnit.unit_spec] at h

p2m_export "AlgebraicCurve.Place" "ord_eq_zero_of_isAlgebraic"

private theorem _root_.AlgebraicCurve.Place.transcendental_of_ord_sub_algebraMap_ne_zero (Q : Place K F) {f : F} {c : K}
    (h : Q.ord (f - algebraMap K F c) ≠ 0) : Transcendental K f := fun hf =>
  h (Q.ord_eq_zero_of_isAlgebraic ((hf.isIntegral.sub isIntegral_algebraMap).isAlgebraic))

p2m_export "AlgebraicCurve.Place" "transcendental_of_ord_sub_algebraMap_ne_zero"

theorem transcendental_of_ord_sub_evalAt_eq_one (Q : Place K F) {f : F}
    (h : Q.ord (f - algebraMap K F (Q.evalAt f)) = 1) : Transcendental K f :=
  Q.transcendental_of_ord_sub_algebraMap_ne_zero (c := Q.evalAt f) (by rw [h]; exact one_ne_zero)

private theorem _root_.AlgebraicCurve.Place.c3e_evalAt_eval (hv : v.IsRational) (p : K[X]) {z : F} (hz : z ∈ v.toValuationSubring) :
    v.evalAt ((p.map (algebraMap K F)).eval z) = p.eval (v.evalAt z) := by
  have h := v.c3e_evalAt_evalEval hv (C p) hz hz
  rwa [Polynomial.map_C, evalEval_C, evalEval_C] at h

p2m_export "AlgebraicCurve.Place" "c3e_evalAt_eval"

private theorem _root_.AlgebraicCurve.Place.c3e_evalAt_sub_algebraMap (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (c : K) :
    v.evalAt (f - algebraMap K F c) = v.evalAt f - c := by
  have h := v.c3e_evalAt_eval hv (X - C c) hf
  simpa [Polynomial.map_sub] using h

p2m_export "AlgebraicCurve.Place" "c3e_evalAt_sub_algebraMap"

theorem c3e_finite_fibre [HasPrincipalDivisors K F] (hrat : ∀ w : Place K F, w.IsRational)
    (Q : Place K F) {z : F} (he : Q.ord (z - algebraMap K F (Q.evalAt z)) = 1) :
    {P : Place K F | z ∈ P.toValuationSubring ∧ P.evalAt z = Q.evalAt z}.Finite := by
  have hne : z - algebraMap K F (Q.evalAt z) ≠ 0 := by
    intro h0; rw [h0, ord_zero] at he; exact zero_ne_one he
  refine (c3e_finite_setOf_ord_ne_zero (K := K) hne).subset fun P hP => ?_
  obtain ⟨hzP, hval⟩ := hP
  have hmem : z - algebraMap K F (Q.evalAt z) ∈ P.toValuationSubring := sub_mem hzP (P.algebraMap_mem' _)
  have hv0 : P.evalAt (z - algebraMap K F (Q.evalAt z)) = 0 := by
    rw [P.c3e_evalAt_sub_algebraMap (hrat P) hzP, hval, sub_self]
  exact ne_of_gt (P.c3e_ord_pos_of_evalAt_eq_zero (hrat P) hne hmem hv0)

theorem c3e_good [CharZero K]
    (x₀ : F) [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (hrat : ∀ w : Place K F, w.IsRational)
    {z y : F} (hz : Transcendental K z)
    (G : K[X][Y]) (hGirr : Irreducible G) (hG : (G.map (mapRingHom (algebraMap K F))).evalEval z y = 0)
    (Q : Place K F) (hzQ : z ∈ Q.toValuationSubring)
    (he : Q.ord (z - algebraMap K F (Q.evalAt z)) = 1)
    (hreg : ∀ P : Place K F, z ∈ P.toValuationSubring → P.evalAt z = Q.evalAt z → y ∈ P.toValuationSubring)
    (hsep : ∀ P : Place K F, P ≠ Q → z ∈ P.toValuationSubring → P.evalAt z = Q.evalAt z →
      P.evalAt y ≠ Q.evalAt y) :
    (derivative G).evalEval (Q.evalAt z) (Q.evalAt y) ≠ 0 := by
  have hyQ : y ∈ Q.toValuationSubring := hreg Q hzQ rfl
  have hlead : G.leadingCoeff.eval (Q.evalAt z) ≠ 0 :=
    eval_leadingCoeff_ne_zero_of_forall_mem_toValuationSubring x₀ hrat hz G hGirr hG (Q.evalAt z) Q hzQ rfl hreg
  exact derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne x₀ hrat hz G hGirr hG Q hzQ hyQ
    he hlead fun Q' hne hz' hzv _ => hsep Q' hne hz' hzv

private theorem _root_.AlgebraicCurve.Place.nudge_adicValuation_le_exp_neg_iff (P : Place K F) (f : F) (n : ℤ) :
    P.adicValuation f ≤ WithZero.exp (-n) ↔ f = 0 ∨ n ≤ P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hne := P.adicValuation_ne_zero hf
    rw [← WithZero.log_le_iff_le_exp hne]
    simp only [hf, false_or, ord]
    omega

p2m_export "AlgebraicCurve.Place" "nudge_adicValuation_le_exp_neg_iff"

private theorem _root_.AlgebraicCurve.Place.nudge_adicValuation_algebraMap_le_one (P : Place K F) (c : K) :
    P.adicValuation (algebraMap K F c) ≤ 1 := by
  have h : algebraMap K F c = ((⟨algebraMap K F c, P.algebraMap_mem' c⟩ : P.toValuationSubring) : F) := rfl
  rw [h, P.adicValuation_coe]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _

p2m_export "AlgebraicCurve.Place" "nudge_adicValuation_algebraMap_le_one"

private theorem _root_.AlgebraicCurve.Place.nudge_evalAt_add (P : Place K F) (hP : P.IsRational) {f g : F}
    (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
  apply P.algebraMap_residueField_injective
  rw [map_add, P.algebraMap_evalAt hP (add_mem hf hg), P.algebraMap_evalAt hP hf,
    P.algebraMap_evalAt hP hg, ← map_add]
  rfl

p2m_export "AlgebraicCurve.Place" "nudge_evalAt_add"

private theorem _root_.AlgebraicCurve.Place.nudge_evalAt_sub_algebraMap (P : Place K F) (hP : P.IsRational) {f : F}
    (hf : f ∈ P.toValuationSubring) (c : K) :
    P.evalAt (f - algebraMap K F c) = P.evalAt f - c := by
  rw [sub_eq_add_neg, ← map_neg, P.nudge_evalAt_add hP hf (P.algebraMap_mem' _), P.evalAt_algebraMap,
    ← sub_eq_add_neg]

p2m_export "AlgebraicCurve.Place" "nudge_evalAt_sub_algebraMap"

private theorem _root_.AlgebraicCurve.Place.nudge_adicValuation_sub_evalAt_le (P : Place K F) (hP : P.IsRational) {f : F}
    (hf : f ∈ P.toValuationSubring) :
    P.adicValuation (f - algebraMap K F (P.evalAt f)) ≤ WithZero.exp (-(1 : ℤ)) := by
  rw [P.nudge_adicValuation_le_exp_neg_iff]
  rcases eq_or_ne (f - algebraMap K F (P.evalAt f)) 0 with h0 | hne
  · exact Or.inl h0
  · right
    have hmem : f - algebraMap K F (P.evalAt f) ∈ P.toValuationSubring := sub_mem hf (P.algebraMap_mem' _)
    have h0 : 0 ≤ P.ord (f - algebraMap K F (P.evalAt f)) := P.ord_nonneg_of_mem hmem
    have hval : P.evalAt (f - algebraMap K F (P.evalAt f)) = 0 := by
      rw [P.nudge_evalAt_sub_algebraMap hP hf, sub_self]
    have hne0 : P.ord (f - algebraMap K F (P.evalAt f)) ≠ 0 := fun h => P.evalAt_ne_zero hP hne h hval
    omega

p2m_export "AlgebraicCurve.Place" "nudge_adicValuation_sub_evalAt_le"

theorem nudge [CharZero K] (hrat : ∀ w : Place K F, w.IsRational)
    (Q : Place K F) {r : ℕ} (Yf : Fin r → F) (hYQ : ∀ l, Yf l ∈ Q.toValuationSubring)
    (j : Fin r) (hj : Q.ord (Yf j - algebraMap K F (Q.evalAt (Yf j))) = 1)
    (T : Finset (Place K F)) (hT : ∀ P ∈ T, ∃ k, Yf k ∉ P.toValuationSubring) :
    ∃ c : Fin r → ℤ,
      Q.ord ((∑ l, ((c l : ℤ) : K) • Yf l) - algebraMap K F (Q.evalAt (∑ l, ((c l : ℤ) : K) • Yf l))) = 1 ∧
      ∀ P ∈ T, (∑ l, ((c l : ℤ) : K) • Yf l) ∈ P.toValuationSubring →
        P.evalAt (∑ l, ((c l : ℤ) : K) • Yf l) ≠ Q.evalAt (∑ l, ((c l : ℤ) : K) • Yf l) := by
  classical

  set g : Fin r → F := fun l => Yf l - algebraMap K F (Q.evalAt (Yf l)) with hgdef
  let fvec : (Fin r → K) →ₗ[K] F :=
    { toFun := fun c => ∑ l, c l • g l
      map_add' := fun a b => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hfvec : ∀ c : Fin r → K, fvec c = ∑ l, c l • g l := fun _ => rfl
  have hfvec_single : ∀ k : Fin r, fvec (Pi.single k 1) = g k := by
    intro k
    rw [hfvec, Finset.sum_eq_single k (fun l _ hl => by rw [Pi.single_eq_of_ne hl, zero_smul])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, one_smul]

  let W' : Place K F → ℤ → Submodule K F := fun P n =>
    { carrier := {f | P.adicValuation f ≤ WithZero.exp (-n)}
      add_mem' := fun {a b} ha hb => by
        show P.adicValuation (a + b) ≤ WithZero.exp (-n)
        exact le_trans (Valuation.map_add _ a b) (max_le ha hb)
      zero_mem' := by
        show P.adicValuation 0 ≤ WithZero.exp (-n)
        simp
      smul_mem' := fun a f hf => by
        show P.adicValuation (a • f) ≤ WithZero.exp (-n)
        rw [Algebra.smul_def, map_mul]
        calc P.adicValuation (algebraMap K F a) * P.adicValuation f
            ≤ 1 * WithZero.exp (-n) := mul_le_mul' (P.nudge_adicValuation_algebraMap_le_one a) hf
          _ = WithZero.exp (-n) := one_mul _ }
  have hW' : ∀ P n f, f ∈ W' P n ↔ f = 0 ∨ n ≤ P.ord f := fun P n f => by
    show P.adicValuation f ≤ WithZero.exp (-n) ↔ _
    exact P.nudge_adicValuation_le_exp_neg_iff f n
  let nT : Place K F → ℤ := fun P => if P = Q then 2 else 1
  have hQT : Q ∉ T := fun h => by
    obtain ⟨k, hk⟩ := hT Q h
    exact hk (hYQ k)

  have havoid : ∀ t ∈ insert Q T, ∃ c : Fin r → K, fvec c ∉ W' t (nT t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with htQ | htT
    · refine ⟨Pi.single j 1, ?_⟩
      rw [htQ, hfvec_single, hW', show nT Q = 2 from if_pos rfl]
      rintro (h0 | h2)
      · simp only [hgdef] at h0
        rw [h0, ord_zero] at hj
        exact zero_ne_one hj
      · simp only [hgdef] at h2
        omega
    · obtain ⟨k, hk⟩ := hT t htT
      refine ⟨Pi.single k 1, ?_⟩
      rw [hfvec_single, hW']
      have htQ' : t ≠ Q := by
        intro h
        rw [h] at htT
        exact hQT htT
      have hnT : nT t = 1 := if_neg htQ'
      rw [hnT]
      rintro (h0 | h1)
      · apply hk
        have : Yf k = g k + algebraMap K F (Q.evalAt (Yf k)) := by simp only [hgdef, sub_add_cancel]
        rw [this, h0, zero_add]
        exact t.algebraMap_mem' _
      · apply hk
        have hg0 : g k ≠ 0 := by
          intro h0
          rw [h0, ord_zero] at h1
          omega
        have hgk : g k ∈ t.toValuationSubring := t.mem_of_ord_nonneg hg0 (by omega)
        have : Yf k = g k + algebraMap K F (Q.evalAt (Yf k)) := by simp only [hgdef, sub_add_cancel]
        rw [this]
        exact add_mem hgk (t.algebraMap_mem' _)

  obtain ⟨c, hc⟩ := LinearMap.exists_int_forall_apply_notMem (insert Q T) (fun _ => fvec)
    (fun t => W' t (nT t)) havoid
  refine ⟨c, ?_, ?_⟩
  ·
    have hzQ : (∑ l, ((c l : ℤ) : K) • Yf l) ∈ Q.toValuationSubring :=
      Subring.sum_mem _ fun l _ => by
        rw [Algebra.smul_def]; exact mul_mem (Q.algebraMap_mem' _) (hYQ l)
    have hval : Q.evalAt (∑ l, ((c l : ℤ) : K) • Yf l) = ∑ l, ((c l : ℤ) : K) * Q.evalAt (Yf l) :=
      Q.c3e_evalAt_sum_smul (hrat Q) Finset.univ Yf (fun l => ((c l : ℤ) : K)) (fun l _ => hYQ l)
    have hfc : fvec (fun l => ((c l : ℤ) : K)) = ∑ l, ((c l : ℤ) : K) • g l := rfl
    have hG : (∑ l, ((c l : ℤ) : K) • Yf l) - algebraMap K F (Q.evalAt (∑ l, ((c l : ℤ) : K) • Yf l))
        = fvec (fun l => ((c l : ℤ) : K)) := by
      rw [hfc, hval, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hgdef, smul_sub, map_mul, Algebra.smul_def, mul_sub]
    rw [hG]
    have hnot : fvec (fun l => ((c l : ℤ) : K)) ∉ W' Q (nT Q) := hc Q (Finset.mem_insert_self Q T)
    have hnT : nT Q = 2 := if_pos rfl
    rw [hnT, hW'] at hnot
    push Not at hnot
    have hin : fvec (fun l => ((c l : ℤ) : K)) ∈ W' Q 1 := by
      rw [hfc]
      refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
      show Q.adicValuation (g l) ≤ WithZero.exp (-(1 : ℤ))
      exact Q.nudge_adicValuation_sub_evalAt_le (hrat Q) (hYQ l)
    rw [hW'] at hin
    rcases hin with h0 | h1
    · exact absurd h0 hnot.1
    · have := hnot.2; omega
  ·
    intro P hPT hzP hPQ
    have hnot : fvec (fun l => ((c l : ℤ) : K)) ∉ W' P (nT P) := hc P (Finset.mem_insert_of_mem hPT)
    have hPQ' : P ≠ Q := by
      intro h
      rw [h] at hPT
      exact hQT hPT
    have hnT : nT P = 1 := if_neg hPQ'
    rw [hnT] at hnot
    apply hnot
    have hval : Q.evalAt (∑ l, ((c l : ℤ) : K) • Yf l) = ∑ l, ((c l : ℤ) : K) * Q.evalAt (Yf l) :=
      Q.c3e_evalAt_sum_smul (hrat Q) Finset.univ Yf (fun l => ((c l : ℤ) : K)) (fun l _ => hYQ l)
    have hfc : fvec (fun l => ((c l : ℤ) : K)) = ∑ l, ((c l : ℤ) : K) • g l := rfl
    have hG : fvec (fun l => ((c l : ℤ) : K))
        = (∑ l, ((c l : ℤ) : K) • Yf l) - algebraMap K F (P.evalAt (∑ l, ((c l : ℤ) : K) • Yf l)) := by
      rw [hPQ, hfc, hval, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hgdef, smul_sub, map_mul, Algebra.smul_def, mul_sub]
    show P.adicValuation (fvec (fun l => ((c l : ℤ) : K))) ≤ WithZero.exp (-(1 : ℤ))
    rw [hG]
    exact P.nudge_adicValuation_sub_evalAt_le (hrat P) hzP

theorem nudge_evalAt_add_intCast_smul (P : Place K F) (hP : P.IsRational) {f w : F}
    (hf : f ∈ P.toValuationSubring) (hw : w ∈ P.toValuationSubring) (n : ℤ) :
    P.evalAt (f + ((n : ℤ) : K) • w) = P.evalAt f + (n : K) * P.evalAt w := by
  have hsm : ((n : ℤ) : K) • w ∈ P.toValuationSubring := by
    rw [Algebra.smul_def]
    exact mul_mem (P.algebraMap_mem' _) hw
  rw [P.nudge_evalAt_add hP hf hsm, Algebra.smul_def, P.evalAt_mul hP (P.algebraMap_mem' _) hw,
    P.evalAt_algebraMap]

theorem c3e_lambda [CharZero K] (hrat : ∀ w : Place K F, w.IsRational)
    (Q : Place K F) (Φ : Finset (Place K F)) {r : ℕ} (Yf : Fin r → F) (w : F)
    (hYQ : ∀ l, Yf l ∈ Q.toValuationSubring) (hwQ : w ∈ Q.toValuationSubring)
    (hYP : ∀ P ∈ Φ, ∀ l, Yf l ∈ P.toValuationSubring) (hwP : ∀ P ∈ Φ, w ∈ P.toValuationSubring)
    (hsep : ∀ P ∈ Φ, P.evalAt w ≠ Q.evalAt w) :
    ∃ lam : Fin r → ℤ, ∀ P ∈ Φ, ∀ l,
      P.evalAt (Yf l + ((lam l : ℤ) : K) • w) ≠ Q.evalAt (Yf l + ((lam l : ℤ) : K) • w) := by
  classical

  have hval : ∀ (P : Place K F), w ∈ P.toValuationSubring → ∀ {f : F}, f ∈ P.toValuationSubring →
      ∀ lam : ℤ, P.evalAt (f + ((lam : ℤ) : K) • w) = P.evalAt f + (lam : K) * P.evalAt w := by
    intro P hw f hf lam
    rw [P.c3e_evalAt_add (hrat P) hf
        (by simpa only [Algebra.smul_def] using mul_mem (P.algebraMap_mem' (lam : K)) hw),
      P.c3e_evalAt_smul (hrat P) _ hw]

  have key : ∀ l, ∃ lam : ℤ, ∀ P ∈ Φ,
      P.evalAt (Yf l) + (lam : K) * P.evalAt w ≠ Q.evalAt (Yf l) + (lam : K) * Q.evalAt w := by
    intro l
    obtain ⟨lam, hlam⟩ := Infinite.exists_notMem_finset
      ((Φ.image fun P => -(P.evalAt (Yf l) - Q.evalAt (Yf l)) / (P.evalAt w - Q.evalAt w)).preimage
        (Int.cast : ℤ → K) Int.cast_injective.injOn)
    refine ⟨lam, fun P hP h => hlam ?_⟩
    rw [Finset.mem_preimage, Finset.mem_image]
    refine ⟨P, hP, ?_⟩
    rw [div_eq_iff (sub_ne_zero.mpr (hsep P hP))]
    linear_combination -h
  choose lam hlam using key
  refine ⟨lam, fun P hP l => ?_⟩
  rw [hval P (hwP P hP) (hYP P hP l), hval Q hwQ (hYQ l)]
  exact hlam l P hP

end generic
end AlgebraicCurve.Place

theorem transcendental_of_not_mem_range_algebraMap {K F : Type*} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] {f : F} (hf : f ∉ Set.range (algebraMap K F)) : Transcendental K f := by
  intro halg
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one K f
    (IsAlgClosed.degree_eq_one_of_irreducible (k := K) (minpoly.irreducible halg.isIntegral)))
  exact hf ⟨c, hc⟩

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "pivotIndex evalVec chordVec Place Place.ord_zero HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.evalAt_one"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg adicValuation adicValuation_ne_zero adicValuation_coe ord ord_zero ord_mul ord_inv ord_coe_unit algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt evalAt_one derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne eval_leadingCoeff_ne_zero_of_forall_mem_toValuationSubring isRational_iff_deg_eq_one ord_nonneg_of_mem mem_of_ord_nonneg evalAt_mul evalAt_algebraMap evalAt_ne_zero"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"
section smul_generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem c3e_smul_mem (v : Place K F) (c : K) {f : F} (hf : f ∈ v.toValuationSubring) :
    c • f ∈ v.toValuationSubring := by
  rw [Algebra.smul_def]
  exact mul_mem (v.algebraMap_mem' _) hf

theorem c3e_sum_single_one_smul {r : ℕ} (Yf : Fin r → F) (j : Fin r) :
    ∑ l, (((Pi.single j (1 : ℤ) : Fin r → ℤ) l : ℤ) : K) • Yf l = Yf j := by
  classical
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, Int.cast_one, one_smul]
  · intro l _ hlj
    rw [Pi.single_eq_of_ne hlj, Int.cast_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem c3e_sum_zero_smul {r : ℕ} (Yf : Fin r → F) :
    ∑ l, (((0 : Fin r → ℤ) l : ℤ) : K) • Yf l = 0 := by
  simp

theorem c3e_sum_snoc_single_smul_snoc {r : ℕ} (Yf : Fin r → F) (y : F) (l : Fin r) :
    ∑ k : Fin (r + 1), (((Fin.snoc (Pi.single l (1 : ℤ) : Fin r → ℤ) (0 : ℤ) : Fin (r + 1) → ℤ) k : ℤ) : K) •
      (Fin.snoc Yf y : Fin (r + 1) → F) k = Yf l := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Int.cast_zero, zero_smul, add_zero]
  exact c3e_sum_single_one_smul Yf l

theorem c3e_add_smul_sum_eq {r : ℕ} (Yf : Fin r → F) (d : Fin r → ℤ) (lam : ℤ) (l : Fin r) :
    Yf l + ((lam : ℤ) : K) • (∑ l', ((d l' : ℤ) : K) • Yf l')
      = ∑ l', (((Pi.single l (1 : ℤ) : Fin r → ℤ) l' + lam * d l' : ℤ) : K) • Yf l' := by
  classical
  rw [← c3e_sum_single_one_smul (K := K) Yf l, Algebra.smul_def ((lam : ℤ) : K), Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [Int.cast_add, Int.cast_mul, add_smul, Algebra.smul_def (((lam : ℤ) : K) * ((d l' : ℤ) : K)) (Yf l'),
    map_mul, mul_assoc, ← Algebra.smul_def ((d l' : ℤ) : K) (Yf l')]

theorem c3e_sum_snoc_single_neg_smul {r : ℕ} (Yf : Fin r → F) (w : F) (lam : Fin r → ℤ) (l : Fin r) :
    ∑ k : Fin (r + 1), (((Fin.snoc (Pi.single l (1 : ℤ) : Fin r → ℤ) (-(lam l)) : Fin (r + 1) → ℤ) k : ℤ) : K) •
      (Fin.snoc (fun l' => Yf l' + ((lam l' : ℤ) : K) • w) w : Fin (r + 1) → F) k = Yf l := by
  classical
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [c3e_sum_single_one_smul (fun l' => Yf l' + ((lam l' : ℤ) : K) • w) l, Int.cast_neg, neg_smul,
    add_neg_cancel_right]

theorem c3e_sum_single_sub_single_smul {r : ℕ} (v : Fin r → F) (i j : Fin r) (_hj : j ≠ i) (c : K) :
    ∑ l, ((Pi.single i c - Pi.single j 1 : Fin r → K) l) • v l = algebraMap K F c * v i - v j := by
  classical
  simp only [Pi.sub_apply, Pi.single_apply, sub_smul, ite_smul, zero_smul, one_smul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Algebra.smul_def]

private theorem _root_.AlgebraicCurve.Place.c3e_mul_inv_mem_of_forall_ord_le (v : Place K F) {r : ℕ} (s : Fin r → F) (i : Fin r) (hsi : s i ≠ 0)
    (hle : ∀ j, v.ord (s i) ≤ v.ord (s j)) (l : Fin r) : s l * (s i)⁻¹ ∈ v.toValuationSubring := by
  by_cases hsl : s l = 0
  · rw [hsl, zero_mul]
    exact zero_mem _
  · apply v.mem_of_ord_nonneg (mul_ne_zero hsl (inv_ne_zero hsi))
    rw [v.ord_mul hsl (inv_ne_zero hsi), v.ord_inv]
    have := hle l
    omega

p2m_export "AlgebraicCurve.Place" "c3e_mul_inv_mem_of_forall_ord_le"
end smul_generic
end AlgebraicCurve.Place

namespace ModularCurve
p2m_export "ModularCurve" "IsEmbBasis modularFunctionFieldBar JZero JZero.chordVec_ne_zero_of_ne hasPrincipalDivisors_modularFunctionFieldBar_unconditional deg_eq_one_modularFunctionFieldBar exists_transcendental_finiteDimensional_modularFunctionFieldBar"
namespace JZero
p2m_export "ModularCurve.JZero" "exists_ord_div_sub_evalAt_eq_one chordVec_ne_zero_of_ne exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero"
p2m_open "ModularCurve.JZero ModularCurve"

local notation "𝕂" => AlgebraicClosure ℚ

section
variable (N : ℕ) [NeZero N]

theorem c3e_isRational (w : Place 𝕂 (modularFunctionFieldBar N)) : w.IsRational :=
  (w.isRational_iff_deg_eq_one).mpr (deg_eq_one_modularFunctionFieldBar N w)

variable {N}

theorem c3e_div_mem {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (i : Fin r)
    (P : Place 𝕂 (modularFunctionFieldBar N)) (hP : ∀ j, P.ord (s i) ≤ P.ord (s j)) (l : Fin r) :
    s l * (s i)⁻¹ ∈ P.toValuationSubring := by
  have hl : s l ≠ 0 := hs.1.ne_zero l
  have hi : s i ≠ 0 := hs.1.ne_zero i
  refine P.mem_of_ord_nonneg (mul_ne_zero hl (inv_ne_zero hi)) ?_
  rw [P.ord_mul hl (inv_ne_zero hi), P.ord_inv]
  have := hP l
  omega

theorem c3e_transcendental_div {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (i j : Fin r) (hj : j ≠ i) : Transcendental 𝕂 (s j * (s i)⁻¹) := by
  classical
  refine transcendental_of_not_mem_range_algebraMap ?_
  rintro ⟨c, hc⟩
  have hi : s i ≠ 0 := hs.1.ne_zero i
  have hsum : ∑ l, ((Pi.single i c - Pi.single j 1 : Fin r → 𝕂) l) • s l = 0 := by
    rw [Place.c3e_sum_single_sub_single_smul s i j hj c, hc, inv_mul_cancel_right₀ hi, sub_self]
  have h := Fintype.linearIndependent_iff.mp hs.1 _ hsum j
  rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hj, zero_sub, neg_eq_zero] at h
  exact one_ne_zero h

theorem c3e_roundOne_bad_finite {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (i : Fin r) (u : Fin (r + 1) → modularFunctionFieldBar N)
    (hu : ∀ (P : Place 𝕂 (modularFunctionFieldBar N)), (∀ j, P.ord (s i) ≤ P.ord (s j)) →
      ∀ k, u k ∈ P.toValuationSubring)
    (G : {j : Fin r // j ≠ i} → Fin (r + 1) → 𝕂[X][Y])
    (hh : ∀ (j : {j : Fin r // j ≠ i}) (k : Fin (r + 1)),
      ((derivative (G j k)).map (mapRingHom (algebraMap 𝕂 (modularFunctionFieldBar N)))).evalEval
        (s j * (s i)⁻¹) (u k) ≠ 0) :
    {Q : Place 𝕂 (modularFunctionFieldBar N) | (∀ j, Q.ord (s i) ≤ Q.ord (s j)) ∧
      ∀ j : {j : Fin r // j ≠ i},
        ¬ (Q.ord (s j * (s i)⁻¹ - algebraMap 𝕂 (modularFunctionFieldBar N) (Q.evalAt (s j * (s i)⁻¹))) = 1 ∧
            ∀ k, (derivative (G j k)).evalEval (Q.evalAt (s j * (s i)⁻¹)) (Q.evalAt (u k)) ≠ 0)}.Finite := by
  classical
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hrat := c3e_isRational N

  refine (Set.finite_iUnion fun p : {j : Fin r // j ≠ i} × Fin (r + 1) =>
    Place.c3e_finite_setOf_ord_ne_zero (K := 𝕂) (hh p.1 p.2)).subset ?_
  rintro Q ⟨hQi, hQbad⟩

  obtain ⟨j₀, hj₀⟩ := exists_ord_div_sub_evalAt_eq_one N s hs Q i hQi
  have hj₀i : j₀ ≠ i := by
    rintro rfl
    rw [mul_inv_cancel₀ (hs.1.ne_zero _), Place.evalAt_one, map_one, sub_self, Place.ord_zero] at hj₀
    exact zero_ne_one hj₀

  have hk' := hQbad ⟨j₀, hj₀i⟩
  rw [not_and] at hk'
  obtain ⟨k, hk⟩ := not_forall.mp (hk' hj₀)
  have hk0 : (derivative (G ⟨j₀, hj₀i⟩ k)).evalEval (Q.evalAt (s j₀ * (s i)⁻¹)) (Q.evalAt (u k)) = 0 :=
    not_not.mp hk
  rw [Set.mem_iUnion]
  refine ⟨(⟨j₀, hj₀i⟩, k), ?_⟩
  have hreg := Q.c3e_evalEval_mem (derivative (G ⟨j₀, hj₀i⟩ k)) (c3e_div_mem s hs i Q hQi j₀) (hu Q hQi k)
  have hval : Q.evalAt (((derivative (G ⟨j₀, hj₀i⟩ k)).map (mapRingHom (algebraMap 𝕂 (modularFunctionFieldBar N)))).evalEval
      (s j₀ * (s i)⁻¹) (u k)) = 0 := by
    rw [Q.c3e_evalAt_evalEval (hrat Q) _ (c3e_div_mem s hs i Q hQi j₀) (hu Q hQi k)]
    exact hk0
  exact ne_of_gt (Q.c3e_ord_pos_of_evalAt_eq_zero (hrat Q) (hh ⟨j₀, hj₀i⟩ k) hreg hval)

theorem c3e_nudge {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (i : Fin r)
    (Q : Place 𝕂 (modularFunctionFieldBar N)) (hQ : ∀ j, Q.ord (s i) ≤ Q.ord (s j)) :
    ∃ cz : Fin r → ℤ,
      Q.ord ((∑ l, ((cz l : ℤ) : 𝕂) • (s l * (s i)⁻¹))
        - algebraMap 𝕂 (modularFunctionFieldBar N) (Q.evalAt (∑ l, ((cz l : ℤ) : 𝕂) • (s l * (s i)⁻¹)))) = 1 ∧
      ∀ P : Place 𝕂 (modularFunctionFieldBar N),
        (∑ l, ((cz l : ℤ) : 𝕂) • (s l * (s i)⁻¹)) ∈ P.toValuationSubring →
        P.evalAt (∑ l, ((cz l : ℤ) : 𝕂) • (s l * (s i)⁻¹)) = Q.evalAt (∑ l, ((cz l : ℤ) : 𝕂) • (s l * (s i)⁻¹)) →
        ∀ j, P.ord (s i) ≤ P.ord (s j) := by
  classical
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hrat := c3e_isRational N
  have hs0 : ∀ l, s l ≠ 0 := fun l => hs.1.ne_zero l
  have hYQ : ∀ l, s l * (s i)⁻¹ ∈ Q.toValuationSubring := fun l => c3e_div_mem s hs i Q hQ l

  obtain ⟨j, hj⟩ := exists_ord_div_sub_evalAt_eq_one N s hs Q i hQ

  have hTfin : {P : Place 𝕂 (modularFunctionFieldBar N) | ∃ l, s l * (s i)⁻¹ ∉ P.toValuationSubring}.Finite := by
    refine ((Set.finite_iUnion fun l : Fin r =>
      Place.c3e_finite_setOf_ord_ne_zero (K := 𝕂) (hs0 l)).union
        (Place.c3e_finite_setOf_ord_ne_zero (K := 𝕂) (hs0 i))).subset ?_
    rintro P ⟨l, hl⟩
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hcon
    push Not at hcon
    obtain ⟨hall, hi0⟩ := hcon
    apply hl
    refine P.mem_of_ord_nonneg (mul_ne_zero (hs0 l) (inv_ne_zero (hs0 i))) ?_
    rw [P.ord_mul (hs0 l) (inv_ne_zero (hs0 i)), P.ord_inv, hall l, hi0]
    omega
  have hT : ∀ P ∈ hTfin.toFinset, ∃ k, s k * (s i)⁻¹ ∉ P.toValuationSubring :=
    fun P hP => hTfin.mem_toFinset.mp hP
  obtain ⟨c, hc1, hc2⟩ := Place.nudge hrat Q (fun l => s l * (s i)⁻¹) hYQ j hj hTfin.toFinset hT
  refine ⟨c, hc1, ?_⟩
  intro P hzP hPQ
  by_contra hcon
  push Not at hcon
  obtain ⟨j', hj'⟩ := hcon
  have hPT : P ∈ hTfin.toFinset := by
    refine hTfin.mem_toFinset.mpr ⟨j', fun hmem => ?_⟩
    have h0 := P.ord_nonneg_of_mem hmem
    rw [P.ord_mul (hs0 j') (inv_ne_zero (hs0 i)), P.ord_inv] at h0
    omega
  exact hc2 P hPT hzP hPQ

end

end ModularCurve.JZero

namespace ModularCurve p2m_export "ModularCurve" "IsEmbBasis modularFunctionFieldBar JZero JZero.chordVec_ne_zero_of_ne hasPrincipalDivisors_modularFunctionFieldBar_unconditional deg_eq_one_modularFunctionFieldBar exists_transcendental_finiteDimensional_modularFunctionFieldBar" namespace JZero p2m_export "ModularCurve.JZero" "exists_ord_div_sub_evalAt_eq_one chordVec_ne_zero_of_ne exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero" end ModularCurve.JZero
p2m_open_scoped "ModularCurve ModularCurve.JZero" in

theorem ModularCurve.JZero.sep_exists_evalAt_mul_inv_ne (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (hrat : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.IsRational)
    (i : Fin r) {P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hPQ : P ≠ Q)
    (hP : ∀ j, P.ord (s i) ≤ P.ord (s j)) (hQ : ∀ j, Q.ord (s i) ≤ Q.ord (s j)) :
    ∃ l, P.evalAt (s l * (s i)⁻¹) ≠ Q.evalAt (s l * (s i)⁻¹) := by
  classical
  by_contra hall
  push Not at hall
  apply ModularCurve.JZero.chordVec_ne_zero_of_ne N s hs P Q hPQ
  have hr : 0 < r := Fin.pos i
  obtain ⟨hli, -⟩ := hs
  have hs0 : ∀ l, s l ≠ 0 := fun l => hli.ne_zero l
  have key : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ j, v.ord (s i) ≤ v.ord (s j)) →
      ∃ u : AlgebraicClosure ℚ, ∀ l, evalVec s v l = v.evalAt (s l * (s i)⁻¹) * u := by
    intro v hv
    have hex : ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := ⟨i, hv⟩
    have hkspec : ∀ j, v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
      rw [pivotIndex, dif_pos hex]
      exact Classical.choose_spec hex
    refine ⟨v.evalAt (s i * (s (pivotIndex s v hr))⁻¹), fun l => ?_⟩
    have hYl : s l * (s i)⁻¹ ∈ v.toValuationSubring :=
      v.c3e_mul_inv_mem_of_forall_ord_le s i (hs0 i) hv l
    have hU : s i * (s (pivotIndex s v hr))⁻¹ ∈ v.toValuationSubring :=
      v.c3e_mul_inv_mem_of_forall_ord_le s (pivotIndex s v hr) (hs0 _) hkspec i
    rw [← v.evalAt_mul (hrat v) hYl hU]
    simp only [evalVec, dif_pos hr]
    congr 1
    rw [mul_assoc, inv_mul_cancel_left₀ (hs0 i)]
  obtain ⟨uP, huP⟩ := key P hP
  obtain ⟨uQ, huQ⟩ := key Q hQ
  funext p
  simp only [chordVec, huP, huQ, hall, Pi.zero_apply]
  ring

p2m_open_scoped "ModularCurve ModularCurve.JZero" in

theorem ModularCurve.JZero.sep_exists_int_forall_evalAt_ne (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (hrat : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.IsRational)
    (i : Fin r) (Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hQ : ∀ j, Q.ord (s i) ≤ Q.ord (s j))
    (Φ : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) (hΦQ : ∀ P ∈ Φ, P ≠ Q)
    (hΦ : ∀ P ∈ Φ, ∀ j, P.ord (s i) ≤ P.ord (s j)) :
    ∃ d : Fin r → ℤ, ∀ P ∈ Φ,
      P.evalAt (∑ l, (d l : AlgebraicClosure ℚ) • (s l * (s i)⁻¹)) ≠ Q.evalAt (∑ l, (d l : AlgebraicClosure ℚ) • (s l * (s i)⁻¹)) := by
  classical
  obtain ⟨hli, -⟩ := id hs
  have hsi : s i ≠ 0 := hli.ne_zero i

  let f : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      (Fin r → AlgebraicClosure ℚ) →ₗ[AlgebraicClosure ℚ] AlgebraicClosure ℚ :=
    fun P => ∑ l, (P.evalAt (s l * (s i)⁻¹) - Q.evalAt (s l * (s i)⁻¹)) • LinearMap.proj l
  have hfapply : ∀ P (c : Fin r → AlgebraicClosure ℚ),
      f P c = ∑ l, c l * P.evalAt (s l * (s i)⁻¹) - ∑ l, c l * Q.evalAt (s l * (s i)⁻¹) := by
    intro P c
    simp only [f, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.coe_proj,
      Function.eval, smul_eq_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hf0 : ∀ P ∈ Φ, f P ≠ 0 := by
    intro P hP hzero
    obtain ⟨l, hl⟩ := ModularCurve.JZero.sep_exists_evalAt_mul_inv_ne N s hs hrat i (hΦQ P hP) (hΦ P hP) hQ
    have h1 := congrArg (fun g => g (Pi.single l 1)) hzero
    simp only [hfapply, LinearMap.zero_apply, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact hl (sub_eq_zero.mp h1)
  obtain ⟨d, hd⟩ := LinearMap.exists_int_forall_apply_ne Φ f (fun _ => 0) hf0
  refine ⟨d, fun P hP h => hd P hP ?_⟩
  rw [hfapply,
    ← P.c3e_evalAt_sum_smul (hrat P) Finset.univ _ _ (fun l _ => P.c3e_mul_inv_mem_of_forall_ord_le s i hsi (hΦ P hP) l),
    ← Q.c3e_evalAt_sum_smul (hrat Q) Finset.univ _ _ (fun l _ => Q.c3e_mul_inv_mem_of_forall_ord_le s i hsi hQ l),
    h, sub_self]

p2m_open "ModularCurve.JZero P2MW.S_ModularCurve_JZero_exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero.ModularCurve.JZero AlgebraicCurve.Place P2MW.S_ModularCurve_JZero_exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero.AlgebraicCurve.Place"

local notation "𝕂" => AlgebraicClosure ℚ

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution
    (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (i : Fin r) :
    ∃ (m : ℕ) (z : Fin m → modularFunctionFieldBar N)
      (u : Fin m → Fin (r + 1) → modularFunctionFieldBar N)
      (G : Fin m → Fin (r + 1) → Polynomial (Polynomial (AlgebraicClosure ℚ)))
      (cz : Fin m → Fin r → ℤ) (cu : Fin m → Fin (r + 1) → Fin r → ℤ)
      (M : Fin m → Fin r → Fin (r + 1) → ℤ),
      (∀ a, z a = ∑ l, (cz a l : AlgebraicClosure ℚ) • (s l * (s i)⁻¹)) ∧
      (∀ a k, u a k = ∑ l, (cu a k l : AlgebraicClosure ℚ) • (s l * (s i)⁻¹)) ∧
      (∀ a l, s l * (s i)⁻¹ = ∑ k, (M a l k : AlgebraicClosure ℚ) • u a k) ∧
      (∀ a k, Irreducible (G a k)) ∧
      (∀ a k n n', IsIntegral ℤ (((G a k).coeff n).coeff n')) ∧
      (∀ a k, ((G a k).map (Polynomial.mapRingHom
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))).evalEval (z a) (u a k) = 0) ∧
      (∀ a k, ((Polynomial.derivative (G a k)).map (Polynomial.mapRingHom
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))).evalEval (z a) (u a k) ≠ 0) ∧
      (∀ Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ j, Q.ord (s i) ≤ Q.ord (s j)) →
        ∃ a, Q.ord (z a - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (Q.evalAt (z a))) = 1 ∧
          ∀ k, (Polynomial.derivative (G a k)).evalEval (Q.evalAt (z a)) (Q.evalAt (u a k)) ≠ 0) := by
  classical
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨x₀, -, hx₀⟩ := exists_transcendental_finiteDimensional_modularFunctionFieldBar N
  haveI := hx₀

  set u₁ : Fin (r + 1) → modularFunctionFieldBar N := Fin.snoc (fun l => s l * (s i)⁻¹) 0 with hu₁def
  have hu₁_last : u₁ (Fin.last r) = 0 := by rw [hu₁def, Fin.snoc_last]
  have hu₁_cast : ∀ l : Fin r, u₁ l.castSucc = s l * (s i)⁻¹ := fun l => by rw [hu₁def, Fin.snoc_castSucc]
  have hu₁ : ∀ P : Place 𝕂 (modularFunctionFieldBar N), (∀ j, P.ord (s i) ≤ P.ord (s j)) →
      ∀ k, u₁ k ∈ P.toValuationSubring := by
    intro P hP k
    refine Fin.lastCases ?_ (fun l => ?_) k
    · rw [hu₁_last]
      exact zero_mem _
    · rw [hu₁_cast]
      exact c3e_div_mem s hs i P hP l
  have hG1 := fun (j : {j : Fin r // j ≠ i}) (k : Fin (r + 1)) =>
    Transcendental.exists_irreducible_isIntegral_evalEval_eq_zero_and_derivative_ne_zero x₀
      (c3e_transcendental_div s hs i j.1 j.2) (u₁ k)
  choose G₁ hG₁irr hG₁int hG₁rel hG₁der using hG1

  have hbad := c3e_roundOne_bad_finite s hs i u₁ hu₁ G₁ hG₁der
  set B := hbad.toFinset with hBdef

  have hchild := fun Q : B =>
    exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero N s hs i Q.1 ((hbad.mem_toFinset.mp Q.2).1)
  choose z₂ u₂ G₂ cz₂ cu₂ M₂ hz₂ hu₂ hM₂ hG₂irr hG₂int hG₂rel hG₂der he₂ hgood₂ using hchild

  set zι : ({j : Fin r // j ≠ i} ⊕ (B : Type _)) → modularFunctionFieldBar N :=
    Sum.elim (fun j => s j.1 * (s i)⁻¹) z₂ with hzι
  set uι : ({j : Fin r // j ≠ i} ⊕ (B : Type _)) → Fin (r + 1) → modularFunctionFieldBar N :=
    Sum.elim (fun _ => u₁) u₂ with huι
  set Gι : ({j : Fin r // j ≠ i} ⊕ (B : Type _)) → Fin (r + 1) → 𝕂[X][Y] := Sum.elim G₁ G₂ with hGι
  set czι : ({j : Fin r // j ≠ i} ⊕ (B : Type _)) → Fin r → ℤ :=
    Sum.elim (fun j => Pi.single j.1 1) cz₂ with hczι
  set cuι : ({j : Fin r // j ≠ i} ⊕ (B : Type _)) → Fin (r + 1) → Fin r → ℤ :=
    Sum.elim (fun _ => Fin.snoc (fun l => (Pi.single l 1 : Fin r → ℤ)) 0) cu₂ with hcuι
  set Mι : ({j : Fin r // j ≠ i} ⊕ (B : Type _)) → Fin r → Fin (r + 1) → ℤ :=
    Sum.elim (fun _ l => Fin.snoc (Pi.single l 1 : Fin r → ℤ) 0) M₂ with hMι
  have h1 : ∀ t, zι t = ∑ l, (czι t l : 𝕂) • (s l * (s i)⁻¹) := by
    rintro (j | Q)
    · simp only [hzι, hczι, Sum.elim_inl]
      exact (Place.c3e_sum_single_one_smul (fun l => s l * (s i)⁻¹) j.1).symm
    · exact hz₂ Q
  have h2 : ∀ t k, uι t k = ∑ l, (cuι t k l : 𝕂) • (s l * (s i)⁻¹) := by
    rintro (j | Q) k
    · simp only [huι, hcuι, Sum.elim_inl]
      refine Fin.lastCases ?_ (fun l => ?_) k
      · rw [hu₁_last, Fin.snoc_last]
        exact (Place.c3e_sum_zero_smul (K := 𝕂) (fun l => s l * (s i)⁻¹)).symm
      · rw [hu₁_cast, Fin.snoc_castSucc]
        exact (Place.c3e_sum_single_one_smul (fun l => s l * (s i)⁻¹) l).symm
    · exact hu₂ Q k
  have h3 : ∀ t l, s l * (s i)⁻¹ = ∑ k, (Mι t l k : 𝕂) • uι t k := by
    rintro (j | Q) l
    · simp only [huι, hMι, Sum.elim_inl]
      rw [hu₁def]
      exact (Place.c3e_sum_snoc_single_smul_snoc (fun l => s l * (s i)⁻¹) 0 l).symm
    · exact hM₂ Q l
  have h4 : ∀ t k, Irreducible (Gι t k) := by
    rintro (j | Q) k
    · exact hG₁irr j k
    · exact hG₂irr Q k
  have h5 : ∀ t k n n', IsIntegral ℤ (((Gι t k).coeff n).coeff n') := by
    rintro (j | Q) k
    · exact hG₁int j k
    · exact hG₂int Q k
  have h6 : ∀ t k, ((Gι t k).map (mapRingHom (algebraMap 𝕂 (modularFunctionFieldBar N)))).evalEval
      (zι t) (uι t k) = 0 := by
    rintro (j | Q) k
    · exact hG₁rel j k
    · exact hG₂rel Q k
  have h7 : ∀ t k, ((derivative (Gι t k)).map (mapRingHom (algebraMap 𝕂 (modularFunctionFieldBar N)))).evalEval
      (zι t) (uι t k) ≠ 0 := by
    rintro (j | Q) k
    · exact hG₁der j k
    · exact hG₂der Q k

  have h8 : ∀ Q : Place 𝕂 (modularFunctionFieldBar N), (∀ j, Q.ord (s i) ≤ Q.ord (s j)) →
      ∃ t, Q.ord (zι t - algebraMap 𝕂 (modularFunctionFieldBar N) (Q.evalAt (zι t))) = 1 ∧
        ∀ k, (derivative (Gι t k)).evalEval (Q.evalAt (zι t)) (Q.evalAt (uι t k)) ≠ 0 := by
    intro Q hQ
    by_cases hgood : ∃ j : {j : Fin r // j ≠ i},
        Q.ord (s j.1 * (s i)⁻¹ - algebraMap 𝕂 (modularFunctionFieldBar N) (Q.evalAt (s j.1 * (s i)⁻¹))) = 1 ∧
          ∀ k, (derivative (G₁ j k)).evalEval (Q.evalAt (s j.1 * (s i)⁻¹)) (Q.evalAt (u₁ k)) ≠ 0
    · obtain ⟨j, hj⟩ := hgood
      exact ⟨Sum.inl j, hj⟩
    · have hQB : Q ∈ B := hbad.mem_toFinset.mpr ⟨hQ, fun j => (not_exists.mp hgood) j⟩
      exact ⟨Sum.inr ⟨Q, hQB⟩, he₂ ⟨Q, hQB⟩, hgood₂ ⟨Q, hQB⟩⟩

  set e := (Fintype.equivFin ({j : Fin r // j ≠ i} ⊕ (B : Type _))).symm with hedef
  refine ⟨Fintype.card ({j : Fin r // j ≠ i} ⊕ (B : Type _)),
    fun a => zι (e a), fun a => uι (e a), fun a => Gι (e a), fun a => czι (e a), fun a => cuι (e a),
    fun a => Mι (e a),
    fun a => h1 (e a), fun a => h2 (e a), fun a => h3 (e a), fun a => h4 (e a), fun a => h5 (e a),
    fun a => h6 (e a), fun a => h7 (e a), fun Q hQ => ?_⟩
  obtain ⟨t, ht⟩ := h8 Q hQ
  refine ⟨e.symm t, ?_⟩
  beta_reduce
  rw [Equiv.apply_symm_apply]
  exact ht

#print axioms solution

end S_ModularCurve_JZero_exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero
end P2MW
export P2MW.S_ModularCurve_JZero_exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero (solution)
