-- Prove2me | solution 1 for ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f009eda0-7a25-5e01-bd25-2c27cf8e8129

import Mathlib
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ModularCurve_NodeLocalized_exists_hasValue_nodeCoord_of_centred
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_modularEval_kroneckerRemainder
import Theorems.Thm_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_kroneckerCongruence
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728
import Theorems.Thm_ModularCurve_NodeLocalized_isUnit_evalAt_zero_of_gaussPair_of_isAlgClosed
import Theorems.Thm_ModularCurve_NodeLocalized_isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo"
p2m_attr_erase "instance" "instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of"
p2m_attr_erase "simp" "AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply"
p2m_attr_erase "simp" "ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false
set_option Elab.async false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve"

noncomputable section

namespace Ws23
namespace NodePlaceAPI

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing Polynomial"

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_of_ord_sub_pos {v : Place K F} {g : F} {c : K}
    (h : 0 < v.ord (g - algebraMap K F c)) : v.HasValue g c := by
  have hne : g - algebraMap K F c ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  have hmem : g - algebraMap K F c ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt hne h.le
  have hnu : ¬ IsUnit (⟨g - algebraMap K F c, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    have h0' : v.ord (g - algebraMap K F c) = 0 := h0
    rw [h0'] at h
    exact lt_irrefl _ h
  have hmax : (⟨g - algebraMap K F c, hmem⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact hnu
  have hres0 : residue v.toValuationSubring ⟨g - algebraMap K F c, hmem⟩ = algebraMap K v.ResidueField 0 := by
    rw [map_zero]
    exact (residue_eq_zero_iff _).mpr hmax
  have hd := hasValue_add (⟨hmem, hres0⟩ : v.HasValue (g - algebraMap K F c) 0) (v.hasValue_algebraMap c)
  rwa [sub_add_cancel, zero_add] at hd

theorem hasValue_congrRingEquiv {F' : Type*} [Field F'] [Algebra K F'] (e : F ≃+* F')
    (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a) (v : Place K F) {g : F} {c : K}
    (h : v.HasValue g c) : (Place.congrRingEquiv e he v).HasValue (e g) c := by
  obtain ⟨hg, hr⟩ := h
  let φ := Place.comapSymmRingEquiv e v.toValuationSubring
  have hg' : e g ∈ (Place.congrRingEquiv e he v).toValuationSubring := (φ ⟨g, hg⟩).2
  refine ⟨hg', ?_⟩
  have h1 : (⟨e g, hg'⟩ : (Place.congrRingEquiv e he v).toValuationSubring) = φ ⟨g, hg⟩ := rfl
  have h3 : φ (algebraMap K v.toValuationSubring c)
      = algebraMap K (Place.congrRingEquiv e he v).toValuationSubring c := by
    ext
    rw [Place.coe_comapSymmRingEquiv_apply, Place.coe_algebraMap, Place.coe_algebraMap]
    exact he c
  rw [h1, ← Place.residue_algebraMap, ← h3]
  have key : ∀ z : v.toValuationSubring,
      residue _ (φ z) = IsLocalRing.ResidueField.mapEquiv φ (residue _ z) := fun z => by
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  show residue _ (φ ⟨g, hg⟩) = residue _ (φ (algebraMap K v.toValuationSubring c))
  rw [key, key, hr, Place.residue_algebraMap]

theorem hasValue_placeOfPoint (a : K) (p : K[X]) :
    (RationalFunctionField.placeOfPoint K a).HasValue (algebraMap K[X] (RatFunc K) p) (p.eval a) := by
  let w := RationalFunctionField.heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)
  have hmem : algebraMap K[X] (RatFunc K) p ∈ (RationalFunctionField.placeOfPoint K a).toValuationSubring :=
    RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w p
  refine ⟨hmem, ?_⟩
  have hker : p - C (p.eval a) ∈ RingHom.ker (RationalFunctionField.residueOfHeightOneSpectrum K w) := by
    rw [RationalFunctionField.ker_residueOfHeightOneSpectrum,
      RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton, dvd_iff_isRoot]
    simp [IsRoot]
  rw [RingHom.mem_ker, map_sub, sub_eq_zero, RationalFunctionField.residueOfHeightOneSpectrum_apply,
    RationalFunctionField.residueOfHeightOneSpectrum_apply] at hker
  have hC : (⟨algebraMap K[X] (RatFunc K) (C (p.eval a)), RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w _⟩ :
        (RationalFunctionField.placeOfPoint K a).toValuationSubring)
      = algebraMap K (RationalFunctionField.placeOfPoint K a).toValuationSubring (p.eval a) := by
    ext
    rw [Place.coe_algebraMap, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  have hker' : residue (RationalFunctionField.placeOfPoint K a).toValuationSubring ⟨_, hmem⟩
      = residue (RationalFunctionField.placeOfPoint K a).toValuationSubring
          ⟨algebraMap K[X] (RatFunc K) (C (p.eval a)), RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w _⟩ :=
    hker
  rw [hker', hC, Place.residue_algebraMap]

end PlaceLemmas

end Ws23.NodePlaceAPI

namespace Ws23
namespace NodePlaceAPI

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing Polynomial ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve"

section PlaceLemmas2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.Ws23.NodePlaceAPI.evalAt_eq_of_hasValue' {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) : v.evalAt g = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap]

p2m_export "Ws23.NodePlaceAPI" "evalAt_eq_of_hasValue'"

theorem hasValue_pow {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) :
    v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      exact v.hasValue_one
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul h

end PlaceLemmas2

section JLine

variable (K : Type*) [Field K]

noncomputable def jC1 : ↥(modularFunctionFieldC K 1) := ⟨jqModC K, jqModC_mem K 1⟩

@[scoped simp] theorem coe_jC1 : ((jC1 K : ↥(modularFunctionFieldC K 1)) : LaurentSeries K) = jqModC K := rfl

theorem ratFuncEquivCharLOneC_X :
    ratFuncEquivCharLOneC K (algebraMap K[X] (RatFunc K) X) = jC1 K := by
  apply Subtype.ext
  rw [RatFunc.algebraMap_X, ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (jqModC K) (transcendental_jqModC K)

theorem ratFuncEquivCharLOneC_polynomial (p : K[X]) :
    ratFuncEquivCharLOneC K (algebraMap K[X] (RatFunc K) p) = Polynomial.aeval (jC1 K) p := by
  have hfun : ((ratFuncEquivCharLOneC K : RatFunc K →ₐ[K] ↥(modularFunctionFieldC K 1)).comp
      (IsScalarTower.toAlgHom K K[X] (RatFunc K))) = Polynomial.aeval (jC1 K) := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, Polynomial.aeval_X]
    exact ratFuncEquivCharLOneC_X K
  exact AlgHom.congr_fun hfun p

theorem hasValue_charLGeomPlaceOfPoint_aeval (a : K) (p : K[X]) :
    (charLGeomPlaceOfPoint K a).HasValue (Polynomial.aeval (jC1 K) p) (p.eval a) := by
  have h := hasValue_congrRingEquiv (K := K) (ratFuncEquivCharLOneC K).toRingEquiv
    (fun c => (ratFuncEquivCharLOneC K).commutes c) (RationalFunctionField.placeOfPoint K a)
    (hasValue_placeOfPoint a p)
  rw [← ratFuncEquivCharLOneC_polynomial]
  exact h

theorem hasValue_charLGeomPlaceOfPoint_jC1 (a : K) :
    (charLGeomPlaceOfPoint K a).HasValue (jC1 K) a := by
  simpa using hasValue_charLGeomPlaceOfPoint_aeval K a X

end JLine

end Ws23.NodePlaceAPI
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23"

namespace Ws23
namespace NodePlaceAPI

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve AlgebraicCurve.RationalFunctionField~ord_placeOfPoint_algebraMap IsLocalRing Polynomial ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve"

section Orders

variable {K : Type*} [Field K]

theorem ord_placeOfPoint_algebraMap_eq_mul (a : K) {q : K[X]} (hq : q ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q)
      = (rootMultiplicity a q : ℤ)
          * (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) := by
  obtain ⟨r, hr⟩ := pow_rootMultiplicity_dvd q a
  set m : ℕ := rootMultiplicity a q with hm
  have hXa : (X : K[X]) - C a ≠ 0 := X_sub_C_ne_zero a
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hq (by simpa using hr)
  have hndvd : ¬((X : K[X]) - C a) ∣ r := by
    intro ⟨s, hs⟩
    have : (X - C a) ^ (m + 1) ∣ q := ⟨s, by rw [hr, hs]; ring⟩
    have := (le_rootMultiplicity_iff hq).mpr this
    omega
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hr0' : algebraMap K[X] (RatFunc K) r ≠ 0 := (map_ne_zero_iff _ hinj).mpr hr0
  have hpow' : algebraMap K[X] (RatFunc K) ((X - C a) ^ m) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero m hXa)
  have hordr : (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) r) = 0 := by
    by_contra hcon
    apply hndvd
    have hmem := (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K)
      (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)) hr0).mp hcon
    rw [heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton] at hmem
    exact hmem
  calc (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q)
      = (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) ((X - C a) ^ m)
          * algebraMap K[X] (RatFunc K) r) := by rw [← map_mul, ← hr]
    _ = (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) ((X - C a) ^ m))
          + (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) r) :=
        (placeOfPoint K a).ord_mul hpow' hr0'
    _ = (placeOfPoint K a).ord ((algebraMap K[X] (RatFunc K) (X - C a)) ^ (m : ℤ)) := by
        rw [hordr, add_zero, map_pow, ← zpow_natCast]
    _ = (m : ℤ) * (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) :=
        (placeOfPoint K a).ord_zpow _ _

theorem ord_placeOfPoint_algebraMap (a : K) {q : K[X]} (hq : q ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q) = (rootMultiplicity a q : ℤ) := by
  rw [ord_placeOfPoint_algebraMap_eq_mul a hq, StandardAnnulus.ord_placeOfPoint_X_sub_C_self a, mul_one]

theorem ord_placeOfPoint_algebraMap' (a : K) (q : K[X]) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q) = (rootMultiplicity a q : ℤ) := by
  by_cases hq : q = 0
  · rw [hq, map_zero, Place.ord_zero, rootMultiplicity_zero, Nat.cast_zero]
  · exact ord_placeOfPoint_algebraMap a hq

variable (K)

theorem ord_charLGeomPlaceOfPoint_ratFuncEquiv (a : K) (f : RatFunc K) :
    (charLGeomPlaceOfPoint K a).ord (ratFuncEquivCharLOneC K f) = (placeOfPoint K a).ord f :=
  Place.ord_congrRingEquiv (ratFuncEquivCharLOneC K).toRingEquiv
    (fun c => (ratFuncEquivCharLOneC K).commutes c) (placeOfPoint K a) f

theorem ord_charLGeomPlaceOfPoint_aeval (a : K) (p : K[X]) :
    (charLGeomPlaceOfPoint K a).ord (Polynomial.aeval (jC1 K) p) = (rootMultiplicity a p : ℤ) := by
  rw [← ratFuncEquivCharLOneC_polynomial, ord_charLGeomPlaceOfPoint_ratFuncEquiv, ord_placeOfPoint_algebraMap']

end Orders
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

end Ws23.NodePlaceAPI
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.modularRedLocHom_mem CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem modularFunctionFieldC_one qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full NodeLocalized.exists_hasValue_nodeCoord_of_centred frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder frobNodePair_fst ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData frickeInvolutionBar_frickeInvolutionBar NodeLocalized.exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728 jWidth NodeLocalized.isUnit_evalAt_zero_of_gaussPair_of_isAlgClosed NodeLocalized.isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed"
namespace CharPReduction
p2m_export "ModularCurve.CharPReduction" "modularRedLocHom_mem coeffRed_coeff redRes redRes_apply redKer notMem_redKer_iff mem_localizedAtKer subring_le_localizedAtKer redLoc redRes_ne_zero_of_notMem redLoc_spec redLoc_coe constSeries modularRing jqModC_mem_modularRing jqNModC_mem_modularRing constSeries_mem_modularRing jqModC_mem_integralCoeffs modularRing_le_integralCoeffs modularLocalized modularRedLocHom"
p2m_open "ModularCurve.CharPReduction ModularCurve~coeffEmb_jq"

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

theorem gaussUnit_congr {x y : LaurentSeries L} (hxy : x = y)
    (h : ∃ hx : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, hx⟩ ≠ 0) :
    ∃ hy : y ∈ modularLocalized N A red, modularRedLocHom N A red ⟨y, hy⟩ ≠ 0 := by
  subst hxy
  exact h

theorem gaussUnit_one :
    ∃ h : (1 : LaurentSeries L) ∈ modularLocalized N A red, modularRedLocHom N A red ⟨1, h⟩ ≠ 0 := by
  refine ⟨one_mem _, ?_⟩
  have h1 : (⟨1, one_mem _⟩ : modularLocalized N A red) = 1 := rfl
  rw [h1, map_one]
  exact one_ne_zero

theorem gaussUnit_mul {x y : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0)
    (hy : ∃ h : y ∈ modularLocalized N A red, modularRedLocHom N A red ⟨y, h⟩ ≠ 0) :
    ∃ h : x * y ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x * y, h⟩ ≠ 0 := by
  obtain ⟨hx, hx0⟩ := hx
  obtain ⟨hy, hy0⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have hxy : (⟨x * y, mul_mem hx hy⟩ : modularLocalized N A red) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [hxy, map_mul]
  exact mul_ne_zero hx0 hy0

theorem gaussUnit_inv {x : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0) :
    ∃ h : x⁻¹ ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x⁻¹, h⟩ ≠ 0 := by
  obtain ⟨hx, hx0⟩ := hx
  obtain ⟨r, s, hs, hxs⟩ :=
    (mem_localizedAtKer A red (modularRing N A) (modularRing_le_integralCoeffs N A)).mp hx
  have hsne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) hs
  have hspec := redLoc_spec (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) ⟨x, hx⟩ hxs
  have hx0' : redLoc (A := A) (red := red) (R := modularRing N A)
      (hR := modularRing_le_integralCoeffs N A) ⟨x, hx⟩ ≠ 0 := hx0
  have hrne : redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) r ≠ 0 := by
    rw [← hspec]
    exact mul_ne_zero hx0' hsne
  have hr : r ∉ redKer A red (modularRing N A) (modularRing_le_integralCoeffs N A) :=
    (notMem_redKer_iff A red (modularRing N A) (modularRing_le_integralCoeffs N A)).mpr hrne
  have hxne : x ≠ 0 := by
    intro hx0
    apply hrne
    have hr0 : r = 0 := by
      apply Subtype.ext
      rw [← hxs, hx0, zero_mul]
      rfl
    rw [hr0, map_zero]
  have hinv : x⁻¹ * r = s := by
    rw [← hxs, ← mul_assoc, inv_mul_cancel₀ hxne, one_mul]
  have hmem : x⁻¹ ∈ modularLocalized N A red :=
    (mem_localizedAtKer A red (modularRing N A) (modularRing_le_integralCoeffs N A)).mpr ⟨s, r, hr, hinv⟩
  refine ⟨hmem, ?_⟩
  have hspec' := redLoc_spec (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) ⟨x⁻¹, hmem⟩ hinv
  intro hzero
  apply hsne
  have hzero' : redLoc (A := A) (red := red) (R := modularRing N A)
      (hR := modularRing_le_integralCoeffs N A) ⟨x⁻¹, hmem⟩ = 0 := hzero
  rw [← hspec', hzero', zero_mul]

theorem gaussUnit_pow {x : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0) (n : ℕ) :
    ∃ h : x ^ n ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x ^ n, h⟩ ≠ 0 := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact gaussUnit_one N A red
  | succ n ih =>
      rw [pow_succ]
      exact gaussUnit_mul N A red ih hx

theorem gaussUnit_zpow {x : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0) (n : ℤ) :
    ∃ h : x ^ n ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x ^ n, h⟩ ≠ 0 := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast]
      exact gaussUnit_pow N A red hx n
  | negSucc n =>
      rw [zpow_negSucc]
      exact gaussUnit_inv N A red (gaussUnit_pow N A red hx (n + 1))

end ModularCurve.CharPReduction
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap Place.deg Place.ord_zero Place.ord_mul Place.smulRingEquiv Place.coe_smulRingEquiv_apply Place.smul_toValuationSubring Place.ord_smul Place.smulResidueAlgEquiv Place.residue_algebraMap GluedPic0 Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.heightOneSpectrumOfIrreducible RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum RationalFunctionField.residueOfHeightOneSpectrum RationalFunctionField.residueOfHeightOneSpectrum_apply RationalFunctionField.ker_residueOfHeightOneSpectrum RationalFunctionField.placeOfPoint Place.comapSymmRingEquiv Place.coe_comapSymmRingEquiv_apply Place.congrRingEquiv Place.ord_congrRingEquiv ComponentChart Annulus ConstantReduction ConstantReduction.ord_algebraMap Place.evalAt GaussReduction.ord_nonneg_of_mem_gen StandardAnnulus.ord_placeOfPoint_X_sub_C_self Place.mem_smul_iff' Place.hasValue_smul Place.isRational_smul Place.evalAt_smul"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg ord ord_zero ord_mul ord_coe_unit ord_zpow smulRingEquiv coe_smulRingEquiv_apply smul_toValuationSubring ord_smul smulResidueAlgEquiv algebraMap_mem' toValuationSubring residue_algebraMap HasValue hasValue_one hasValue_algebraMap ord_ofHeightOneSpectrum_ne_zero_iff comapSymmRingEquiv coe_comapSymmRingEquiv_apply congrRingEquiv ord_congrRingEquiv IsRational residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_mul_of_mem evalAt_algebraMap_eq mem_toValuationSubring_of_ord_nonneg_alt mem_smul_iff' hasValue_smul isRational_smul evalAt_smul"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

theorem evalAt_eq_of_hasValue' {g : F} {a : K} (h : v.HasValue g a) : v.evalAt g = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap]

theorem hasValue_pow_of_hasValue {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      exact v.hasValue_one
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul h

theorem hasValue_zpow_of_hasValue {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) (n : ℤ) :
    v.HasValue (g ^ n) (a ^ n) := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
      exact hasValue_pow_of_hasValue h n
  | negSucc n =>
      rw [zpow_negSucc, zpow_negSucc]
      exact (hasValue_pow_of_hasValue h (n + 1)).inv (pow_ne_zero _ ha)

end AlgebraicCurve.Place
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.modularRedLocHom_mem CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem modularFunctionFieldC_one qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full NodeLocalized.exists_hasValue_nodeCoord_of_centred frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder frobNodePair_fst ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData frickeInvolutionBar_frickeInvolutionBar NodeLocalized.exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728 jWidth NodeLocalized.isUnit_evalAt_zero_of_gaussPair_of_isAlgClosed NodeLocalized.isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "exists_hasValue_nodeCoord_of_centred modularEval exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728 isUnit_evalAt_zero_of_gaussPair_of_isAlgClosed isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed"
p2m_open "ModularCurve.NodeLocalized ModularCurve~coeffEmb_jq"

theorem correction_identity {K : Type*} [Field K] (a c q w : K) (m : ℤ) :
    a * (c⁻¹ * q ^ (-m))⁻¹ * w ^ (-m) = c * a * (q * w⁻¹) ^ m := by
  rw [mul_zpow, inv_zpow', mul_inv, inv_inv, zpow_neg q m, inv_inv]
  ring

theorem isFrickeAutFull_one_mul (q : ℕ) [Fact q.Prime] :
    IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) :=
  isFrickeAutFull_frickeInvolutionFull (1 * q) (exists_isFrickeAutFull_of_neZero (1 * q))

theorem frickeInvolutionBar_jElt (q : ℕ) [Fact q.Prime] :
    frickeInvolutionBar (1 * q)
        (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) 1 (1 * q) (one_mul _)
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro (1 * q) (one_mul _)))⟩ :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq).symm)
  rw [hj, h]

theorem frickeInvolutionBar_jqElt (q : ℕ) [Fact q.Prime] :
    frickeInvolutionBar (1 * q)
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ :
          modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) (1 * q) 1 (mul_one _)
  have hjq : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ :
        modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro 1 (mul_one _)))⟩ := Subtype.ext rfl
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (jqd_mem_full (1 * q) (Dvd.intro_left (1 * q) (mul_one _)))⟩ : modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq))
  rw [hjq, h, hj]

theorem qExpand_one_mul {K : Type*} [CommRing K] (q : ℕ) [NeZero q] (x : LaurentSeries K) :
    qExpand K (1 * q) x = qExpand K q x := by
  ext n
  by_cases h : (q : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have e : ((1 * q : ℕ) : ℤ) * m = (q : ℤ) * m := by rw [one_mul]
    rw [qExpand_coeff_mul]
    conv_lhs => rw [← e]
    rw [qExpand_coeff_mul]
  · have h' : ¬ ((1 * q : ℕ) : ℤ) ∣ n := by rwa [one_mul]
    rw [qExpand_coeff_of_not_dvd _ _ h', qExpand_coeff_of_not_dvd _ _ h]

theorem jqNModC_one_mul_eq_pow (K : Type*) [CommRing K] (q : ℕ) [Fact q.Prime] [CharP K q] :
    jqNModC K (1 * q) = jqModC K ^ q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [jqNModC, qExpand_one_mul, qExpand_jqModC_eq_pow_unconditional K]

theorem coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

theorem coeffEmb_qExpand_jq (N : ℕ) [NeZero N] :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N := by
  rw [jqNModC, ← coeffEmb_jq]
  ext n
  by_cases h : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem algebraMap_eq_single' {K : Type*} [CommRing K] (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single 0 c := by
  rw [HahnSeries.algebraMap_apply', show algebraMap K (PowerSeries K) c = PowerSeries.C c from by simp,
    HahnSeries.ofPowerSeries_C]
  rfl

section Red

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] (red : A →+* k)

theorem red_coeff_jqModC (n : ℤ) (h : (jqModC (AlgebraicClosure ℚ)).coeff n ∈ A.toSubring) :
    red ⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h⟩ = (jqModC k).coeff n := by
  have hz : (⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h⟩ : ↥A.toSubring)
      = ((jqModC ℤ).coeff n : ↥A.toSubring) := by
    apply Subtype.ext
    show (jqModC (AlgebraicClosure ℚ)).coeff n = (((jqModC ℤ).coeff n : ↥A.toSubring) : AlgebraicClosure ℚ)
    rw [jqModC_eq_map_intCast (K := AlgebraicClosure ℚ), HahnSeries.map_coeff, eq_intCast, SubringClass.coe_intCast]
  rw [hz, map_intCast, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff, eq_intCast]

theorem redRes_jqModC :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (1 * q) A.toSubring⟩
      = jqModC k := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
  exact red_coeff_jqModC red n _

theorem redRes_jqNModC :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring⟩
      = jqNModC k (1 * q) := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
  show red ⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n, _⟩ = (jqNModC k (1 * q)).coeff n
  by_cases h : ((1 * q : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have hm : (jqModC (AlgebraicClosure ℚ)).coeff m ∈ A.toSubring := CharPReduction.jqModC_mem_integralCoeffs A.toSubring m
    have hx : (⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff ((1 * q : ℕ) * m), CharPReduction.modularRing_le_integralCoeffs
          (1 * q) A.toSubring (CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring) _⟩ : ↥A.toSubring)
        = ⟨(jqModC (AlgebraicClosure ℚ)).coeff m, hm⟩ :=
      Subtype.ext (by show (jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff _ = _; rw [jqNModC, qExpand_coeff_mul])
    rw [hx, red_coeff_jqModC red m hm, jqNModC, qExpand_coeff_mul]
  · have hx : (⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n, CharPReduction.modularRing_le_integralCoeffs
          (1 * q) A.toSubring (CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring) _⟩ : ↥A.toSubring) = 0 :=
      Subtype.ext (by show (jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n = ((0 : ↥A.toSubring) : AlgebraicClosure ℚ)
                      rw [jqNModC, qExpand_coeff_of_not_dvd _ _ h]; rfl)
    rw [hx, map_zero, jqNModC, qExpand_coeff_of_not_dvd _ _ h]

theorem modularEval_mem_modularRing (N : ℕ) [NeZero N] (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    modularEval N A.toSubring P ∈ CharPReduction.modularRing N A.toSubring := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [modularEval, MvPolynomial.eval₂Hom_C]
      exact CharPReduction.constSeries_mem_modularRing N A.toSubring c
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [modularEval, MvPolynomial.eval₂Hom_X']
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · exact CharPReduction.jqModC_mem_modularRing N A.toSubring
      · exact CharPReduction.jqNModC_mem_modularRing N A.toSubring

theorem redRes_modularEval [CharP k q] (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨modularEval (1 * q) A.toSubring P, modularEval_mem_modularRing (1 * q) P⟩
      = Polynomial.aeval (jqModC k)
          (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P) := by

  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* LaurentSeries k :=
    (CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)).comp
      ((modularEval (1 * q) A.toSubring).codRestrict (CharPReduction.modularRing (1 * q) A.toSubring)
        (modularEval_mem_modularRing (1 * q)))
  let ψ : MvPolynomial (Fin 2) ↥A.toSubring →+* LaurentSeries k :=
    (Polynomial.aeval (jqModC k)).toRingHom.comp
      (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q])
  have hφψ : φ = ψ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    ·
      have hC : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.C c), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨CharPReduction.constSeries A.toSubring c, CharPReduction.constSeries_mem_modularRing (1 * q) _ c⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_C _ _ c)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.C c), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.C c))
      rw [hC, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.aeval_C, algebraMap_eq_single' (red c)]
      ext n
      rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff, HahnSeries.coeff_single]
      show red ⟨(CharPReduction.constSeries A.toSubring c).coeff n, _⟩ = _
      have hcs : ∀ m : ℤ, (CharPReduction.constSeries A.toSubring c).coeff m = if m = 0 then (c : AlgebraicClosure ℚ) else 0 := by
        intro m
        show (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)).coeff m = _
        rw [algebraMap_eq_single', HahnSeries.coeff_single]
        split_ifs <;> rfl
      by_cases hn : n = 0
      · subst hn
        have hx : (⟨(CharPReduction.constSeries A.toSubring c).coeff 0, CharPReduction.modularRing_le_integralCoeffs (1 * q)
            A.toSubring (CharPReduction.constSeries_mem_modularRing (1 * q) _ c) 0⟩ : ↥A.toSubring) = c :=
          Subtype.ext (by show (CharPReduction.constSeries A.toSubring c).coeff 0 = c; rw [hcs, if_pos rfl])
        rw [hx, if_pos rfl]
      · have hx : (⟨(CharPReduction.constSeries A.toSubring c).coeff n, CharPReduction.modularRing_le_integralCoeffs (1 * q)
            A.toSubring (CharPReduction.constSeries_mem_modularRing (1 * q) _ c) n⟩ : ↥A.toSubring) = 0 :=
          Subtype.ext (by show (CharPReduction.constSeries A.toSubring c).coeff n = ((0 : ↥A.toSubring) : AlgebraicClosure ℚ);
                          rw [hcs, if_neg hn]; rfl)
        rw [hx, map_zero, if_neg hn]
    ·
      have hX : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (1 * q) A.toSubring⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_X' _ _ 0)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.X 0))
      rw [hX, redRes_jqModC, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Polynomial.aeval_X]
    ·
      have hX : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 1), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_X' _ _ 1)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 1), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.X 1))
      rw [hX, redRes_jqNModC, jqNModC_one_mul_eq_pow, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero,
        map_pow, Polynomial.aeval_X]
  exact RingHom.congr_fun hφψ P

omit [Fact q.Prime] in

theorem eval_graphReduce (a : k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    Polynomial.eval a (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P)
      = MvPolynomial.eval₂Hom red ![a, a ^ q] P := by
  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* k :=
    (Polynomial.evalRingHom a).comp (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q])
  have hφ : φ = MvPolynomial.eval₂Hom red ![a, a ^ q] := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c)) = _
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.eval_C]
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 0)) = _
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_zero, Polynomial.eval_X]
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 1)) = _
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero, Polynomial.eval_pow, Polynomial.eval_X]
  exact RingHom.congr_fun hφ P

omit [Fact q.Prime] in

theorem eval₂Hom_kroneckerPolynomial (a : k) (R : Polynomial (Polynomial ℤ)) :
    MvPolynomial.eval₂Hom red ![a, a ^ q]
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)
      = ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a := by
  set E : MvPolynomial (Fin 2) ↥A.toSubring →+* k := MvPolynomial.eval₂Hom red ![a, a ^ q] with hE
  set g : Polynomial ℤ →+* MvPolynomial (Fin 2) ↥A.toSubring :=
    Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0) with hg
  have h1 : E (Polynomial.eval₂ g (MvPolynomial.X 1) R) = R.eval₂ (E.comp g) (E (MvPolynomial.X 1)) :=
    Polynomial.hom_eval₂ R g E (MvPolynomial.X 1)
  have hEg : E.comp g = Polynomial.eval₂RingHom (Int.castRingHom k) a := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · rw [RingHom.comp_apply, hg, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply, hE,
        MvPolynomial.eval₂Hom_C, eq_intCast, map_intCast, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, eq_intCast]
    · rw [RingHom.comp_apply, hg, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hE, MvPolynomial.eval₂Hom_X',
        Matrix.cons_val_zero, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hEX : E (MvPolynomial.X 1) = a ^ q := by
    rw [hE, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [h1, hEg, hEX]

  have h2 : ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a
      = R.eval₂ ((Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (Int.castRingHom k))) (Polynomial.eval a (Polynomial.C (a ^ q))) := by
    rw [Polynomial.eval_map, ← Polynomial.coe_evalRingHom, Polynomial.hom_eval₂]
  have h3 : (Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (Int.castRingHom k)) = Polynomial.eval₂RingHom (Int.castRingHom k) a := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_evalRingHom, Polynomial.eval_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [h2, h3, Polynomial.eval_C]

end Red
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

theorem exists_kroneckerRemainder (q : ℕ) [Fact q.Prime] (data : ModularPolynomialData q) :
    ∃ R : Polynomial (Polynomial ℤ),
      data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
        + Polynomial.C (Polynomial.C (q : ℤ)) * R := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hKr : KroneckerCongruence q data := kroneckerCongruence q data
  have hdvd : Polynomial.C (Polynomial.C (q : ℤ)) ∣
      data.Φ - (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro m
    have h := congrArg (fun S : Polynomial (Polynomial (ZMod q)) => (S.coeff n).coeff m) hKr
    have hprod : reduceModBivar q ((Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q))
        = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by
      simp only [map_mul, map_sub, map_pow, reduceModBivar_X, reduceModBivar_C_X]
    rw [← hprod] at h
    simp only [reduceModBivar, Polynomial.coe_mapRingHom, Polynomial.coeff_map, eq_intCast] at h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Polynomial.coeff_sub, Polynomial.coeff_sub, Int.cast_sub, sub_eq_zero]
    exact h
  obtain ⟨R, hR⟩ := hdvd
  exact ⟨R, by rw [← hR]; ring⟩

section Gauss

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] (red : A →+* k)

theorem gaussUnit_of_mem_modularRing {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ CharPReduction.modularRing (1 * q) A.toSubring)
    (hred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨x, hx⟩ ≠ 0) :
    ∃ h : x ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨x, h⟩ ≠ 0 := by
  refine ⟨CharPReduction.subring_le_localizedAtKer A.toSubring red _ _ hx, ?_⟩
  show CharPReduction.redLoc _ ≠ 0
  have h := CharPReduction.redLoc_coe (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨x, hx⟩
  intro h0
  apply hred
  rw [← h]
  exact h0

theorem gaussUnit_of_mem_modularRing_div {r s : LaurentSeries (AlgebraicClosure ℚ)}
    (hr : r ∈ CharPReduction.modularRing (1 * q) A.toSubring) (hs : s ∈ CharPReduction.modularRing (1 * q) A.toSubring)
    (hrred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨r, hr⟩ ≠ 0)
    (hsred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨s, hs⟩ ≠ 0) :
    ∃ h : r * s⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨r * s⁻¹, h⟩ ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h0
    apply hsred
    have : (⟨s, hs⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hnot : (⟨s, hs⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) ∉ CharPReduction.redKer A.toSubring red
      (CharPReduction.modularRing (1 * q) A.toSubring) (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) :=
    (CharPReduction.notMem_redKer_iff _ _ _ _).mpr hsred
  have hpres : r * s⁻¹ * s = r := by rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  have hmem : r * s⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := ⟨⟨r, hr⟩, ⟨s, hs⟩, hnot, hpres⟩
  refine ⟨hmem, ?_⟩
  show CharPReduction.redLoc _ ≠ 0
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨r * s⁻¹, hmem⟩ (r := ⟨r, hr⟩) (s := ⟨s, hs⟩) hpres
  exact left_ne_zero_of_mul (ne_of_eq_of_ne hspec hrred)

end Gauss
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

end ModularCurve.NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

namespace E4b80310

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve.NodeLocalized"

section NodeSide

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]

theorem modularRedLocHom_modularEval (red : A →+* k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red
        ⟨modularEval (1 * q) A.toSubring P, CharPReduction.subring_le_localizedAtKer _ _ _ _
          (modularEval_mem_modularRing (A := A) (1 * q) P)⟩
      = Polynomial.aeval (jqModC k)
          (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P) := by
  rw [← redRes_modularEval red P]
  exact CharPReduction.redLoc_coe (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
    ⟨modularEval (1 * q) A.toSubring P, modularEval_mem_modularRing (A := A) (1 * q) P⟩

theorem coe_aeval_jC1 (p : Polynomial k) :
    ((Polynomial.aeval (Ws23.NodePlaceAPI.jC1 k) p : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = Polynomial.aeval (jqModC k) p := by
  rw [← Ws23.NodePlaceAPI.coe_jC1 k, ← IntermediateField.algebraMap_apply, ← IntermediateField.algebraMap_apply,
    Polynomial.aeval_algebraMap_apply]

end NodeSide
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

end E4b80310
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

namespace Ws23
namespace CentredSigma

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve"

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.mem_smul_iff' (g : F) :
    σ g ∈ (σ • v).toValuationSubring ↔ g ∈ v.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

p2m_alias "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve.Place.mem_smul_iff'" "AlgebraicCurve.Place.mem_smul_iff'"

private theorem _root_.AlgebraicCurve.Place.hasValue_smul {g : F} {c : K} (h : v.HasValue g c) :
    (σ • v).HasValue (σ g) c := by
  obtain ⟨hg, hr⟩ := h
  let φ := Place.smulRingEquiv σ v.toValuationSubring
  have hg' : σ g ∈ (σ • v).toValuationSubring := (φ ⟨g, hg⟩).2
  refine ⟨hg', ?_⟩
  have h1 : (⟨σ g, hg'⟩ : (σ • v).toValuationSubring) = φ ⟨g, hg⟩ := rfl
  have h3 : φ (algebraMap K v.toValuationSubring c) = algebraMap K (σ • v).toValuationSubring c := by
    ext
    rw [Place.coe_smulRingEquiv_apply, Place.coe_algebraMap, σ.commutes]
    rfl
  rw [h1, ← Place.residue_algebraMap, ← h3]
  have key : ∀ z : v.toValuationSubring,
      residue _ (φ z) = IsLocalRing.ResidueField.mapEquiv φ (residue _ z) := fun z => by
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  show residue _ (φ ⟨g, hg⟩) = residue _ (φ (algebraMap K v.toValuationSubring c))
  rw [key, key, hr, Place.residue_algebraMap]

p2m_alias "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve.Place.hasValue_smul" "AlgebraicCurve.Place.hasValue_smul"

private theorem _root_.AlgebraicCurve.Place.isRational_smul (hv : v.IsRational) : (σ • v).IsRational := by
  intro z
  obtain ⟨w, hw⟩ := (Place.smulResidueAlgEquiv σ v).surjective z
  obtain ⟨c, hc⟩ := hv w
  refine ⟨c, ?_⟩
  rw [← hw, ← hc]
  exact ((Place.smulResidueAlgEquiv σ v).commutes c).symm

p2m_alias "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve.Place.isRational_smul" "AlgebraicCurve.Place.isRational_smul"

private theorem _root_.AlgebraicCurve.Place.evalAt_smul (hv : v.IsRational) (g : F) :
    (σ • v).evalAt (σ g) = v.evalAt g := by
  by_cases hg : g ∈ v.toValuationSubring
  · have h1 : v.HasValue g (v.evalAt g) := ⟨hg, (v.algebraMap_evalAt hv hg).symm⟩
    have h2 := Place.hasValue_smul σ v h1
    rw [(σ • v).evalAt_of_mem h2.mem, h2.residue_eq, (σ • v).residueInv_algebraMap]
  · have hg' : σ g ∉ (σ • v).toValuationSubring := fun h => hg ((Place.mem_smul_iff' σ v g).mp h)
    rw [Place.evalAt, Place.evalAt, dif_neg hg, dif_neg hg']

p2m_alias "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve.Place.evalAt_smul" "AlgebraicCurve.Place.evalAt_smul"
end Generic
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

section Modular

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

noncomputable def jE (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩

noncomputable def jqE (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

theorem isFrickeAutFull_one_mul (q : ℕ) [Fact q.Prime] :
    IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) :=
  isFrickeAutFull_frickeInvolutionFull (1 * q) (exists_isFrickeAutFull_of_neZero (1 * q))

theorem frickeInvolutionBar_jE (q : ℕ) [Fact q.Prime] : frickeInvolutionBar (1 * q) (jE q) = jqE q := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) 1 (1 * q) (one_mul _)
  have hj : jE q = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro (1 * q) (one_mul _)))⟩ :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq).symm)
  rw [hj, h]
  rfl

theorem frickeInvolutionBar_jqE (q : ℕ) [Fact q.Prime] : frickeInvolutionBar (1 * q) (jqE q) = jE q := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) (1 * q) 1 (mul_one _)
  have hjq : jqE q = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro 1 (mul_one _)))⟩ := Subtype.ext rfl
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (jqd_mem_full (1 * q) (Dvd.intro_left (1 * q) (mul_one _)))⟩ : modularFunctionFieldBar (1 * q)) = jE q :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq))
  rw [hjq, h, hj]

theorem frickeInvolutionBar_symm_jE (q : ℕ) [Fact q.Prime] : (frickeInvolutionBar (1 * q)).symm (jE q) = jqE q := by
  rw [AlgEquiv.symm_apply_eq]
  exact (frickeInvolutionBar_jqE q).symm

theorem frickeInvolutionBar_symm_jqE (q : ℕ) [Fact q.Prime] : (frickeInvolutionBar (1 * q)).symm (jqE q) = jE q := by
  rw [AlgEquiv.symm_apply_eq]
  exact (frickeInvolutionBar_jE q).symm

theorem frickeInvolutionBar_smul' (c : AlgebraicClosure ℚ) (x : ↥(modularFunctionFieldBar (1 * q))) :
    frickeInvolutionBar (1 * q) (c • x) = c • frickeInvolutionBar (1 * q) x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]

variable (red : A →+* k)

def Centred (a : k) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  (∃ x : A, red x = a ∧
      0 < W.ord (jE q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
  (∃ y : A, red y = a ^ q ∧
      0 < W.ord (jqE q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))

theorem centred_smul {a : k} (ha2 : a ^ (q ^ 2) = a) {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : Centred red a W) : Centred red (a ^ q) (frickeInvolutionBar (1 * q) • W) := by
  obtain ⟨⟨x, hxa, hx⟩, ⟨y, hya, hy⟩⟩ := hW
  refine ⟨⟨y, hya, ?_⟩, ⟨x, ?_, ?_⟩⟩
  · rw [← frickeInvolutionBar_jqE q, ← (frickeInvolutionBar (1 * q)).commutes (y : AlgebraicClosure ℚ), ← map_sub,
      Place.ord_smul]
    exact hy
  · rw [hxa, ← pow_mul, ← pow_two, ha2]
  · rw [← frickeInvolutionBar_jE q, ← (frickeInvolutionBar (1 * q)).commutes (x : AlgebraicClosure ℚ), ← map_sub,
      Place.ord_smul]
    exact hx

theorem centred_of_centred_smul {a : k} (ha2 : a ^ (q ^ 2) = a)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : Centred red (a ^ q) (frickeInvolutionBar (1 * q) • W)) : Centred red a W := by
  obtain ⟨⟨x, hxa, hx⟩, ⟨y, hya, hy⟩⟩ := hW
  refine ⟨⟨y, ?_, ?_⟩, ⟨x, hxa, ?_⟩⟩
  · rw [hya, ← pow_mul, ← pow_two, ha2]
  · rw [← Place.ord_smul (frickeInvolutionBar (1 * q)) W, map_sub, frickeInvolutionBar_jE, AlgEquiv.commutes]
    exact hy
  · rw [← Place.ord_smul (frickeInvolutionBar (1 * q)) W, map_sub, frickeInvolutionBar_jqE, AlgEquiv.commutes]
    exact hx

theorem centred_smul_iff {a : k} (ha2 : a ^ (q ^ 2) = a) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    Centred red (a ^ q) (frickeInvolutionBar (1 * q) • W) ↔ Centred red a W :=
  ⟨centred_of_centred_smul red ha2, centred_smul red ha2⟩

theorem forall_centred_ord_smul_eq_zero {a : k} (ha2 : a ^ (q ^ 2) = a) {f : ↥(modularFunctionFieldBar (1 * q))}
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W → W.ord f = 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : Centred red (a ^ q) W) :
    W.ord (frickeInvolutionBar (1 * q) f) = 0 := by
  have hW' : Centred red (a ^ q) (frickeInvolutionBar (1 * q) • ((frickeInvolutionBar (1 * q))⁻¹ • W)) := by
    rwa [smul_inv_smul]
  have h := hford _ (centred_of_centred_smul red ha2 hW')
  rwa [← Place.ord_smul (frickeInvolutionBar (1 * q)), smul_inv_smul] at h

end Modular
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

end Ws23.CentredSigma
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

namespace Ws23
namespace SlopeLaw0

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve.NodeLocalized P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.CentredSigma"

section Small

set_option synthInstance.maxHeartbeats 1600000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

theorem not_isUnit_natCast_zpow [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) {n : ℤ} (hn : n ≠ 0)
    (h : ((q : AlgebraicClosure ℚ)) ^ n ∈ A) : ¬ IsUnit (⟨_, h⟩ : A) := by
  have hqmem : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
    (hker _).mp (by rw [map_natCast]; exact CharP.cast_eq_zero k q)
  have hqnu : ¬ IsUnit ((q : ℕ) : A) := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hqmem
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hcoe : ∀ m : ℕ, ((((q : ℕ) : A) ^ m : A) : AlgebraicClosure ℚ) = ((q : AlgebraicClosure ℚ)) ^ (m : ℤ) := by
    intro m
    rw [zpow_natCast]
    push_cast
    rfl
  intro hu
  apply hqnu
  rcases lt_or_gt_of_ne hn with hlt | hgt
  ·
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -((m : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
    subst hm
    have hprod : ((q : ℕ) : A) ^ (m + 1) * (⟨_, h⟩ : A) = 1 := by
      apply Subtype.ext
      show ((((q : ℕ) : A) ^ (m + 1) : A) : AlgebraicClosure ℚ) * ((q : AlgebraicClosure ℚ)) ^ (-((m : ℤ) + 1))
        = (1 : AlgebraicClosure ℚ)
      rw [hcoe, zpow_neg, ← Nat.cast_succ, mul_inv_cancel₀ (zpow_ne_zero _ hq0)]
    have hu2 : IsUnit (((q : ℕ) : A) ^ (m + 1)) := ⟨⟨_, _, hprod, by rwa [mul_comm] at hprod⟩, rfl⟩
    exact (isUnit_pow_iff (Nat.succ_ne_zero m)).mp hu2
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
    subst hm
    have heq : (⟨_, h⟩ : A) = ((q : ℕ) : A) ^ (m + 1) := by
      apply Subtype.ext
      show ((q : AlgebraicClosure ℚ)) ^ ((m : ℤ) + 1) = (((q : ℕ) : A) ^ (m + 1) : A)
      rw [hcoe, Nat.cast_succ]
    rw [heq] at hu
    exact (isUnit_pow_iff (Nat.succ_ne_zero m)).mp hu

omit [Fact q.Prime] in

theorem pow_pow_sq_eq {a : k} (ha2 : a ^ (q ^ 2) = a) : (a ^ q) ^ (q ^ 2) = a ^ q := by
  rw [← pow_mul, mul_comm, pow_mul, ha2]

theorem pow_ne_1728 [CharP k q] {a : k} (ha2 : a ^ (q ^ 2) = a) (h1728 : a ≠ 1728) : a ^ q ≠ 1728 := by
  intro h
  apply h1728
  have h2 : (a ^ q) ^ q = (1728 : k) ^ q := by rw [h]
  rw [← pow_mul, ← pow_two, ha2] at h2
  rw [h2]
  have h3 : frobenius k q ((1728 : ℕ) : k) = ((1728 : ℕ) : k) := map_natCast (frobenius k q) 1728
  rw [frobenius_def] at h3
  exact_mod_cast h3

theorem ord_algebraMap_mul {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {c : K} (hc : c ≠ 0)
    {g : F} (hg : g ≠ 0) : v.ord (algebraMap K F c * g) = v.ord g := by
  rw [v.ord_mul ((map_ne_zero _).mpr hc) hg, (v.hasValue_algebraMap c).ord_eq_zero hc, zero_add]

theorem coe_algebraMap_eq_constSeries (c : A) :
    ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = CharPReduction.constSeries A.toSubring ⟨(c : AlgebraicClosure ℚ), c.2⟩ := rfl

theorem algebraMap_mem_modularLocalized (red : A →+* k) (c : A) :
    ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by
  rw [coe_algebraMap_eq_constSeries]
  exact CharPReduction.subring_le_localizedAtKer _ _ _ _
    (CharPReduction.constSeries_mem_modularRing (1 * q) A.toSubring ⟨(c : AlgebraicClosure ℚ), c.2⟩)

theorem modularRedLocHom_algebraMap [CharP k q] (red : A →+* k) (c : A)
    (h : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ = algebraMap k (LaurentSeries k) (red c) := by
  have hm : modularEval (1 * q) A.toSubring (MvPolynomial.C ⟨(c : AlgebraicClosure ℚ), c.2⟩)
      = ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [modularEval, MvPolynomial.eval₂Hom_C, coe_algebraMap_eq_constSeries]
  have key := E4b80310.modularRedLocHom_modularEval (q := q) (A := A) red (MvPolynomial.C ⟨(c : AlgebraicClosure ℚ), c.2⟩)
  rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.aeval_C] at key
  have hsub : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.C ⟨(c : AlgebraicClosure ℚ), c.2⟩),
        CharPReduction.subring_le_localizedAtKer _ _ _ _
          (ModularCurve.NodeLocalized.modularEval_mem_modularRing (A := A) (1 * q) _)⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red))
      = ⟨_, h⟩ := Subtype.ext hm
  rw [hsub] at key
  exact key

theorem coe_smul_eq (c : A) (g : ↥(modularFunctionFieldBar (1 * q))) :
    (((c : AlgebraicClosure ℚ) • g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
          ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * (g : LaurentSeries (AlgebraicClosure ℚ)) := by
  rw [Algebra.smul_def]
  rfl

theorem smul_mem_modularLocalized (red : A →+* k) (c : A) {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    (((c : AlgebraicClosure ℚ) • g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by
  rw [coe_smul_eq]
  exact mul_mem (algebraMap_mem_modularLocalized red c) hg

theorem modularRedLocHom_smul [CharP k q] (red : A →+* k) (c : A) {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hcg : (((c : AlgebraicClosure ℚ) • g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hcg⟩
      = algebraMap k (LaurentSeries k) (red c) * CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩ := by
  have hprod : (⟨_, hcg⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red))
      = ⟨_, algebraMap_mem_modularLocalized red c⟩ * ⟨_, hg⟩ := Subtype.ext (coe_smul_eq c g)
  rw [hprod, map_mul, modularRedLocHom_algebraMap]

theorem nodeCoord_mem_and_evalAt_ne_zero [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : Centred red a W) :
    (jqE q - jE q ^ q) ∈ W.toValuationSubring ∧ W.evalAt (jqE q - jE q ^ q) ≠ 0 := by
  obtain ⟨c, -, ⟨d, -, hcd⟩, hV⟩ :=
    ModularCurve.NodeLocalized.exists_hasValue_nodeCoord_of_centred red hker hq a ha ha2 h0 h1728 W hW
  have hV' : W.HasValue (jqE q - jE q ^ q) (c : AlgebraicClosure ℚ) := hV
  refine ⟨hV'.mem, ?_⟩
  rw [evalAt_eq_of_hasValue' hV']
  intro hc0
  have hq0 : ((q : ℕ) : A) ≠ 0 := by
    intro h
    have : ((q : ℕ) : AlgebraicClosure ℚ) = 0 := by exact_mod_cast congrArg Subtype.val h
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  apply hq0
  rw [← hcd, show c = 0 from Subtype.ext hc0, zero_mul]

theorem modularFunctionFieldC_one_mul (K : Type*) [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] :
    modularFunctionFieldC K (1 * q) = modularFunctionFieldC K 1 := by
  rw [modularFunctionFieldC_one, modularFunctionFieldC, ModularCurve.NodeLocalized.jqNModC_one_mul_eq_pow]
  refine le_antisymm ?_ (IntermediateField.adjoin.mono K _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton _)
  · exact pow_mem (IntermediateField.subset_adjoin K _ (Set.mem_singleton (jqModC K))) q

theorem modularRedLocHom_mem_one [CharP k q] (red : A →+* k)
    (g : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red g ∈ modularFunctionFieldC k 1 := by
  rw [← modularFunctionFieldC_one_mul k q]
  exact CharPReduction.modularRedLocHom_mem A.toSubring red (1 * q) g

end Small
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

end Ws23.SlopeLaw0
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

namespace Ws23
namespace Jump

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve"

section UnitA
set_option synthInstance.maxHeartbeats 1600000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

theorem not_isUnit_natCast_zpow [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) {n : ℤ} (hn : n ≠ 0)
    (h : ((q : AlgebraicClosure ℚ)) ^ n ∈ A) : ¬ IsUnit (⟨_, h⟩ : A) := by
  have hqmem : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
    (hker _).mp (by rw [map_natCast]; exact CharP.cast_eq_zero k q)
  have hqnu : ¬ IsUnit ((q : ℕ) : A) := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hqmem
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hcoe : ∀ m : ℕ, ((((q : ℕ) : A) ^ m : A) : AlgebraicClosure ℚ) = ((q : AlgebraicClosure ℚ)) ^ (m : ℤ) := by
    intro m
    rw [zpow_natCast]
    push_cast
    rfl
  intro hu
  apply hqnu
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -((m : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
    subst hm
    have hprod : ((q : ℕ) : A) ^ (m + 1) * (⟨_, h⟩ : A) = 1 := by
      apply Subtype.ext
      show ((((q : ℕ) : A) ^ (m + 1) : A) : AlgebraicClosure ℚ) * ((q : AlgebraicClosure ℚ)) ^ (-((m : ℤ) + 1))
        = (1 : AlgebraicClosure ℚ)
      rw [hcoe, zpow_neg, ← Nat.cast_succ, mul_inv_cancel₀ (zpow_ne_zero _ hq0)]
    have hu2 : IsUnit (((q : ℕ) : A) ^ (m + 1)) := ⟨⟨_, _, hprod, by rwa [mul_comm] at hprod⟩, rfl⟩
    exact (isUnit_pow_iff (Nat.succ_ne_zero m)).mp hu2
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
    subst hm
    have heq : (⟨_, h⟩ : A) = ((q : ℕ) : A) ^ (m + 1) := by
      apply Subtype.ext
      show ((q : AlgebraicClosure ℚ)) ^ ((m : ℤ) + 1) = (((q : ℕ) : A) ^ (m + 1) : A)
      rw [hcoe, Nat.cast_succ]
    rw [heq] at hu
    exact (isUnit_pow_iff (Nat.succ_ne_zero m)).mp hu

def UnitA (A : ValuationSubring (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) : Prop := ∃ h : x ∈ A, IsUnit (⟨x, h⟩ : A)

omit [Fact q.Prime] in
theorem UnitA.mul {x y : AlgebraicClosure ℚ} (hx : UnitA A x) (hy : UnitA A y) : UnitA A (x * y) := by
  obtain ⟨hx, hxu⟩ := hx
  obtain ⟨hy, hyu⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : A) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this]
  exact hxu.mul hyu

omit [Fact q.Prime] in
theorem UnitA.ne_zero {x : AlgebraicClosure ℚ} (hx : UnitA A x) : x ≠ 0 := by
  obtain ⟨hx, hxu⟩ := hx
  intro h0
  apply hxu.ne_zero
  exact Subtype.ext h0

omit [Fact q.Prime] in
theorem UnitA.inv {x : AlgebraicClosure ℚ} (hx : UnitA A x) : UnitA A x⁻¹ := by
  obtain ⟨hx, u, hu⟩ := hx
  have h1 : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = x⁻¹ := by
    have h3 : x * (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = 1 := by
      have h4 : ((u : A) : AlgebraicClosure ℚ) = x := by rw [hu]
      rw [← h4, ← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel]
      rfl
    exact eq_inv_of_mul_eq_one_right h3
  have hmem : x⁻¹ ∈ A := by rw [← h1]; exact ((u⁻¹ : Aˣ) : A).2
  refine ⟨hmem, ?_⟩
  have : (⟨x⁻¹, hmem⟩ : A) = ((u⁻¹ : Aˣ) : A) := Subtype.ext h1.symm
  rw [this]
  exact Units.isUnit _

omit [Fact q.Prime] in

theorem UnitA.of_mul_left {x y : AlgebraicClosure ℚ} (hxy : UnitA A (x * y)) (hx : UnitA A x) : UnitA A y := by
  have h := (hx.inv).mul hxy
  rwa [← mul_assoc, inv_mul_cancel₀ hx.ne_zero, one_mul] at h

omit [Fact q.Prime] in
theorem UnitA.congr {x y : AlgebraicClosure ℚ} (hx : UnitA A x) (e : x = y) : UnitA A y := e ▸ hx

theorem UnitA.red_ne_zero (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {x : AlgebraicClosure ℚ} (hx : UnitA A x) : red ⟨x, hx.1⟩ ≠ 0 := by
  obtain ⟨hmem, hu⟩ := hx
  intro h
  have := (hker _).mp h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this
  exact this hu

theorem eq_zero_of_unitA_natCast_zpow [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) {n : ℤ}
    (h : UnitA A (((q : AlgebraicClosure ℚ)) ^ n)) : n = 0 := by
  by_contra hn
  obtain ⟨hmem, hu⟩ := h
  exact not_isUnit_natCast_zpow red hker hn hmem hu

omit [Fact q.Prime] in

theorem unitA_iff_valuation_eq_one {x : AlgebraicClosure ℚ} : UnitA A x ↔ A.valuation x = 1 := by
  constructor
  · rintro ⟨hx, hu⟩
    exact (A.valuation_eq_one_iff ⟨x, hx⟩).mp hu
  · intro h
    have hle : A.valuation x ≤ 1 := h.le
    have hx : x ∈ A := (A.valuation_le_one_iff x).mp hle
    exact ⟨hx, (A.valuation_eq_one_iff ⟨x, hx⟩).mpr h⟩

omit [Fact q.Prime] in

theorem UnitA.of_pow {x : AlgebraicClosure ℚ} {e : ℕ} (he : e ≠ 0) (h : UnitA A (x ^ e)) : UnitA A x := by
  rw [unitA_iff_valuation_eq_one] at h ⊢
  rw [map_pow] at h
  rcases lt_trichotomy (A.valuation x) 1 with hlt | heq | hgt
  · exact absurd h (pow_lt_one₀ zero_le' hlt he).ne
  · exact heq
  · exact absurd h (one_lt_pow₀ hgt he).ne'

end UnitA
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

end Ws23.Jump
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

namespace Ws23
namespace Jump

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve.NodeLocalized P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.CentredSigma"

section PlaceGeneric

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_one' : v.ord (1 : F) = 0 := (v.hasValue_one).ord_eq_zero one_ne_zero

theorem ord_pow' {f : F} (hf : f ≠ 0) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  induction n with
  | zero => rw [pow_zero, ord_one', Nat.cast_zero, zero_mul]
  | succ n ih => rw [pow_succ, v.ord_mul (pow_ne_zero _ hf) hf, ih]; push_cast; ring

theorem ord_inv' {f : F} (hf : f ≠ 0) : v.ord f⁻¹ = - v.ord f := by
  have h := v.ord_mul hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one'] at h
  omega

theorem ord_zpow' {f : F} (hf : f ≠ 0) (n : ℤ) : v.ord (f ^ n) = n * v.ord f := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast, ord_pow' v hf]
  · rw [zpow_neg, zpow_natCast, ord_inv' v (pow_ne_zero _ hf), ord_pow' v hf]; ring

theorem ord_nonneg_of_mem' {g : F} (hm : g ∈ v.toValuationSubring) : 0 ≤ v.ord g := by
  by_cases hg : g = 0
  · rw [hg, Place.ord_zero]
  · exact GaussReduction.ord_nonneg_of_mem_gen v hm hg

theorem hasValue_ne_zero_of_inv {y : F} (hy : y ≠ 0) {c c' : K} (h : v.HasValue y c) (h' : v.HasValue y⁻¹ c') :
    c ≠ 0 := by
  have hprod := h.mul h'
  rw [mul_inv_cancel₀ hy] at hprod
  have h1 : c * c' = 1 := hprod.unique v.hasValue_one
  exact left_ne_zero_of_mul_eq_one h1

theorem coe_zpow' {L : Type*} [Field L] [Algebra K L] (S : IntermediateField K L) (x : ↥S) (m : ℤ) :
    ((x ^ m : ↥S) : L) = (x : L) ^ m := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, SubmonoidClass.coe_pow]
  | negSucc n => rw [zpow_negSucc, zpow_negSucc, IntermediateField.coe_inv, SubmonoidClass.coe_pow]

theorem zpow_mem_of_mem_of_inv_mem {f : F} (hf : f ∈ v.toValuationSubring) (hfi : f⁻¹ ∈ v.toValuationSubring) (m : ℤ) :
    f ^ m ∈ v.toValuationSubring := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact pow_mem hf n
  | negSucc n => rw [zpow_negSucc, ← inv_pow]; exact pow_mem hfi _

theorem isRational_W {q : ℕ} [Fact q.Prime] (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : W.IsRational := by
  intro z
  have h : W.deg = 1 := deg_eq_one_modularFunctionFieldBar (1 * q) W
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra (AlgebraicClosure ℚ) W.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra (AlgebraicClosure ℚ) W.ResidueField) := by rw [hbt]; exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

end PlaceGeneric
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

section RL

set_option synthInstance.maxHeartbeats 1600000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  (red : A →+* k)

noncomputable def rlHom : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red) →+* ↥(modularFunctionFieldC k 1) :=
  (CharPReduction.modularRedLocHom (1 * q) A.toSubring red).codRestrict (modularFunctionFieldC k 1)
    (fun x => Ws23.SlopeLaw0.modularRedLocHom_mem_one red x)

theorem coe_rlHom (x : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) :
    ((rlHom red x : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = CharPReduction.modularRedLocHom (1 * q) A.toSubring red x :=
  rfl

theorem rlHom_eq (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hF : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨x, hx⟩ ∈ modularFunctionFieldC k 1) :
    (⟨_, hF⟩ : ↥(modularFunctionFieldC k 1)) = rlHom red ⟨x, hx⟩ := Subtype.ext rfl

theorem rlHom_ne_zero_iff (x : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) :
    rlHom red x ≠ 0 ↔ CharPReduction.modularRedLocHom (1 * q) A.toSubring red x ≠ 0 := by
  rw [not_iff_not]
  constructor
  · intro h; have := congrArg Subtype.val h; exact this
  · intro h; exact Subtype.ext h

theorem rlHom_zpow {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : ∃ h : x ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨x, h⟩ ≠ 0)
    (m : ℤ) (hm : x ^ m ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    rlHom red ⟨x ^ m, hm⟩ = (rlHom red ⟨x, hx.1⟩) ^ m := by
  obtain ⟨hxm, hx0⟩ := hx
  have hne : rlHom red ⟨x, hxm⟩ ≠ 0 := (rlHom_ne_zero_iff red _).mpr hx0
  have hxne : x ≠ 0 := by
    intro h0; apply hx0
    have : (⟨x, hxm⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 0 := Subtype.ext h0
    rw [this, map_zero]

  suffices key : ∀ (y : LaurentSeries (AlgebraicClosure ℚ)) (hy : y ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
      y = x ^ m → rlHom red ⟨y, hy⟩ = (rlHom red ⟨x, hxm⟩) ^ m from key _ hm rfl
  intro y hy hyx
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have : (⟨y, hy⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨x, hxm⟩ ^ n :=
      Subtype.ext (show y = (((⟨x, hxm⟩ ^ n : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red))) : LaurentSeries (AlgebraicClosure ℚ)) by
        rw [SubmonoidClass.coe_pow, hyx]; exact zpow_natCast x n)
    rw [this, map_pow, zpow_natCast]
  · have hprod : (⟨y, hy⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) * ⟨x, hxm⟩ ^ n = 1 := by
      apply Subtype.ext
      show y * x ^ n = 1
      rw [hyx, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hxne)]
    have h2 := congrArg (rlHom red) hprod
    rw [map_mul, map_pow, map_one] at h2
    rw [zpow_neg, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left h2

theorem rlHom_inv {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : ∃ h : x ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨x, h⟩ ≠ 0)
    (hm : x⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    rlHom red ⟨x⁻¹, hm⟩ = (rlHom red ⟨x, hx.1⟩)⁻¹ := by
  obtain ⟨hxm, hx0⟩ := hx
  have hxne : x ≠ 0 := by
    intro h0; apply hx0
    have : (⟨x, hxm⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hprod : (⟨x⁻¹, hm⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) * ⟨x, hxm⟩ = 1 :=
    Subtype.ext (show x⁻¹ * x = 1 from inv_mul_cancel₀ hxne)
  have h2 := congrArg (rlHom red) hprod
  rw [map_mul, map_one] at h2
  exact eq_inv_of_mul_eq_one_left h2

theorem ord_rlHom_smul (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (v : Place k ↥(modularFunctionFieldC k 1)) (c : A) (hc : IsUnit c)
    {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hg0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩ ≠ 0)
    (hcg : (((c : AlgebraicClosure ℚ) • g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    v.ord (rlHom red ⟨_, hcg⟩) = v.ord (rlHom red ⟨_, hg⟩) := by
  have hredc : red c ≠ 0 := by
    intro h
    have := (hker _).mp h
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this
    exact this hc
  have heq : rlHom red ⟨_, hcg⟩ = algebraMap k (modularFunctionFieldC k 1) (red c) * rlHom red ⟨_, hg⟩ := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, coe_rlHom, coe_rlHom]
    exact Ws23.SlopeLaw0.modularRedLocHom_smul red c hg hcg
  have hne : rlHom red ⟨_, hg⟩ ≠ 0 := (rlHom_ne_zero_iff red _).mpr hg0
  rw [heq, Ws23.SlopeLaw0.ord_algebraMap_mul v hredc hne]

end RL
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

section Calibrator

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  [IsAlgClosed k] [DecidableEq k] (red : A →+* k)

theorem rootMultiplicity_X_sub_X_pow_sq_eq_one {b : k} (hb : b ^ (q ^ 2) = b) :
    (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k).rootMultiplicity b = 1 := by
  have hq1 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt
  have hne : (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k) ≠ 0 := by
    intro h
    have := congrArg Polynomial.natDegree (sub_eq_zero.mp h)
    rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow] at this
    omega
  have hroot : (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k).IsRoot b := by
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_X, hb, sub_self]
  have hderiv : Polynomial.derivative (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k) = 1 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_X_pow]
    have : ((q ^ 2 : ℕ) : Polynomial k) = 0 := by
      rw [pow_two, Nat.cast_mul]
      have hq : ((q : ℕ) : Polynomial k) = 0 := by
        rw [← Polynomial.C_eq_natCast, CharP.cast_eq_zero k q, map_zero]
      rw [hq, zero_mul]
    rw [Polynomial.C_eq_natCast, this, zero_mul, sub_zero]
  have hnot : ¬ (Polynomial.derivative (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k)).IsRoot b := by
    rw [hderiv, Polynomial.IsRoot, Polynomial.eval_one]; exact one_ne_zero
  have hle := (Polynomial.one_lt_rootMultiplicity_iff_isRoot (p := (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k)) hne).not.mpr
    (fun h => hnot h.2)
  have hge : 1 ≤ (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k).rootMultiplicity b :=
    (Polynomial.rootMultiplicity_pos hne).mpr hroot
  omega

theorem exists_gaussUnit_calibrator_ord_eq_one (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    ∃ (hz : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (jqE q - jE q ^ q)⁻¹ :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hz⟩ ≠ 0 ∧
      (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, hz⟩) = 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨J, hJ⟩ : ∃ J : ↥(modularFunctionFieldBar (1 * q)), J = ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ := ⟨_, rfl⟩
  obtain ⟨JQ, hJQ⟩ : ∃ JQ : ↥(modularFunctionFieldBar (1 * q)), JQ = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ := ⟨_, rfl⟩
  have hJser : (J : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by rw [hJ]; exact coeffEmb_jq
  have hJQser : (JQ : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
    rw [hJQ]; exact coeffEmb_qExpand_jq (1 * q)

  have hGser : ((JQ - J ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) A.toSubring (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) := by
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, hJser, hJQser]
    simp only [modularEval, map_sub, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Matrix.cons_val_one,
      Matrix.cons_val_zero]
  have hHser : ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) := by
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, hJser, hJQser]
    simp only [modularEval, map_sub, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Matrix.cons_val_one,
      Matrix.cons_val_zero]

  have hHred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
      ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularRing (1 * q) _⟩ ≠ 0 := by
    rw [redRes_modularEval]
    intro hzero
    have hQ : (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
        (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q : MvPolynomial (Fin 2) ↥A.toSubring)) ≠ 0 := by
      rw [map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      intro h
      have hdeg := congrArg Polynomial.natDegree (sub_eq_zero.mp h)
      rw [Polynomial.natDegree_X, ← pow_mul, Polynomial.natDegree_X_pow] at hdeg
      have h25 : 25 ≤ q * q := Nat.mul_le_mul hq hq
      rw [← hdeg] at h25
      exact absurd h25 (by norm_num)
    exact transcendental_jqModC k ⟨_, hQ, hzero⟩

  obtain ⟨data⟩ := nonempty_modularPolynomialData q
  obtain ⟨R, hR⟩ := exists_kroneckerRemainder q data
  have hRne := eval_kroneckerRemainder_ne_zero_of_mem_ssJSet hq data R hR a ha h0 h1728
  have hEval := modularEval_kroneckerRemainder A data R hR
  rw [← hJ, ← hJQ] at hEval

  obtain ⟨Rser, hRser⟩ : ∃ Rser : LaurentSeries (AlgebraicClosure ℚ), Rser = modularEval (1 * q) A.toSubring
      (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
        (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring) := ⟨_, rfl⟩
  rw [← hRser] at hEval
  have hRmem : Rser ∈ CharPReduction.modularRing (1 * q) A.toSubring := by rw [hRser]; exact modularEval_mem_modularRing (1 * q) _
  have hRred' : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨Rser, hRmem⟩ ≠ 0 := by
    have hx : (⟨Rser, hRmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = ⟨modularEval (1 * q) A.toSubring
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring), modularEval_mem_modularRing (1 * q) _⟩ := Subtype.ext hRser
    rw [hx, redRes_modularEval]
    intro hzero
    have hQ : (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)) ≠ 0 := by
      intro h
      apply hRne
      rw [← eval₂Hom_kroneckerPolynomial red a R, ← eval_graphReduce red a, h, Polynomial.eval_zero]
    exact transcendental_jqModC k ⟨_, hQ, hzero⟩
  have hHmem : ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularRing (1 * q) A.toSubring := by rw [hHser]; exact modularEval_mem_modularRing (1 * q) _
  have hHred' : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨_, hHmem⟩ ≠ 0 := by
    have hx : (⟨_, hHmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring))
        = ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularRing (1 * q) _⟩ :=
      Subtype.ext hHser
    rw [hx]; exact hHred
  have hH0 : (J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
    intro h
    apply hHred'
    have hx : (⟨_, hHmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 :=
      Subtype.ext (by
        show ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
          = ((0 : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) : LaurentSeries (AlgebraicClosure ℚ))
        rw [h]; rfl)
    rw [hx, map_zero]
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

  have hjE : jE q = J := by rw [hJ]; rfl
  have hjqE : jqE q = JQ := by rw [hJQ]; rfl
  have hident : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (JQ - J ^ q)⁻¹
      = (J - JQ ^ q) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ))⁻¹
          * ((JQ - J ^ q) * (J - JQ ^ q)))⁻¹ := by
    have h : (J - JQ ^ q) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ))⁻¹
          * ((JQ - J ^ q) * (J - JQ ^ q)))⁻¹
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (JQ - J ^ q)⁻¹
          * ((J - JQ ^ q) * (J - JQ ^ q)⁻¹) := by
      rw [mul_inv, inv_inv, mul_inv]; ring
    rw [h, mul_inv_cancel₀ hH0, mul_one]
  have hcoe : (((J - JQ ^ q) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ))⁻¹
          * ((JQ - J ^ q) * (J - JQ ^ q)))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * Rser⁻¹ := by
    rw [MulMemClass.coe_mul, IntermediateField.coe_inv, MulMemClass.coe_mul, IntermediateField.coe_inv, MulMemClass.coe_mul,
      hEval, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, map_natCast,
      map_natCast, show (((q : ℕ) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = (modularFunctionFieldBar (1 * q)).val (q : ↥(modularFunctionFieldBar (1 * q))) from rfl, map_natCast]
  have hzser : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (jqE q - jE q ^ q)⁻¹ :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * Rser⁻¹ := by
    rw [hjE, hjqE, hident, hcoe]
  obtain ⟨hz, hz0⟩ := CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hzser.symm
    (gaussUnit_of_mem_modularRing_div red hHmem hRmem hHred' hRred')
  refine ⟨hz, hz0, ?_⟩

  have hRser0 : Rser ≠ 0 := by
    intro h0; apply hRred'
    have : (⟨Rser, hRmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hRloc := CharPReduction.subring_le_localizedAtKer A.toSubring red _ (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) hRmem
  have hHloc := CharPReduction.subring_le_localizedAtKer A.toSubring red _ (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) hHmem
  have hprodML : (⟨_, hz⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) * ⟨Rser, hRloc⟩ = ⟨_, hHloc⟩ := by
    apply Subtype.ext
    show ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (jqE q - jE q ^ q)⁻¹ :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * Rser = _
    rw [hzser, mul_assoc, inv_mul_cancel₀ hRser0, mul_one]
  have hprodF := congrArg (rlHom red) hprodML
  rw [map_mul] at hprodF

  have hRl : rlHom red ⟨Rser, hRloc⟩ = Polynomial.aeval (jC1 k)
      (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)) := by
    apply Subtype.ext
    rw [coe_rlHom, E4b80310.coe_aeval_jC1]
    have hx : (⟨Rser, hRloc⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨modularEval (1 * q) A.toSubring _,
        CharPReduction.subring_le_localizedAtKer _ _ _ _ (ModularCurve.NodeLocalized.modularEval_mem_modularRing (A := A) (1 * q) _)⟩ := Subtype.ext hRser
    rw [hx]
    exact E4b80310.modularRedLocHom_modularEval red _
  have hHl : rlHom red ⟨_, hHloc⟩ = Polynomial.aeval (jC1 k) (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k) := by
    apply Subtype.ext
    rw [coe_rlHom, E4b80310.coe_aeval_jC1]
    have hx : (⟨_, hHloc⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        CharPReduction.subring_le_localizedAtKer _ _ _ _ (ModularCurve.NodeLocalized.modularEval_mem_modularRing (A := A) (1 * q) _)⟩ := Subtype.ext hHser
    rw [hx, E4b80310.modularRedLocHom_modularEval red]
    congr 1
    rw [map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero, ← pow_mul, pow_two]

  have hordR : (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨Rser, hRloc⟩) = 0 := by
    rw [hRl, Ws23.NodePlaceAPI.ord_charLGeomPlaceOfPoint_aeval]
    have : Polynomial.rootMultiplicity a (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)) = 0 := by
      rw [Polynomial.rootMultiplicity_eq_zero_iff]
      intro hroot
      exfalso
      apply hRne
      rw [← eval₂Hom_kroneckerPolynomial red a R, ← eval_graphReduce red a]
      exact hroot
    rw [this]; rfl
  have hordH : (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, hHloc⟩) = 1 := by
    rw [hHl, Ws23.NodePlaceAPI.ord_charLGeomPlaceOfPoint_aeval, rootMultiplicity_X_sub_X_pow_sq_eq_one ha2]; rfl
  have hz0' : rlHom red ⟨_, hz⟩ ≠ 0 := (rlHom_ne_zero_iff red _).mpr hz0
  have hR0' : rlHom red ⟨Rser, hRloc⟩ ≠ 0 := by
    intro h; rw [h, mul_zero] at hprodF
    have := hordH; rw [← hprodF, Place.ord_zero] at this; exact zero_ne_one this
  have hsum := congrArg (charLGeomPlaceOfPoint k a).ord hprodF
  rw [Place.ord_mul _ hz0' hR0', hordR, hordH, add_zero] at hsum
  exact hsum

end Calibrator
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

end Ws23.Jump
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap Place.deg Place.ord_zero Place.ord_mul Place.smulRingEquiv Place.coe_smulRingEquiv_apply Place.smul_toValuationSubring Place.ord_smul Place.smulResidueAlgEquiv Place.residue_algebraMap GluedPic0 Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.heightOneSpectrumOfIrreducible RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum RationalFunctionField.residueOfHeightOneSpectrum RationalFunctionField.residueOfHeightOneSpectrum_apply RationalFunctionField.ker_residueOfHeightOneSpectrum RationalFunctionField.placeOfPoint Place.comapSymmRingEquiv Place.coe_comapSymmRingEquiv_apply Place.congrRingEquiv Place.ord_congrRingEquiv ComponentChart Annulus ConstantReduction ConstantReduction.ord_algebraMap Place.evalAt GaussReduction.ord_nonneg_of_mem_gen StandardAnnulus.ord_placeOfPoint_X_sub_C_self Place.mem_smul_iff' Place.hasValue_smul Place.isRational_smul Place.evalAt_smul"
p2m_open "AlgebraicCurve"
namespace ComponentChart
p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff residue nodes residue_algebraMap ker_residue dom"
p2m_open "AlgebraicCurve.ComponentChart"

open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

private theorem _root_.AlgebraicCurve.ComponentChart.isUnit_of_residue_ne_zero (C : ComponentChart A F Fbar) {g : F} (hg : g ∈ C.integers)
    (h : C.residue ⟨g, hg⟩ ≠ 0) : IsUnit (⟨g, hg⟩ : C.integers) := by
  by_contra hnu
  apply h
  have hmem : (⟨g, hg⟩ : C.integers) ∈ maximalIdeal C.integers := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hnu
  rw [← C.ker_residue] at hmem
  exact hmem

p2m_export "AlgebraicCurve.ComponentChart" "isUnit_of_residue_ne_zero"

private theorem _root_.AlgebraicCurve.ComponentChart.inv_mem_of_residue_ne_zero (C : ComponentChart A F Fbar) {g : F} (hg : g ∈ C.integers)
    (h : C.residue ⟨g, hg⟩ ≠ 0) : g⁻¹ ∈ C.integers := by
  obtain ⟨u, hu⟩ := C.isUnit_of_residue_ne_zero hg h
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply h
    have : (⟨0, hg⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have hmul : ((u : C.integers) : F) * ((u⁻¹ : C.integersˣ) : C.integers) = 1 := by
    have h1 : (u : C.integers) * ((u⁻¹ : C.integersˣ) : C.integers) = 1 := Units.mul_inv u
    exact congrArg Subtype.val h1
  have hginv : g⁻¹ = ((u⁻¹ : C.integersˣ) : C.integers) := by
    rw [hu] at hmul
    exact (eq_inv_of_mul_eq_one_right hmul).symm
  rw [hginv]
  exact ((u⁻¹ : C.integersˣ) : C.integers).2

p2m_export "AlgebraicCurve.ComponentChart" "inv_mem_of_residue_ne_zero"

private theorem _root_.AlgebraicCurve.ComponentChart.const_mem_of_smul_unit (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers)
    (hfres : C.residue ⟨f, hf⟩ ≠ 0) {c : L} (hcf : c • f ∈ C.integers)
    (hcfres : C.residue ⟨c • f, hcf⟩ ≠ 0) : c ∈ A ∧ c⁻¹ ∈ A := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hfres
    have : (⟨0, hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have hfinv : f⁻¹ ∈ C.integers := C.inv_mem_of_residue_ne_zero hf hfres
  have hginv : (c • f)⁻¹ ∈ C.integers := C.inv_mem_of_residue_ne_zero hcf hcfres
  have hcF : algebraMap L F c = (c • f) * f⁻¹ := by
    rw [Algebra.smul_def, mul_assoc, mul_inv_cancel₀ hf0, mul_one]
  have hcinvF : algebraMap L F c⁻¹ = f * (c • f)⁻¹ := by
    rw [Algebra.smul_def, mul_inv, map_inv₀, ← mul_assoc, mul_comm f, mul_assoc, mul_inv_cancel₀ hf0,
      mul_one]
  constructor
  · rw [← C.algebraMap_mem_iff, hcF]; exact mul_mem hcf hfinv
  · rw [← C.algebraMap_mem_iff, hcinvF]; exact mul_mem hf hginv

p2m_export "AlgebraicCurve.ComponentChart" "const_mem_of_smul_unit"

private theorem _root_.AlgebraicCurve.ComponentChart.ord_residue_smul_eq (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar)
    {f : F} (hf : f ∈ C.integers) {c : L} (hcA : c ∈ A) (hcu : IsUnit (⟨c, hcA⟩ : A))
    (hcf : c • f ∈ C.integers) :
    x.ord (C.residue ⟨c • f, hcf⟩) = x.ord (C.residue ⟨f, hf⟩) := by
  have hcres : C.residue ⟨algebraMap L F c, (C.algebraMap_mem_iff c).mpr hcA⟩
      = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A ⟨c, hcA⟩) :=
    C.residue_algebraMap ⟨c, hcA⟩
  have hcres0 : algebraMap (ResidueField A) Fbar (IsLocalRing.residue A ⟨c, hcA⟩) ≠ 0 := by
    rw [map_ne_zero]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hcu
  have hsplit : (⟨c • f, hcf⟩ : C.integers)
      = ⟨algebraMap L F c, (C.algebraMap_mem_iff c).mpr hcA⟩ * ⟨f, hf⟩ :=
    Subtype.ext (Algebra.smul_def c f)
  rw [hsplit, map_mul, hcres]
  by_cases hfr : C.residue ⟨f, hf⟩ = 0
  · rw [hfr, mul_zero]
  · rw [Place.ord_mul _ hcres0 hfr,
      ConstantReduction.ord_algebraMap x ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hcu), zero_add]

p2m_export "AlgebraicCurve.ComponentChart" "ord_residue_smul_eq"
end ComponentChart
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

namespace Ws23
namespace SlopeLawW

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve.NodeLocalized P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.CentredSigma P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.SlopeLaw0 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.Jump"

section Core

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
  [CharP k q] [IsAlgClosed k] [DecidableEq k]

theorem pow_q_eq_self_of_wide {a : k} (hw : a = 0 ∨ a = 1728) : a ^ q = a := by
  rcases hw with rfl | rfl
  · exact zero_pow (Fact.out : q.Prime).ne_zero
  · have h : ((1728 : ℕ) : k) ^ q = ((1728 : ℕ) : k) := by
      have := map_natCast (frobenius k q) 1728
      rwa [frobenius_def] at this
    exact_mod_cast h

theorem isUnit_evalAt_wide_of_gaussPair (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (hq : 5 ≤ q)
    (a : k) (ha : a ∈ ssJSet q k) (hw : a = 0 ∨ a = 1728)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W → W.ord f = 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : Centred red a W) :
    ∃ h : W.evalAt f ∈ A, IsUnit (⟨_, h⟩ : A) := by
  rcases hw with rfl | rfl
  · exact ModularCurve.NodeLocalized.isUnit_evalAt_zero_of_gaussPair_of_isAlgClosed red hker ha hq f h₁ h₁u h₂ h₂u
      (fun W h => hford W h) W hW
  · exact ModularCurve.NodeLocalized.isUnit_evalAt_ofNat1728_of_gaussPair_of_isAlgClosed red hker ha hq f h₁ h₁u h₂ h₂u
      (fun W h => hford W h) W hW

theorem exists_zeroChart_slopeData_wide (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hw : a = 0 ∨ a = 1728)
    (z z' : ↥(modularFunctionFieldBar (1 * q)))
    (hmod : z' * z = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a))
    (hzg : ∃ (h : ((frickeInvolutionBar (1 * q) z : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * q) A.toSubring red),
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hzg' : ∃ (h : ((z' : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * q) A.toSubring red),
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hzW : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W →
        z ∈ W.toValuationSubring ∧ W.evalAt z ≠ 0)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W → W.ord f = 0) :
    ∃ (d : AlgebraicClosure ℚ) (m : ℤ)
      (h₂ : ((frickeInvolutionBar (1 * q) ((d • f : modularFunctionFieldBar (1 * q))) : modularFunctionFieldBar (1 * q)) :
          LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1),
      d ≠ 0 ∧ CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0 ∧
      (charLGeomPlaceOfPoint k (a ^ q)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC k 1)) = m ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W →
        UnitA A (d * W.evalAt f * W.evalAt z ^ (-m)) := by
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have haq : a ^ q = a := pow_q_eq_self_of_wide hw
  have he0 : jWidth a ≠ 0 := by unfold jWidth; split_ifs <;> norm_num

  set g : ↥(modularFunctionFieldBar (1 * q)) := frickeInvolutionBar (1 * q) f with hg
  have hg0 : g ≠ 0 := (map_ne_zero_iff _ (frickeInvolutionBar (1 * q)).injective).mpr hf
  have hford_g : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W → W.ord g = 0 := by
    intro W hW
    have h := forall_centred_ord_smul_eq_zero red ha2 hford W
    rw [haq] at h
    exact h hW

  obtain ⟨c', hc'0, m', hdvd, k₁, k₂, k₁F, k₁u, k₂u, hordN⟩ :=
    ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728
      red hker hq a ha ha2 hw g hg0 hford_g
  obtain ⟨N, hN⟩ := hdvd

  have eσ : frickeInvolutionBar (1 * q) ((c' • f : modularFunctionFieldBar (1 * q))) = c' • g := by
    rw [hg, Ws23.CentredSigma.frickeInvolutionBar_smul']
  have h₂ : ((frickeInvolutionBar (1 * q) ((c' • f : modularFunctionFieldBar (1 * q))) : modularFunctionFieldBar (1 * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [eσ]; exact k₁
  have heq₂ : (⟨_, h₂⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, k₁⟩ :=
    Subtype.ext (congrArg (fun t : ↥(modularFunctionFieldBar (1 * q)) => (t : LaurentSeries (AlgebraicClosure ℚ))) eσ)
  have h₂F := modularRedLocHom_mem_one red ⟨_, h₂⟩
  have h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0 := by rw [heq₂]; exact k₁u
  set m : ℤ := (charLGeomPlaceOfPoint k (a ^ q)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC k 1)) with hm
  have hem : ((jWidth a : ℕ) : ℤ) * m = -m' := by
    rw [← hordN, frobNodePair_fst, hm, haq]
    congr 1
    rw [rlHom_eq red, rlHom_eq red, heq₂]
  have hmN : m = -N := by
    rw [hN] at hem
    have : ((jWidth a : ℕ) : ℤ) * (m + N) = 0 := by rw [mul_add, hem]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by exact_mod_cast h) he0
    · omega
  refine ⟨c', m, h₂, h₂F, hc'0, h₂u, rfl, ?_⟩

  intro W hW
  have hWrat : W.IsRational := Ws23.Jump.isRational_W W
  set e₀ : AlgebraicClosure ℚ := c' * (q : AlgebraicClosure ℚ) ^ m' with he₀
  have he₀0 : e₀ ≠ 0 := mul_ne_zero hc'0 (zpow_ne_zero _ hq0)
  set G₀ : ↥(modularFunctionFieldBar (1 * q)) := (e₀ • f) * z' ^ m with hG₀

  have hk₂' : ((e₀ • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    have : frickeInvolutionBar (1 * q) (((c' * (q : AlgebraicClosure ℚ) ^ m') • g : modularFunctionFieldBar (1 * q))) = e₀ • f := by
      rw [hg, Ws23.CentredSigma.frickeInvolutionBar_smul', frickeInvolutionBar_frickeInvolutionBar]
    rw [← this]; exact k₂
  have hk₂u' : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hk₂'⟩ ≠ 0 := by
    have e1 : frickeInvolutionBar (1 * q) (((c' * (q : AlgebraicClosure ℚ) ^ m') • g : modularFunctionFieldBar (1 * q))) = e₀ • f := by
      rw [hg, Ws23.CentredSigma.frickeInvolutionBar_smul', frickeInvolutionBar_frickeInvolutionBar]
    have : (⟨_, hk₂'⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, k₂⟩ :=
      Subtype.ext (congrArg (fun t : ↥(modularFunctionFieldBar (1 * q)) => (t : LaurentSeries (AlgebraicClosure ℚ))) e1.symm)
    rw [this]; exact k₂u
  have hGauss1 : ∃ h : ((G₀ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 := by
    have hcoe : ((G₀ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = ((e₀ • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * ((z' : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ^ m := by
      simp only [hG₀, MulMemClass.coe_mul, coe_zpow']
    exact CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hcoe.symm
      (CharPReduction.gaussUnit_mul (1 * q) A.toSubring red ⟨hk₂', hk₂u'⟩ (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hzg' m))

  have hz0 : z ≠ 0 := by
    intro h0
    obtain ⟨hzm, hz0'⟩ := hzg
    apply hz0'
    have : (⟨_, hzm⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 0 :=
      Subtype.ext (by show ((frickeInvolutionBar (1 * q) z : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _; rw [h0, map_zero]; rfl)
    rw [this, map_zero]
  have hσz0 : frickeInvolutionBar (1 * q) z ≠ 0 := (map_ne_zero_iff _ (frickeInvolutionBar (1 * q)).injective).mpr hz0
  have hσz' : frickeInvolutionBar (1 * q) z' = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) * (frickeInvolutionBar (1 * q) z)⁻¹ := by
    have h := congrArg (frickeInvolutionBar (1 * q)) hmod
    rw [map_mul, AlgEquiv.commutes] at h
    rw [← h, mul_assoc, mul_inv_cancel₀ hσz0, mul_one]
  have hX0 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero _).mpr hq0
  have hσG₀ : frickeInvolutionBar (1 * q) G₀ = ((q : AlgebraicClosure ℚ) ^ (m' + (jWidth a : ℤ) * m)) • ((c' • g) * (frickeInvolutionBar (1 * q) z) ^ (-m)) := by
    have h1 : frickeInvolutionBar (1 * q) G₀ = (e₀ • g) * (frickeInvolutionBar (1 * q) z') ^ m := by
      rw [hG₀, map_mul, map_zpow₀, Ws23.CentredSigma.frickeInvolutionBar_smul', ← hg]
    have h2 : (frickeInvolutionBar (1 * q) z') ^ m
        = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ)) ^ ((jWidth a : ℤ) * m)
          * (frickeInvolutionBar (1 * q) z) ^ (-m) := by
      rw [hσz', mul_zpow, inv_zpow', map_pow, ← zpow_natCast, ← zpow_mul]
      all_goals first | (push_cast; ring) | ring
    have h3 : (e₀ • g : ↥(modularFunctionFieldBar (1 * q))) = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c')
        * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ)) ^ m' * g := by
      rw [Algebra.smul_def, he₀, map_mul, map_zpow₀]
    rw [h1, h2, h3, Algebra.smul_def, Algebra.smul_def, map_zpow₀, zpow_add₀ hX0]
    ring
  have hexp : m' + (jWidth a : ℤ) * m = 0 := by rw [hmN, hN]; ring
  have hσG₀' : frickeInvolutionBar (1 * q) G₀ = (c' • g) * (frickeInvolutionBar (1 * q) z) ^ (-m) := by
    rw [hσG₀, hexp, zpow_zero, one_smul]
  have hGauss2 : ∃ h : ((frickeInvolutionBar (1 * q) G₀ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 := by
    have hcoe : ((frickeInvolutionBar (1 * q) G₀ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = ((c' • g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * ((frickeInvolutionBar (1 * q) z : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ^ (-m) := by
      rw [hσG₀']; simp only [MulMemClass.coe_mul, coe_zpow']
    exact CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hcoe.symm
      (CharPReduction.gaussUnit_mul (1 * q) A.toSubring red ⟨k₁, k₁u⟩ (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hzg (-m)))

  have hzval : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W →
      W.HasValue z (W.evalAt z) ∧ W.evalAt z ≠ 0 := by
    intro W hW
    obtain ⟨hzm, hzne⟩ := hzW W hW
    exact ⟨⟨hzm, (W.algebraMap_evalAt (Ws23.Jump.isRational_W W) hzm).symm⟩, hzne⟩
  have hz'val : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W →
      W.HasValue z' ((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) * (W.evalAt z)⁻¹) := by
    intro W hW
    obtain ⟨hv, hne⟩ := hzval W hW
    have hz'eq : z' = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) * z⁻¹ := by
      rw [← hmod, mul_assoc, mul_inv_cancel₀ hz0, mul_one]
    rw [hz'eq]
    exact (W.hasValue_algebraMap _).mul (hv.inv hne)
  have hqe0 : (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero)
  have hford_G₀ : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W → W.ord G₀ = 0 := by
    intro W hW
    obtain ⟨hv, hne⟩ := hzval W hW
    have hz'0 : z' ≠ 0 := by
      intro h0; apply hqe0
      have := hmod; rw [h0, zero_mul] at this
      exact ((map_ne_zero _).mpr hqe0 this.symm).elim
    have hordz' : W.ord z' = 0 := (hz'val W hW).ord_eq_zero (mul_ne_zero hqe0 (inv_ne_zero hne))
    rw [hG₀, Place.ord_mul _ (smul_ne_zero he₀0 hf) (zpow_ne_zero _ hz'0), Algebra.smul_def,
      ord_algebraMap_mul W he₀0 hf, hford W hW, ord_zpow' _ hz'0, hordz', mul_zero, add_zero]

  obtain ⟨hG₀mem, hG₀u⟩ := isUnit_evalAt_wide_of_gaussPair red hker hq a ha hw G₀ hGauss1.1 hGauss1.2 hGauss2.1 hGauss2.2 hford_G₀ W hW

  obtain ⟨hv, hne⟩ := hzval W hW
  have hfmem : f ∈ W.toValuationSubring := W.mem_toValuationSubring_of_ord_nonneg_alt hf (hford W hW).ge
  have hef : W.evalAt (e₀ • f) = e₀ * W.evalAt f := by
    rw [Algebra.smul_def, W.evalAt_mul_of_mem hWrat (W.algebraMap_mem' e₀) hfmem, W.evalAt_algebraMap_eq]
  have hz'pow : W.HasValue (z' ^ m) (((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) * (W.evalAt z)⁻¹) ^ m) :=
    Place.hasValue_zpow_of_hasValue (hz'val W hW) (mul_ne_zero hqe0 (inv_ne_zero hne)) m
  have hefmem : (e₀ • f : ↥(modularFunctionFieldBar (1 * q))) ∈ W.toValuationSubring := by
    rw [Algebra.smul_def]; exact mul_mem (W.algebraMap_mem' _) hfmem
  have hG₀val : W.evalAt G₀ = e₀ * W.evalAt f * (((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) * (W.evalAt z)⁻¹) ^ m) := by
    rw [hG₀, W.evalAt_mul_of_mem hWrat hefmem hz'pow.mem, hef, Place.evalAt_eq_of_hasValue' hz'pow]
  refine UnitA.congr ⟨hG₀mem, hG₀u⟩ ?_
  rw [hG₀val, he₀, mul_zpow, inv_zpow', ← zpow_natCast, ← zpow_mul]
  have : (q : AlgebraicClosure ℚ) ^ m' * ((q : ℕ) : AlgebraicClosure ℚ) ^ ((jWidth a : ℤ) * m) = 1 := by
    push_cast
    rw [← zpow_add₀ hq0, hexp, zpow_zero]
  push_cast at this ⊢
  calc c' * (q : AlgebraicClosure ℚ) ^ m' * W.evalAt f * ((q : AlgebraicClosure ℚ) ^ ((jWidth a : ℤ) * m) * W.evalAt z ^ (-m))
      = c' * W.evalAt f * W.evalAt z ^ (-m) * ((q : AlgebraicClosure ℚ) ^ m' * (q : AlgebraicClosure ℚ) ^ ((jWidth a : ℤ) * m)) := by ring
    _ = c' * W.evalAt f * W.evalAt z ^ (-m) := by rw [this, mul_one]

end Core
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

end Ws23.SlopeLawW
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

namespace Ws23
namespace SlopeLawW

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve.NodeLocalized P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.CentredSigma P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.SlopeLaw0 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.Jump"

section CoreInfty

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
  [CharP k q] [IsAlgClosed k] [DecidableEq k]

theorem exists_inftyChart_slopeData_wide (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hw : a = 0 ∨ a = 1728)
    (z z' : ↥(modularFunctionFieldBar (1 * q)))
    (hmod : z' * z = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a))
    (hzg : ∃ (h : ((frickeInvolutionBar (1 * q) z : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * q) A.toSubring red),
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hzg' : ∃ (h : ((z' : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * q) A.toSubring red),
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hz'W : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W →
        z' ∈ W.toValuationSubring ∧ W.evalAt z' ≠ 0)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W → W.ord f = 0) :
    ∃ (d : AlgebraicClosure ℚ) (m : ℤ)
      (h₁ : ((d • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1),
      d ≠ 0 ∧ CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 ∧
      (charLGeomPlaceOfPoint k a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) = m ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W →
        UnitA A (d * W.evalAt f * W.evalAt z' ^ (-m)) := by
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have he0 : jWidth a ≠ 0 := by unfold jWidth; split_ifs <;> norm_num

  obtain ⟨c', hc'0, m', hdvd, k₁, k₂, k₁F, k₁u, k₂u, hordN⟩ :=
    ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728
      red hker hq a ha ha2 hw f hf hford
  obtain ⟨N, hN⟩ := hdvd
  set m : ℤ := (charLGeomPlaceOfPoint k a).ord (⟨_, k₁F⟩ : ↥(modularFunctionFieldC k 1)) with hm
  have hem : ((jWidth a : ℕ) : ℤ) * m = -m' := by rw [← hordN, frobNodePair_fst]
  have hmN : m = -N := by
    rw [hN] at hem
    have : ((jWidth a : ℕ) : ℤ) * (m + N) = 0 := by rw [mul_add, hem]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by exact_mod_cast h) he0
    · omega
  have hexp : m' + (jWidth a : ℤ) * m = 0 := by rw [hmN, hN]; ring
  refine ⟨c', m, k₁, k₁F, hc'0, k₁u, rfl, ?_⟩
  intro W hW
  have hWrat : W.IsRational := Ws23.Jump.isRational_W W

  set G₀ : ↥(modularFunctionFieldBar (1 * q)) := (c' • f) * z' ^ (-m) with hG₀
  have hGauss1 : ∃ h : ((G₀ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 := by
    have hcoe : ((G₀ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = ((c' • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * ((z' : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ^ (-m) := by
      simp only [hG₀, MulMemClass.coe_mul, coe_zpow']
    exact CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hcoe.symm
      (CharPReduction.gaussUnit_mul (1 * q) A.toSubring red ⟨k₁, k₁u⟩ (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hzg' (-m)))

  have hz0 : z ≠ 0 := by
    intro h0
    obtain ⟨hzm, hz0'⟩ := hzg
    apply hz0'
    have : (⟨_, hzm⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 0 :=
      Subtype.ext (by show ((frickeInvolutionBar (1 * q) z : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _; rw [h0, map_zero]; rfl)
    rw [this, map_zero]
  have hσz0 : frickeInvolutionBar (1 * q) z ≠ 0 := (map_ne_zero_iff _ (frickeInvolutionBar (1 * q)).injective).mpr hz0
  have hX0 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero _).mpr hq0
  have hσz' : frickeInvolutionBar (1 * q) z' = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) * (frickeInvolutionBar (1 * q) z)⁻¹ := by
    have h := congrArg (frickeInvolutionBar (1 * q)) hmod
    rw [map_mul, AlgEquiv.commutes] at h
    rw [← h, mul_assoc, mul_inv_cancel₀ hσz0, mul_one]
  have hσG₀ : frickeInvolutionBar (1 * q) G₀
      = frickeInvolutionBar (1 * q) (((c' * (q : AlgebraicClosure ℚ) ^ m') • f : modularFunctionFieldBar (1 * q))) * (frickeInvolutionBar (1 * q) z) ^ m := by
    have h2 : (frickeInvolutionBar (1 * q) z') ^ (-m)
        = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ)) ^ m'
          * (frickeInvolutionBar (1 * q) z) ^ m := by
      rw [hσz', mul_zpow, inv_zpow', neg_neg, map_pow, ← zpow_natCast, ← zpow_mul]
      have : ((jWidth a : ℕ) : ℤ) * -m = m' := by rw [hmN, hN]; ring
      rw [this]
    rw [hG₀, map_mul, map_zpow₀, h2, Ws23.CentredSigma.frickeInvolutionBar_smul', Ws23.CentredSigma.frickeInvolutionBar_smul',
      Algebra.smul_def, Algebra.smul_def, map_mul, map_zpow₀]
    ring
  have hGauss2 : ∃ h : ((frickeInvolutionBar (1 * q) G₀ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 := by
    have hcoe : ((frickeInvolutionBar (1 * q) G₀ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = ((frickeInvolutionBar (1 * q) (((c' * (q : AlgebraicClosure ℚ) ^ m') • f : modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
          * ((frickeInvolutionBar (1 * q) z : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ^ m := by
      rw [hσG₀]; simp only [MulMemClass.coe_mul, coe_zpow']
    exact CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hcoe.symm
      (CharPReduction.gaussUnit_mul (1 * q) A.toSubring red ⟨k₂, k₂u⟩ (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hzg m))

  have hz'val : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W →
      W.HasValue z' (W.evalAt z') ∧ W.evalAt z' ≠ 0 := by
    intro W hW
    obtain ⟨hzm, hzne⟩ := hz'W W hW
    exact ⟨⟨hzm, (W.algebraMap_evalAt (Ws23.Jump.isRational_W W) hzm).symm⟩, hzne⟩
  have hz'0 : z' ≠ 0 := by
    intro h0
    have := hmod; rw [h0, zero_mul] at this
    exact (pow_ne_zero _ hX0) (by rw [map_pow] at this; exact this.symm)
  have hford_G₀ : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W → W.ord G₀ = 0 := by
    intro W hW
    obtain ⟨hv, hne⟩ := hz'val W hW
    rw [hG₀, Place.ord_mul _ (smul_ne_zero hc'0 hf) (zpow_ne_zero _ hz'0), Algebra.smul_def,
      ord_algebraMap_mul W hc'0 hf, hford W hW, ord_zpow' _ hz'0, hv.ord_eq_zero hne, mul_zero, add_zero]

  obtain ⟨hG₀mem, hG₀u⟩ := isUnit_evalAt_wide_of_gaussPair red hker hq a ha hw G₀ hGauss1.1 hGauss1.2 hGauss2.1 hGauss2.2 hford_G₀ W hW
  obtain ⟨hv, hne⟩ := hz'val W hW
  have hfmem : f ∈ W.toValuationSubring := W.mem_toValuationSubring_of_ord_nonneg_alt hf (hford W hW).ge
  have hcfmem : (c' • f : ↥(modularFunctionFieldBar (1 * q))) ∈ W.toValuationSubring := by
    rw [Algebra.smul_def]; exact mul_mem (W.algebraMap_mem' _) hfmem
  have hcf : W.evalAt (c' • f) = c' * W.evalAt f := by
    rw [Algebra.smul_def, W.evalAt_mul_of_mem hWrat (W.algebraMap_mem' c') hfmem, W.evalAt_algebraMap_eq]
  have hz'pow : W.HasValue (z' ^ (-m)) ((W.evalAt z') ^ (-m)) := Place.hasValue_zpow_of_hasValue hv hne (-m)
  have hG₀val : W.evalAt G₀ = c' * W.evalAt f * W.evalAt z' ^ (-m) := by
    rw [hG₀, W.evalAt_mul_of_mem hWrat hcfmem hz'pow.mem, hcf, Place.evalAt_eq_of_hasValue' hz'pow]
  exact UnitA.congr ⟨hG₀mem, hG₀u⟩ hG₀val

end CoreInfty
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

end Ws23.SlopeLawW
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

namespace Ws23
namespace SlopeLawW
p2m_open "IsLocalRing AlgebraicCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.CentredSigma P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.Jump"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem slopeLaw_oppAnnulus_inftyChart_wide_aux (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p) (n : ℕ) [NeZero n] (hn : n = 1 * p)
    {Fbari : Type} [Field Fbari] [Algebra (IsLocalRing.ResidueField ↥A) Fbari]
    (Ci : ComponentChart A ↥(modularFunctionFieldBar n) Fbari)
    (xi : Place (IsLocalRing.ResidueField ↥A) Fbari)
    (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) (ha2 : a ^ (p ^ 2) = a)
    (hw : a = 0 ∨ a = 1728)
    (An : Annulus A ↥(modularFunctionFieldBar n))
    (z' z : ↥(modularFunctionFieldBar n)) (hz' : An.param = z')
    (hmod : z' * z = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar n) (((p : ℕ) : AlgebraicClosure ℚ) ^ jWidth a))
    (hzg : ∃ (h : ((frickeInvolutionBar n z : modularFunctionFieldBar n) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized n A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom n A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0)
    (hzg' : ∃ (h : ((z' : modularFunctionFieldBar n) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized n A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom n A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0)
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar n), W ∈ An.dom ↔
          ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full n (jq_mem n))⟩ : modularFunctionFieldBar n)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar n) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ n jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full n (dvd_refl n))⟩ :
                modularFunctionFieldBar n)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar n) (y : AlgebraicClosure ℚ)))))
    (huniti : ∀ (g : ↥(modularFunctionFieldBar n))
        (h₁ : ((g : modularFunctionFieldBar n) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized n A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom n A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ≠ 0 →
        ∃ hg : g ∈ Ci.integers, Ci.residue ⟨g, hg⟩ ≠ 0)
    (hordresi : ∀ (g : ↥(modularFunctionFieldBar n)) (hg : g ∈ Ci.integers)
        (h₁ : ((g : modularFunctionFieldBar n) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized n A.toSubring (IsLocalRing.residue ↥A))
        (h₁F : CharPReduction.modularRedLocHom n A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        xi.ord (Ci.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    ∀ (f : ↥(modularFunctionFieldBar n)) (hf : f ∈ Ci.integers), Ci.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) →
      ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(xi.ord (Ci.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A) := by
  subst hn
  intro f hf hfres hford P hP
  have hker : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A :=
    fun c => IsLocalRing.residue_eq_zero_iff c
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hfres
    have : (⟨0, hf⟩ : Ci.integers) = 0 := rfl
    rw [this, map_zero]

  have hz'W : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), Centred (IsLocalRing.residue ↥A) a W →
      z' ∈ W.toValuationSubring ∧ W.evalAt z' ≠ 0 := by
    intro W hW
    obtain ⟨-, hzm, -, hzne, -⟩ := An.mem_dom W ((hdom W).mpr hW)
    rw [hz'] at hzm hzne
    exact ⟨hzm, hzne⟩
  obtain ⟨d, m, h₂, h₂F, hd0, h₂u, hord, hunitW⟩ :=
    exists_inftyChart_slopeData_wide (IsLocalRing.residue ↥A) hker hp5 a ha ha2 hw z z' hmod hzg hzg' hz'W f hf0
      (fun W hW => hford W ((hdom W).mpr hW))

  obtain ⟨hgC, hgres⟩ := huniti (d • f) h₂ h₂u
  obtain ⟨hdA, hdinvA⟩ := Ci.const_mem_of_smul_unit hf hfres hgC hgres
  have hdunit : IsUnit (⟨d, hdA⟩ : ↥A) :=
    ⟨⟨⟨d, hdA⟩, ⟨d⁻¹, hdinvA⟩, Subtype.ext (mul_inv_cancel₀ hd0), Subtype.ext (inv_mul_cancel₀ hd0)⟩, rfl⟩
  have hn : xi.ord (Ci.residue ⟨f, hf⟩) = m := by
    rw [← Ci.ord_residue_smul_eq xi hf hdA hdunit hgC, hordresi (d • f) hgC h₂ h₂F]
    exact hord
  rw [hn, hz']

  obtain ⟨hmem, hu⟩ := hunitW P ((hdom P).mp hP)
  have hquot : P.evalAt f * P.evalAt z' ^ (-m) = d⁻¹ * (d * P.evalAt f * P.evalAt z' ^ (-m)) := by
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul (P.evalAt f)]
  have hmemA : P.evalAt f * P.evalAt z' ^ (-m) ∈ A := by
    rw [hquot]; exact mul_mem hdinvA hmem
  refine ⟨hmemA, ?_⟩
  have hprod : (⟨_, hmemA⟩ : ↥A) = ⟨d⁻¹, hdinvA⟩ * ⟨_, hmem⟩ := Subtype.ext hquot
  rw [hprod]
  refine IsUnit.mul ?_ hu
  exact ⟨⟨⟨d⁻¹, hdinvA⟩, ⟨d, hdA⟩, Subtype.ext (inv_mul_cancel₀ hd0), Subtype.ext (mul_inv_cancel₀ hd0)⟩, rfl⟩

end Ws23.SlopeLawW
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23 P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.Ws23.NodePlaceAPI"

p2m_open "ModularCurve~coeffEmb_jq" in open Ws23.SlopeLawW _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing _root_.P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ)
    [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbari : Type}
    [Field Fbari]
    [Algebra (IsLocalRing.ResidueField ↥A) Fbari]
    (Ci : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) Fbari)
    (xi : Place (IsLocalRing.ResidueField ↥A) Fbari)
    (a : IsLocalRing.ResidueField ↥A)
    (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A))
    (ha2 : a ^ (p ^ 2) = a)
    (hw : a = 0 ∨ a = 1728)
    (hnodesi : xi ∈ Ci.nodes)
    (An' : Annulus A ↥(modularFunctionFieldBar (1 * p)))
    (z' z : ↥(modularFunctionFieldBar (1 * p)))
    (hz' : An'.param = z')
    (hmod : z' * z = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((An'.modulus : ↥A) : AlgebraicClosure ℚ))
    (hmodw : An'.modulus = ((p : ℕ) : ↥A) ^ jWidth a)
    (hdom' : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), W ∈ An'.dom ↔
          ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (y : AlgebraicClosure ℚ)))))
    (hzg' : ∃ (h : ((z' : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
         (hF : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
         CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0 ∧
         (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, hF⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 1)
    (hzg : ∃ (h : ((frickeInvolutionBar (1 * p) z : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
         (hF : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
         CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0 ∧
         (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, hF⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 1)
    (huniti : ∀ (g : ↥(modularFunctionFieldBar (1 * p)))
        (h₁ : ((g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ≠ 0 →
        ∃ hg : g ∈ Ci.integers, Ci.residue ⟨g, hg⟩ ≠ 0)
    (hordresi : ∀ (g : ↥(modularFunctionFieldBar (1 * p))) (hg : g ∈ Ci.integers)
        (h₁ : ((g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
        (h₁F : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₁⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        xi.ord (Ci.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    An'.IsAttached Ci xi := by
  haveI : NeZero (1 * p) := ⟨by rw [one_mul]; exact (Fact.out : p.Prime).ne_zero⟩

  obtain ⟨hzm, hzF, hzne, hzord⟩ := hzg'
  obtain ⟨hzC, hzres⟩ := huniti z' hzm hzne
  have hz1 : xi.ord (Ci.residue ⟨z', hzC⟩) = 1 := by rw [hordresi z' hzC hzm hzF]; exact hzord

  have hmod' : z' * z = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (((p : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) := by
    rw [hmod, hmodw]; push_cast; rfl
  subst hz'
  refine ⟨hnodesi, hzC, hz1, ?_⟩

  exact slopeLaw_oppAnnulus_inftyChart_wide_aux p A hp5 (1 * p) rfl Ci xi a ha ha2 hw An' An'.param z rfl hmod'
    (hzg.elim fun h hh => ⟨h, hh.elim fun hF hr => hr.1⟩) ⟨hzm, hzne⟩ hdom' huniti hordresi

end
end S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
end P2MW
export P2MW.S_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne (solution)
