-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9ba3d8d2-d6f3-5c7d-af05-3dfa0d47be65

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
import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
import Theorems.Thm_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728
import Theorems.Thm_ModularCurve_NodeLocalized_exists_smul_gaussUnit
import Theorems.Thm_ModularCurve_exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_exists_hasValue_frobNodePair_of_forall_pole_not_centred
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_NodeLocalized
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

namespace P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728
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

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve"

noncomputable section

namespace Ws23
namespace NodePlaceAPI

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing Polynomial"

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

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing Polynomial ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve"

section PlaceLemmas2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_eq_of_hasValue' {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) : v.evalAt g = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap]

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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23"

namespace Ws23
namespace NodePlaceAPI

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve AlgebraicCurve.RationalFunctionField~ord_placeOfPoint_algebraMap IsLocalRing Polynomial ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve"

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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end Ws23.NodePlaceAPI
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.modularRedLocHom_mem CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem modularFunctionFieldC_one qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full NodeLocalized.exists_hasValue_nodeCoord_of_centred frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet deg_eq_one_modularFunctionFieldBar frobNodePair frobNodePair_fst ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728 jWidth gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728 NodeLocalized.exists_smul_gaussUnit exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing exists_hasValue_frobNodePair_of_forall_pole_not_centred"
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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap Place.deg Place.ord_zero Place.ord_mul Place.smulRingEquiv Place.coe_smulRingEquiv_apply Place.smul_toValuationSubring Place.ord_smul Place.smulResidueAlgEquiv Place.residue_algebraMap GluedPic0 Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.heightOneSpectrumOfIrreducible RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum RationalFunctionField.residueOfHeightOneSpectrum RationalFunctionField.residueOfHeightOneSpectrum_apply RationalFunctionField.ker_residueOfHeightOneSpectrum RationalFunctionField.placeOfPoint Place.comapSymmRingEquiv Place.coe_comapSymmRingEquiv_apply Place.congrRingEquiv Place.ord_congrRingEquiv Place.evalAt GaussReduction.ord_nonneg_of_mem_gen StandardAnnulus.ord_placeOfPoint_X_sub_C_self Place.mem_smul_iff' Place.hasValue_smul Place.isRational_smul Place.evalAt_smul"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg ord ord_zero ord_mul ord_coe_unit ord_zpow smulRingEquiv coe_smulRingEquiv_apply smul_toValuationSubring ord_smul smulResidueAlgEquiv algebraMap_mem' toValuationSubring residue_algebraMap HasValue hasValue_one hasValue_algebraMap ord_ofHeightOneSpectrum_ne_zero_iff comapSymmRingEquiv coe_comapSymmRingEquiv_apply congrRingEquiv ord_congrRingEquiv IsRational residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt mem_toValuationSubring_of_ord_nonneg_alt mem_smul_iff' hasValue_smul isRational_smul evalAt_smul"
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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.modularRedLocHom_mem CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem modularFunctionFieldC_one qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full NodeLocalized.exists_hasValue_nodeCoord_of_centred frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet deg_eq_one_modularFunctionFieldBar frobNodePair frobNodePair_fst ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728 jWidth gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728 NodeLocalized.exists_smul_gaussUnit exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing exists_hasValue_frobNodePair_of_forall_pole_not_centred"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "exists_hasValue_nodeCoord_of_centred modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict exists_smul_gaussUnit coeffSubring_eq_or_isDiscreteValuationRing"
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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end ModularCurve.NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace E4b80310

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

section WSide

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

def jE (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩

def jqE (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

variable (A) in

def evalF (q : ℕ) [Fact q.Prime] : MvPolynomial (Fin 2) ↥A.toSubring →+* ↥(modularFunctionFieldBar (1 * q)) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).comp A.toSubring.subtype) ![jE q, jqE q]

theorem coe_evalF (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    ((evalF A q P : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) A.toSubring P := by
  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (algebraMap ↥(modularFunctionFieldBar (1 * q)) (LaurentSeries (AlgebraicClosure ℚ))).comp (evalF A q)
  have hφ : φ = modularEval (1 * q) A.toSubring := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · show algebraMap _ _ (evalF A q (MvPolynomial.C c)) = modularEval (1 * q) A.toSubring (MvPolynomial.C c)
      rw [evalF, MvPolynomial.eval₂Hom_C, modularEval, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply]
      rfl
    · show algebraMap _ _ (evalF A q (MvPolynomial.X 0)) = modularEval (1 * q) A.toSubring (MvPolynomial.X 0)
      rw [evalF, MvPolynomial.eval₂Hom_X', modularEval, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero,
        Matrix.cons_val_zero, IntermediateField.algebraMap_apply]
      exact coeffEmb_jq
    · show algebraMap _ _ (evalF A q (MvPolynomial.X 1)) = modularEval (1 * q) A.toSubring (MvPolynomial.X 1)
      rw [evalF, MvPolynomial.eval₂Hom_X', modularEval, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero, IntermediateField.algebraMap_apply]
      exact coeffEmb_qExpand_jq (1 * q)
  have := RingHom.congr_fun hφ P
  rw [← this]
  rfl

theorem hasValue_evalF (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    {x y : ↥A.toSubring} (hx : W.HasValue (jE q) (x : AlgebraicClosure ℚ))
    (hy : W.HasValue (jqE q) (y : AlgebraicClosure ℚ)) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    W.HasValue (evalF A q P) ((MvPolynomial.eval ![x, y] P : ↥A.toSubring) : AlgebraicClosure ℚ) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [evalF, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C, RingHom.comp_apply]
      exact W.hasValue_algebraMap _
  | add p r hp hr =>
      rw [map_add, map_add, Subring.coe_add]
      exact hasValue_add hp hr
  | mul_X p i hp =>
      rw [map_mul, map_mul, Subring.coe_mul]
      refine hp.mul ?_
      rw [evalF, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X]
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · simpa using hx
      · simpa using hy

theorem red_eval {k : Type*} [Field k] (red : A →+* k) (x y : ↥A.toSubring) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    red (MvPolynomial.eval ![x, y] P) = pointEval A.toSubring red (red x) (red y) P := by
  have h : (red : ↥A.toSubring →+* k).comp (MvPolynomial.eval ![x, y]) = pointEval A.toSubring red (red x) (red y) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · rw [RingHom.comp_apply, MvPolynomial.eval_C, pointEval, MvPolynomial.eval₂Hom_C]
    · rw [RingHom.comp_apply, MvPolynomial.eval_X, pointEval, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero,
        Matrix.cons_val_zero]
    · rw [RingHom.comp_apply, MvPolynomial.eval_X, pointEval, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact RingHom.congr_fun h P

end WSide
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end E4b80310
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace E4b80310

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized"

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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end E4b80310
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace CentredSigma

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve"

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.mem_smul_iff' (g : F) :
    σ g ∈ (σ • v).toValuationSubring ↔ g ∈ v.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

p2m_alias "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve.Place.mem_smul_iff'" "AlgebraicCurve.Place.mem_smul_iff'"

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

p2m_alias "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve.Place.hasValue_smul" "AlgebraicCurve.Place.hasValue_smul"

private theorem _root_.AlgebraicCurve.Place.isRational_smul (hv : v.IsRational) : (σ • v).IsRational := by
  intro z
  obtain ⟨w, hw⟩ := (Place.smulResidueAlgEquiv σ v).surjective z
  obtain ⟨c, hc⟩ := hv w
  refine ⟨c, ?_⟩
  rw [← hw, ← hc]
  exact ((Place.smulResidueAlgEquiv σ v).commutes c).symm

p2m_alias "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve.Place.isRational_smul" "AlgebraicCurve.Place.isRational_smul"

private theorem _root_.AlgebraicCurve.Place.evalAt_smul (hv : v.IsRational) (g : F) :
    (σ • v).evalAt (σ g) = v.evalAt g := by
  by_cases hg : g ∈ v.toValuationSubring
  · have h1 : v.HasValue g (v.evalAt g) := ⟨hg, (v.algebraMap_evalAt hv hg).symm⟩
    have h2 := Place.hasValue_smul σ v h1
    rw [(σ • v).evalAt_of_mem h2.mem, h2.residue_eq, (σ • v).residueInv_algebraMap]
  · have hg' : σ g ∉ (σ • v).toValuationSubring := fun h => hg ((Place.mem_smul_iff' σ v g).mp h)
    rw [Place.evalAt, Place.evalAt, dif_neg hg, dif_neg hg']

p2m_alias "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve.Place.evalAt_smul" "AlgebraicCurve.Place.evalAt_smul"
end Generic
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

section Modular

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

private noncomputable def _root_.Ws23.CentredSigma.jE (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩

p2m_export "Ws23.CentredSigma" "jE"

private noncomputable def _root_.Ws23.CentredSigma.jqE (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

p2m_export "Ws23.CentredSigma" "jqE"
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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end Ws23.CentredSigma
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace SlopeLaw0

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.CentredSigma"

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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end Ws23.SlopeLaw0
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace Jump

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve"

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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end Ws23.Jump
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace Jump

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve"

section Torsion
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]

theorem unitA_natCast_of_not_dvd (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {b : ℕ} (hb : ¬ q ∣ b) : UnitA A ((b : AlgebraicClosure ℚ)) := by
  have hmemb : ((b : AlgebraicClosure ℚ)) ∈ A := by exact_mod_cast (natCast_mem A b)
  refine ⟨hmemb, ?_⟩
  by_contra hnu
  have hmem : (⟨(b : AlgebraicClosure ℚ), hmemb⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hnu
  have h0 := (hker _).mpr hmem
  have heq : (⟨(b : AlgebraicClosure ℚ), hmemb⟩ : A) = (b : A) := Subtype.ext (by push_cast; rfl)
  rw [heq, map_natCast] at h0
  exact hb ((CharP.cast_eq_zero_iff k q b).mp h0)

theorem exists_unitA_natCast_mul_zpow (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {b : ℕ} (hb : b ≠ 0) : ∃ n : ℤ, UnitA A ((b : AlgebraicClosure ℚ) * ((q : AlgebraicClosure ℚ)) ^ (-n)) := by
  obtain ⟨e, b', hb', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb q (Fact.out : q.Prime).one_lt.ne'
  refine ⟨e, ?_⟩
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  refine UnitA.congr (unitA_natCast_of_not_dvd red hker hb') ?_
  push_cast
  rw [zpow_neg, zpow_natCast, mul_comm ((q : AlgebraicClosure ℚ) ^ e), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one]

theorem exists_unitA_intCast_mul_zpow (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {z : ℤ} (hz : z ≠ 0) : ∃ n : ℤ, UnitA A ((z : AlgebraicClosure ℚ) * ((q : AlgebraicClosure ℚ)) ^ (-n)) := by
  have hnz : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  obtain ⟨n, hn⟩ := exists_unitA_natCast_mul_zpow red hker hnz
  refine ⟨n, ?_⟩
  rcases Int.natAbs_eq z with h | h
  · rw [h, Int.cast_natCast]; exact hn
  · rw [h, Int.cast_neg, Int.cast_natCast]
    have hneg : UnitA A (-1 : AlgebraicClosure ℚ) := by
      refine ⟨neg_mem (one_mem A), ?_⟩
      rw [show (⟨-(1 : AlgebraicClosure ℚ), neg_mem (one_mem A)⟩ : A) = -1 from rfl]
      exact isUnit_one.neg
    refine UnitA.congr (hneg.mul hn) ?_
    ring

theorem exists_unitA_zpow_mul_zpow (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {x : AlgebraicClosure ℚ} (hx : x ≠ 0) :
    ∃ (e n : ℤ), e ≠ 0 ∧ UnitA A (x ^ e * ((q : AlgebraicClosure ℚ)) ^ (-n)) := by
  classical

  obtain ⟨p, hp0, hpx⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)
  set P : Polynomial ℤ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) p with hP
  have hP0 : P ≠ 0 := fun h =>
    hp0 ((IsLocalization.integerNormalization_eq_zero_iff (M := nonZeroDivisors ℤ) le_rfl p).mp h)
  have hPx : Polynomial.aeval x P = 0 := IsLocalization.integerNormalization_aeval_eq_zero _ p hpx

  set t : ℕ → AlgebraicClosure ℚ := fun i => (P.coeff i : AlgebraicClosure ℚ) * x ^ i with ht
  have hsum : ∑ i ∈ Finset.range (P.natDegree + 1), t i = 0 := by
    rw [Polynomial.aeval_eq_sum_range] at hPx
    simpa only [ht, Algebra.smul_def, algebraMap_int_eq, eq_intCast] using hPx
  set S := (Finset.range (P.natDegree + 1)).filter (fun i => P.coeff i ≠ 0) with hS
  have hdS : P.natDegree ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.self_mem_range_succ _, by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hP0⟩
  have hSne : S.Nonempty := ⟨_, hdS⟩
  let v := A.valuation
  obtain ⟨i₀, hi₀S, hmax⟩ := Finset.exists_max_image S (fun i => v (t i)) hSne
  have ht0 : ∀ i ∈ S, t i ≠ 0 := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    exact mul_ne_zero (by exact_mod_cast hi.2) (pow_ne_zero _ hx)
  have hv0 : v (t i₀) ≠ 0 := (Valuation.ne_zero_iff v).mpr (ht0 _ hi₀S)

  have hexists : ∃ j ∈ S, j ≠ i₀ ∧ v (t j) = v (t i₀) := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ i ∈ (Finset.range (P.natDegree + 1)).erase i₀, v (t i) < v (t i₀) := by
      intro i hi
      rw [Finset.mem_erase] at hi
      by_cases hiS : i ∈ S
      · exact lt_of_le_of_ne (hmax i hiS) (hcon i hiS hi.1)
      · have : t i = 0 := by
          have : P.coeff i = 0 := by
            by_contra hne; exact hiS (by rw [hS, Finset.mem_filter]; exact ⟨hi.2, hne⟩)
          rw [ht]; simp [this]
        rw [this, map_zero]; exact zero_lt_iff.mpr hv0
    have hsum' : t i₀ + ∑ i ∈ (Finset.range (P.natDegree + 1)).erase i₀, t i = 0 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_of_mem_filter i₀ hi₀S)]; exact hsum
    have hlt2 := Valuation.map_sum_lt v hv0 hlt
    rw [eq_neg_of_add_eq_zero_right hsum', Valuation.map_neg] at hlt2
    exact lt_irrefl _ hlt2
  obtain ⟨j, hjS, hji, hvj⟩ := hexists

  have hunit : UnitA A (t j / t i₀) := by
    rw [unitA_iff_valuation_eq_one, map_div₀, hvj, div_self hv0]

  have hcj : (P.coeff j) ≠ 0 := (Finset.mem_filter.mp hjS).2
  have hci : (P.coeff i₀) ≠ 0 := (Finset.mem_filter.mp hi₀S).2
  obtain ⟨n₁, hn₁⟩ := exists_unitA_intCast_mul_zpow red hker hcj
  obtain ⟨n₂, hn₂⟩ := exists_unitA_intCast_mul_zpow red hker hci
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hcj' : ((P.coeff j : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast hcj
  have hci' : ((P.coeff i₀ : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast hci

  have hU : UnitA A (x ^ ((j : ℤ) - (i₀ : ℤ)) * ((q : AlgebraicClosure ℚ)) ^ (-(n₂ - n₁))) := by
    refine UnitA.congr ((hunit.mul hn₁.inv).mul hn₂) ?_
    rw [ht]
    simp only
    rw [zpow_sub₀ hx, zpow_natCast, zpow_natCast]
    field_simp
    rw [zpow_neg, zpow_neg, zpow_neg, zpow_sub₀ hq0]
    field_simp
  refine ⟨(j : ℤ) - (i₀ : ℤ), n₂ - n₁, by omega, hU⟩

theorem exists_unitA_pow_mul_zpow (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {x : AlgebraicClosure ℚ} (hx : x ≠ 0) :
    ∃ (e : ℕ) (n : ℤ), e ≠ 0 ∧ UnitA A (x ^ e * ((q : AlgebraicClosure ℚ)) ^ (-n)) := by
  obtain ⟨e, n, he, hU⟩ := exists_unitA_zpow_mul_zpow red hker hx
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  rcases lt_or_gt_of_ne he with hlt | hgt
  · refine ⟨(-e).toNat, -n, by omega, ?_⟩
    refine UnitA.congr hU.inv ?_
    have h1 : ((-e).toNat : ℤ) = -e := by omega
    rw [← zpow_natCast, h1, mul_inv, ← zpow_neg, ← zpow_neg, neg_neg]
  · refine ⟨e.toNat, n, by omega, ?_⟩
    refine UnitA.congr hU ?_
    have h1 : (e.toNat : ℤ) = e := by omega
    rw [← zpow_natCast, h1]

end Torsion
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end Ws23.Jump
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace Jump

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.CentredSigma"

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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end Ws23.Jump
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace P7b57522e
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized"
theorem modularEval_map_inclusion (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (P : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval N A.toSubring (MvPolynomial.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring)) P)
      = modularEval N (coeffSubring A K) P := by
  rw [modularEval, MvPolynomial.eval₂Hom_map_hom]
  rfl

theorem pointEval_map_inclusion {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (a b : k)
    (P : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    pointEval A.toSubring red a b (MvPolynomial.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring)) P)
      = pointEval (coeffSubring A K) (redRestrict red K) a b P := by
  rw [pointEval, MvPolynomial.eval₂Hom_map_hom]
  rfl

end P7b57522e
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace WParam

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.Jump"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]

theorem frickeInvolutionBar_evalF (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    frickeInvolutionBar (1 * q) (E4b80310.evalF A q P)
      = E4b80310.evalF A q (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P) := by
  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* ↥(modularFunctionFieldBar (1 * q)) :=
    ((frickeInvolutionBar (1 * q) : ↥(modularFunctionFieldBar (1 * q)) ≃ₐ[AlgebraicClosure ℚ] _) : _ →+* _).comp (E4b80310.evalF A q)
  let ψ : MvPolynomial (Fin 2) ↥A.toSubring →+* ↥(modularFunctionFieldBar (1 * q)) :=
    (E4b80310.evalF A q).comp (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) : MvPolynomial (Fin 2) ↥A.toSubring →ₐ[↥A.toSubring] _).toRingHom
  have hφψ : φ = ψ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · show frickeInvolutionBar (1 * q) (E4b80310.evalF A q (MvPolynomial.C c)) = E4b80310.evalF A q (MvPolynomial.rename _ (MvPolynomial.C c))
      rw [MvPolynomial.rename_C, E4b80310.evalF, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, AlgEquiv.commutes]
    · show frickeInvolutionBar (1 * q) (E4b80310.evalF A q (MvPolynomial.X 0)) = E4b80310.evalF A q (MvPolynomial.rename _ (MvPolynomial.X 0))
      rw [MvPolynomial.rename_X, Equiv.swap_apply_left, E4b80310.evalF, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact ModularCurve.NodeLocalized.frickeInvolutionBar_jElt q
    · show frickeInvolutionBar (1 * q) (E4b80310.evalF A q (MvPolynomial.X 1)) = E4b80310.evalF A q (MvPolynomial.rename _ (MvPolynomial.X 1))
      rw [MvPolynomial.rename_X, Equiv.swap_apply_right, E4b80310.evalF, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact ModularCurve.NodeLocalized.frickeInvolutionBar_jqElt q
  exact RingHom.congr_fun hφψ P

theorem pointEval_rename_swap (red : ↥A.toSubring →+* k) (c d : k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    pointEval A.toSubring red c d (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P) = pointEval A.toSubring red d c P := by
  rw [pointEval, pointEval, MvPolynomial.eval₂Hom_rename]
  have : ((![c, d] : Fin 2 → k) ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = ![d, c] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [this]

noncomputable def gr (q : ℕ) (red : ↥A →+* k) (P : MvPolynomial (Fin 2) ↥A.toSubring) : Polynomial k :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P

theorem eval_gr (red : ↥A →+* k) (c : k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    Polynomial.eval c (gr q red P) = pointEval A.toSubring red c (c ^ q) P := by
  rw [gr, eval_graphReduce red c P]; rfl

theorem gr_ne_zero_of_pointEval_ne_zero (red : ↥A →+* k) {c : k} {P : MvPolynomial (Fin 2) ↥A.toSubring}
    (h : pointEval A.toSubring red c (c ^ q) P ≠ 0) : gr q red P ≠ 0 := by
  intro h0; apply h; rw [← eval_gr, h0, Polynomial.eval_zero]

theorem redRes_modularEval_eq_aeval_gr (red : ↥A →+* k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨modularEval (1 * q) A.toSubring P, modularEval_mem_modularRing (1 * q) P⟩
      = Polynomial.aeval (jqModC k) (gr q red P) :=
  redRes_modularEval red P

theorem modularEval_ne_zero_of_gr_ne_zero (red : ↥A →+* k) {P : MvPolynomial (Fin 2) ↥A.toSubring} (h : gr q red P ≠ 0) :
    modularEval (1 * q) A.toSubring P ≠ 0 := by
  intro h0
  apply transcendental_jqModC k
  refine ⟨gr q red P, h, ?_⟩
  rw [← redRes_modularEval_eq_aeval_gr red P]
  have : (⟨modularEval (1 * q) A.toSubring P, modularEval_mem_modularRing (1 * q) P⟩ :
      ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 := Subtype.ext h0
  rw [this, map_zero]

theorem exists_mem_rlHom_mul_eq (red : ↥A →+* k) (g : ↥(modularFunctionFieldBar (1 * q)))
    (r s : MvPolynomial (Fin 2) ↥A.toSubring)
    (hgs : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) A.toSubring s
      = modularEval (1 * q) A.toSubring r)
    (hs : gr q red s ≠ 0) :
    ∃ hg : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      rlHom red ⟨_, hg⟩ * Polynomial.aeval (jC1 k) (gr q red s) = Polynomial.aeval (jC1 k) (gr q red r) := by
  have hsred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
      ⟨modularEval (1 * q) A.toSubring s, modularEval_mem_modularRing (1 * q) s⟩ ≠ 0 := by
    rw [redRes_modularEval_eq_aeval_gr]
    intro h0; exact transcendental_jqModC k ⟨gr q red s, hs, h0⟩
  have hnot := (CharPReduction.notMem_redKer_iff A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)).mpr hsred
  have hg : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
    ⟨⟨_, modularEval_mem_modularRing (1 * q) r⟩, ⟨_, modularEval_mem_modularRing (1 * q) s⟩, hnot, hgs⟩
  refine ⟨hg, ?_⟩
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨_, hg⟩
    (r := ⟨_, modularEval_mem_modularRing (1 * q) r⟩) (s := ⟨_, modularEval_mem_modularRing (1 * q) s⟩) hgs
  apply Subtype.ext
  rw [MulMemClass.coe_mul, coe_rlHom, E4b80310.coe_aeval_jC1, E4b80310.coe_aeval_jC1, ← redRes_modularEval_eq_aeval_gr red s,
    ← redRes_modularEval_eq_aeval_gr red r]
  exact hspec

theorem ord_aeval_gr (red : ↥A →+* k) [DecidableEq k] (c : k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    (charLGeomPlaceOfPoint k c).ord (Polynomial.aeval (jC1 k) (gr q red P)) = ((gr q red P).rootMultiplicity c : ℤ) := by
  rw [Ws23.NodePlaceAPI.ord_charLGeomPlaceOfPoint_aeval]

theorem ord_aeval_gr_eq_zero (red : ↥A →+* k) [DecidableEq k] {c : k} {P : MvPolynomial (Fin 2) ↥A.toSubring}
    (h : pointEval A.toSubring red c (c ^ q) P ≠ 0) :
    (charLGeomPlaceOfPoint k c).ord (Polynomial.aeval (jC1 k) (gr q red P)) = 0 := by
  rw [ord_aeval_gr, Polynomial.rootMultiplicity_eq_zero]
  · rfl
  · intro hroot; exfalso; apply h; rw [← eval_gr]; exact hroot

theorem aeval_gr_ne_zero (red : ↥A →+* k) {P : MvPolynomial (Fin 2) ↥A.toSubring} (h : gr q red P ≠ 0) :
    Polynomial.aeval (jC1 k) (gr q red P) ≠ 0 := by
  intro h0
  apply transcendental_jqModC k
  refine ⟨gr q red P, h, ?_⟩
  have := congrArg (fun t : ↥(modularFunctionFieldC k 1) => (t : LaurentSeries k)) h0
  simp only [E4b80310.coe_aeval_jC1] at this
  exact this

theorem exists_mem_ord_nonneg (red : ↥A →+* k) [DecidableEq k] (c : k) (g : ↥(modularFunctionFieldBar (1 * q)))
    (r s : MvPolynomial (Fin 2) ↥A.toSubring)
    (hgs : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) A.toSubring s
      = modularEval (1 * q) A.toSubring r)
    (hsc : pointEval A.toSubring red c (c ^ q) s ≠ 0) :
    ∃ hg : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      (rlHom red ⟨_, hg⟩ ≠ 0 → 0 ≤ (charLGeomPlaceOfPoint k c).ord (rlHom red ⟨_, hg⟩)) := by
  have hs0 := gr_ne_zero_of_pointEval_ne_zero red hsc
  obtain ⟨hg, hmul⟩ := exists_mem_rlHom_mul_eq red g r s hgs hs0
  refine ⟨hg, fun hne => ?_⟩
  have hsne := aeval_gr_ne_zero red hs0 (k := k)
  have hrne : Polynomial.aeval (jC1 k) (gr q red r) ≠ 0 := by rw [← hmul]; exact mul_ne_zero hne hsne
  have hord := congrArg (charLGeomPlaceOfPoint k c).ord hmul
  rw [Place.ord_mul _ hne hsne, ord_aeval_gr_eq_zero red hsc, add_zero, ord_aeval_gr] at hord
  rw [hord]; exact Int.natCast_nonneg _

end Ws23.WParam
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace WParam

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.Jump"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  [IsAlgClosed k] [DecidableEq k]

theorem exists_rep (red : ↥A →+* k) (a : k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    ∃ (g : ↥(modularFunctionFieldBar (1 * q))) (r s : MvPolynomial (Fin 2) ↥A.toSubring),
      ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) ∧
      ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) A.toSubring s
        = modularEval (1 * q) A.toSubring r ∧
      pointEval A.toSubring red a (a ^ q) s ≠ 0 := by
  obtain ⟨rK, sK, hsK, hx⟩ := x.2
  set r := MvPolynomial.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring)) rK with hr
  set s := MvPolynomial.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring)) sK with hs
  have hsA : pointEval A.toSubring red a (a ^ q) s ≠ 0 := by rw [hs, P7b57522e.pointEval_map_inclusion]; exact hsK
  have hxA : (x : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) A.toSubring s = modularEval (1 * q) A.toSubring r := by
    rw [hr, hs, P7b57522e.modularEval_map_inclusion, P7b57522e.modularEval_map_inclusion]; exact hx
  have hs0 : modularEval (1 * q) A.toSubring s ≠ 0 :=
    modularEval_ne_zero_of_gr_ne_zero red (gr_ne_zero_of_pointEval_ne_zero red hsA)
  refine ⟨E4b80310.evalF A q r * (E4b80310.evalF A q s)⁻¹, r, s, ?_, ?_, hsA⟩
  · rw [MulMemClass.coe_mul, IntermediateField.coe_inv, E4b80310.coe_evalF, E4b80310.coe_evalF, ← hxA, mul_assoc,
      mul_inv_cancel₀ hs0, mul_one]
  · rw [MulMemClass.coe_mul, IntermediateField.coe_inv, E4b80310.coe_evalF, E4b80310.coe_evalF, mul_assoc,
      inv_mul_cancel₀ hs0, mul_one]

theorem presentation_frickeInvolutionBar (red : ↥A →+* k) {a : k} (ha2 : a ^ (q ^ 2) = a)
    (g : ↥(modularFunctionFieldBar (1 * q))) (r s : MvPolynomial (Fin 2) ↥A.toSubring)
    (hgs : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) A.toSubring s
      = modularEval (1 * q) A.toSubring r)
    (hsa : pointEval A.toSubring red a (a ^ q) s ≠ 0) :
    ((frickeInvolutionBar (1 * q) g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        * modularEval (1 * q) A.toSubring (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) s)
      = modularEval (1 * q) A.toSubring (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) r) ∧
    pointEval A.toSubring red (a ^ q) ((a ^ q) ^ q) (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) s) ≠ 0 := by
  constructor
  · have hF : g * E4b80310.evalF A q s = E4b80310.evalF A q r := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, E4b80310.coe_evalF, E4b80310.coe_evalF]; exact hgs
    have h2 := congrArg (frickeInvolutionBar (1 * q)) hF
    rw [map_mul, frickeInvolutionBar_evalF, frickeInvolutionBar_evalF] at h2
    have h3 := congrArg (fun t : ↥(modularFunctionFieldBar (1 * q)) => (t : LaurentSeries (AlgebraicClosure ℚ))) h2
    simp only [MulMemClass.coe_mul, E4b80310.coe_evalF] at h3
    exact h3
  · rw [pointEval_rename_swap, ← pow_mul, ← sq, ha2]; exact hsa

end Ws23.WParam
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace JumpW

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.CentredSigma P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.SlopeLaw0 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.Jump"

section Main

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  [IsAlgClosed k] [DecidableEq k]

theorem jump_core_wide (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (ew : ℕ)
    (ζ u : ↥(modularFunctionFieldBar (1 * q)))
    (hζ : ∃ h : ((ζ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hu : ∃ h : ((u : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hσζ : frickeInvolutionBar (1 * q) ζ = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((q : AlgebraicClosure ℚ) ^ ew) * u⁻¹)
    (hordζ : (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, hζ.1⟩) = 1)
    (hζW : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W →
        ζ ∈ W.toValuationSubring ∧ ζ⁻¹ ∈ W.toValuationSubring)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W → W.ord f = 0)
    (c₁ : AlgebraicClosure ℚ) (hc₁ : c₁ ≠ 0)
    (h₁ : ((c₁ • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (c₂ : AlgebraicClosure ℚ) (hc₂ : c₂ ≠ 0)
    (k₂ : ((c₂ • frickeInvolutionBar (1 * q) f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (k₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, k₂⟩ ≠ 0)
    (e : ℕ) (n : ℤ) (hU : UnitA A ((c₁ / c₂) ^ e * ((q : AlgebraicClosure ℚ)) ^ (-n))) :
    ((ew * e : ℕ) : ℤ) * (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, h₁⟩) = n := by
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  set x : AlgebraicClosure ℚ := c₁ / c₂ with hxdef
  have hx0 : x ≠ 0 := div_ne_zero hc₁ hc₂

  obtain ⟨hz, hz0⟩ := hζ
  have hordz : (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, hz⟩) = 1 := hordζ
  set z : ↥(modularFunctionFieldBar (1 * q)) := ζ with hzdef
  have hzG : ∃ h : ((z : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 :=
    ⟨hz, hz0⟩
  have hσG' : ∃ h : ((u : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 := hu
  have hcf : ∃ h : ((c₁ • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 :=
    ⟨h₁, h₁u⟩
  have hcσf : ∃ h : ((c₂ • frickeInvolutionBar (1 * q) f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 :=
    ⟨k₂, k₂u⟩

  set g : ↥(modularFunctionFieldBar (1 * q)) := (c₁ • f) ^ (ew * e) * z ^ (-n) with hgdef
  have hgcoe : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((c₁ • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ^ (ew * e)
        * ((z : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ^ (-n) := by
    simp only [hgdef, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_zpow']
  have hgL : ∃ h : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 :=
    CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hgcoe.symm
      (CharPReduction.gaussUnit_mul (1 * q) A.toSubring red (CharPReduction.gaussUnit_pow (1 * q) A.toSubring red hcf (ew * e))
        (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hzG (-n)))

  have hUw : UnitA A ((x ^ e * ((q : AlgebraicClosure ℚ)) ^ (-n)) ^ ew) := by
    refine ⟨pow_mem hU.1 ew, ?_⟩
    have : (⟨(x ^ e * ((q : AlgebraicClosure ℚ)) ^ (-n)) ^ ew, pow_mem hU.1 ew⟩ : ↥A) = ⟨_, hU.1⟩ ^ ew := rfl
    rw [this]; exact hU.2.pow ew
  set uA : ↥A := ⟨(x ^ e * ((q : AlgebraicClosure ℚ)) ^ (-n)) ^ ew, hUw.1⟩ with huA
  have huAunit : IsUnit uA := hUw.2
  have hreduA : red uA ≠ 0 := hUw.red_ne_zero red hker
  set g₂ : ↥(modularFunctionFieldBar (1 * q)) := (c₂ • frickeInvolutionBar (1 * q) f) ^ (ew * e) * u ^ n with hg₂def
  have hσg : frickeInvolutionBar (1 * q) g = (uA : AlgebraicClosure ℚ) • g₂ := by
    have hxc : x * c₂ = c₁ := by rw [hxdef, div_mul_cancel₀ _ hc₂]
    have hcu : (((x ^ e * (q : AlgebraicClosure ℚ) ^ (-n)) ^ ew : AlgebraicClosure ℚ))
        = x ^ (ew * e) * (q : AlgebraicClosure ℚ) ^ (-((ew : ℤ) * n)) := by
      rw [mul_pow, ← pow_mul, mul_comm e ew, ← zpow_natCast ((q : AlgebraicClosure ℚ) ^ (-n)) ew, ← zpow_mul]
      congr 2; ring
    have hF1 : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((q : AlgebraicClosure ℚ) ^ ew) * u⁻¹) ^ (-n)
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((q : AlgebraicClosure ℚ) ^ (-((ew : ℤ) * n))) * u ^ n := by
      rw [mul_zpow, inv_zpow', neg_neg, ← map_zpow₀, ← zpow_natCast (q : AlgebraicClosure ℚ) ew, ← zpow_mul]
      congr 3; ring
    have hF2 : ((x • (c₂ • frickeInvolutionBar (1 * q) f) : ↥(modularFunctionFieldBar (1 * q)))) ^ (ew * e)
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x ^ (ew * e)) * (c₂ • frickeInvolutionBar (1 * q) f) ^ (ew * e) := by
      rw [smul_pow, Algebra.smul_def, map_pow]
    rw [hgdef, hg₂def, map_mul, map_pow, map_zpow₀, hzdef, hσζ, Ws23.CentredSigma.frickeInvolutionBar_smul', ← hxc, ← smul_smul,
      hF2, hF1, huA]
    show _ = (((x ^ e * (q : AlgebraicClosure ℚ) ^ (-n)) ^ ew : AlgebraicClosure ℚ)) • _
    rw [hcu]
    simp only [Algebra.smul_def, map_mul]
    ring
  have hg₂L : ∃ h : ((g₂ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 := by
    have hg₂coe : ((g₂ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = ((c₂ • frickeInvolutionBar (1 * q) f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ^ (ew * e)
          * ((u : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ^ n := by
      simp only [hg₂def, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_zpow']
    exact CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hg₂coe.symm
      (CharPReduction.gaussUnit_mul (1 * q) A.toSubring red (CharPReduction.gaussUnit_pow (1 * q) A.toSubring red hcσf (ew * e))
        (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hσG' n))
  have hσgmem : ((frickeInvolutionBar (1 * q) g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [hσg]; exact Ws23.SlopeLaw0.smul_mem_modularLocalized red uA hg₂L.1
  have hσgL : ∃ h : ((frickeInvolutionBar (1 * q) g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 := by
    refine ⟨hσgmem, ?_⟩
    have hmem2 := Ws23.SlopeLaw0.smul_mem_modularLocalized red uA hg₂L.1
    have heq : (⟨_, hσgmem⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hmem2⟩ :=
      Subtype.ext (congrArg (fun t : ↥(modularFunctionFieldBar (1 * q)) => (t : LaurentSeries (AlgebraicClosure ℚ))) hσg)
    rw [heq, Ws23.SlopeLaw0.modularRedLocHom_smul red uA hg₂L.1 hmem2]
    exact mul_ne_zero ((map_ne_zero _).mpr hreduA) hg₂L.2

  have htube : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W →
      g ∈ W.toValuationSubring ∧ g⁻¹ ∈ W.toValuationSubring := by
    intro W hW
    have hWrat : W.IsRational := isRational_W W
    have hfmem : f ∈ W.toValuationSubring := W.mem_toValuationSubring_of_ord_nonneg_alt hf (hford W hW).ge
    have hfinv : f⁻¹ ∈ W.toValuationSubring :=
      W.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hf) (by rw [ord_inv' W hf, hford W hW, neg_zero])
    obtain ⟨hzmem, hzinv⟩ := hζW W hW
    have hcfmem : (c₁ • f : ↥(modularFunctionFieldBar (1 * q))) ∈ W.toValuationSubring := by
      rw [Algebra.smul_def]; exact mul_mem (W.algebraMap_mem' _) hfmem
    have hcfinv : (c₁ • f : ↥(modularFunctionFieldBar (1 * q)))⁻¹ ∈ W.toValuationSubring := by
      rw [Algebra.smul_def, mul_inv, ← map_inv₀]; exact mul_mem (W.algebraMap_mem' _) hfinv
    refine ⟨mul_mem (pow_mem hcfmem (ew * e)) (zpow_mem_of_mem_of_inv_mem W hzmem hzinv (-n)), ?_⟩
    rw [hgdef, mul_inv, ← inv_pow, ← zpow_neg, neg_neg]
    exact mul_mem (pow_mem hcfinv (ew * e)) (zpow_mem_of_mem_of_inv_mem W hzmem hzinv n)

  have h₁gF := Ws23.SlopeLaw0.modularRedLocHom_mem_one red ⟨_, hgL.1⟩
  have h₂gF := Ws23.SlopeLaw0.modularRedLocHom_mem_one red ⟨_, hσgL.1⟩
  obtain ⟨cg, hVg, -⟩ := ModularCurve.exists_hasValue_frobNodePair_of_forall_pole_not_centred red a ha ha2 g hgL.1 h₁gF hσgL.1 h₂gF
    (fun W hlt hW => absurd (ord_nonneg_of_mem' W (htube W hW).1) (not_le.mpr hlt))

  obtain ⟨hginvL, hginvL0⟩ := CharPReduction.gaussUnit_inv (1 * q) A.toSubring red hgL
  obtain ⟨hσginvL, hσginvL0⟩ := CharPReduction.gaussUnit_inv (1 * q) A.toSubring red hσgL
  have hginvmem : ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by rw [IntermediateField.coe_inv]; exact hginvL
  have hσginvmem : ((frickeInvolutionBar (1 * q) g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by rw [map_inv₀, IntermediateField.coe_inv]; exact hσginvL
  have h₁giF := Ws23.SlopeLaw0.modularRedLocHom_mem_one red ⟨_, hginvmem⟩
  have h₂giF := Ws23.SlopeLaw0.modularRedLocHom_mem_one red ⟨_, hσginvmem⟩
  obtain ⟨cg', hVg', -⟩ := ModularCurve.exists_hasValue_frobNodePair_of_forall_pole_not_centred red a ha ha2 g⁻¹ hginvmem h₁giF hσginvmem h₂giF
    (fun W hlt hW => absurd (ord_nonneg_of_mem' W (htube W hW).2) (not_le.mpr hlt))

  set y : ↥(modularFunctionFieldC k 1) := rlHom red ⟨_, hgL.1⟩ with hydef
  have hy0 : y ≠ 0 := (rlHom_ne_zero_iff red _).mpr hgL.2
  have hVg1 : (charLGeomPlaceOfPoint k a).HasValue y cg := by
    have := hVg; rwa [rlHom_eq red] at this
  have hVg2 : (charLGeomPlaceOfPoint k a).HasValue y⁻¹ cg' := by
    have h2 := hVg'
    rw [rlHom_eq red] at h2
    have heq : rlHom red ⟨_, hginvmem⟩ = y⁻¹ := by
      rw [hydef, ← rlHom_inv red hgL hginvL]
      congr 1
    rwa [heq] at h2
  have hcg0 : cg ≠ 0 := hasValue_ne_zero_of_inv _ hy0 hVg1 hVg2
  have hordy : (charLGeomPlaceOfPoint k a).ord y = 0 := hVg1.ord_eq_zero hcg0

  have hzn := (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hzG (-n)).1
  have hsplit : (⟨_, hgL.1⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, h₁⟩ ^ (ew * e) * ⟨_, hzn⟩ := by
    apply Subtype.ext
    show ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [hgcoe]
    rfl
  have hy : y = rlHom red ⟨_, h₁⟩ ^ (ew * e) * rlHom red ⟨_, hz⟩ ^ (-n) := by
    rw [hydef, hsplit, map_mul, map_pow, rlHom_zpow red hzG (-n)]
  have hn10 : rlHom red ⟨_, h₁⟩ ≠ 0 := (rlHom_ne_zero_iff red _).mpr h₁u
  have hz10 : rlHom red ⟨_, hz⟩ ≠ 0 := (rlHom_ne_zero_iff red _).mpr hz0
  rw [hy, Place.ord_mul _ (pow_ne_zero _ hn10) (zpow_ne_zero _ hz10), ord_pow' _ hn10, ord_zpow' _ hz10, hordz] at hordy
  push_cast at hordy ⊢
  linarith

theorem jump_wide (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (ew : ℕ)
    (ζ u : ↥(modularFunctionFieldBar (1 * q)))
    (hζ : ∃ h : ((ζ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hu : ∃ h : ((u : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hσζ : frickeInvolutionBar (1 * q) ζ = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((q : AlgebraicClosure ℚ) ^ ew) * u⁻¹)
    (hordζ : (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, hζ.1⟩) = 1)
    (hζW : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W →
        ζ ∈ W.toValuationSubring ∧ ζ⁻¹ ∈ W.toValuationSubring)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W → W.ord f = 0)
    (c₁ : AlgebraicClosure ℚ) (hc₁ : c₁ ≠ 0)
    (h₁ : ((c₁ • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (c₂ : AlgebraicClosure ℚ) (hc₂ : c₂ ≠ 0)
    (k₂ : ((c₂ • frickeInvolutionBar (1 * q) f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (k₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, k₂⟩ ≠ 0) :
    UnitA A (c₁ / c₂ * ((q : AlgebraicClosure ℚ)) ^ (-((ew : ℤ) * (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, h₁⟩)))) := by
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  obtain ⟨e, n, he, hU⟩ := exists_unitA_pow_mul_zpow red hker (div_ne_zero hc₁ hc₂ : c₁ / c₂ ≠ 0)
  have hcore := jump_core_wide red hker a ha ha2 ew ζ u hζ hu hσζ hordζ hζW f hf hford c₁ hc₁ h₁ h₁u c₂ hc₂ k₂ k₂u e n hU
  refine UnitA.of_pow he (UnitA.congr hU ?_)
  rw [← hcore, mul_pow]
  congr 1
  rw [← zpow_natCast (((q : AlgebraicClosure ℚ)) ^ (-((ew : ℤ) * (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, h₁⟩)))) e, ← zpow_mul]
  congr 1
  push_cast
  ring

end Main
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end Ws23.JumpW
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace WNodeOrd
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized"
open Polynomial in

private scoped instance instIsAlgClosedResidueField_reMint {L : Type*} [Field L] [IsAlgClosed L]
    (A : ValuationSubring L) : IsAlgClosed (IsLocalRing.ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ (fun f hf_monic hf_irr => ?_)
  have hf_lifts : f ∈ lifts (IsLocalRing.residue A) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => IsLocalRing.residue_surjective (f.coeff n)
  obtain ⟨g, hg_map, -, hg_monic⟩ := lifts_and_degree_eq_and_monic hf_lifts hf_monic
  have hgL_deg : (g.map (algebraMap A L)).degree ≠ 0 := by
    rw [hg_monic.degree_map]
    intro h0
    have hg_nat : g.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)
    have hf_deg : f.natDegree = 0 := by
      rw [← hg_map, hg_monic.natDegree_map]; exact hg_nat
    exact hf_irr.not_isUnit (by rw [(hf_monic.natDegree_eq_zero).mp hf_deg]; exact isUnit_one)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hgL_deg
  have hα_int : IsIntegral A α := ⟨g, hg_monic, by rwa [IsRoot.def, eval_map] at hα⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hα_int
  refine ⟨IsLocalRing.residue A a, ?_⟩
  have hga : g.eval a = 0 := by
    have : algebraMap A L (g.eval a) = 0 := by
      rw [show algebraMap A L (g.eval a) = (g.map (algebraMap A L)).eval α from by
        rw [← ha, eval_map, eval₂_hom]]
      exact hα
    exact (map_eq_zero_iff _ Subtype.coe_injective).mp this
  rw [show f.eval (IsLocalRing.residue A a) = IsLocalRing.residue A (g.eval a) from by
    rw [← hg_map, eval_map, eval₂_hom], hga, map_zero]

theorem mem_range_red_of_pow_q_sq_eq_self {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q] [IsAlgClosed k]
    (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha2 : a ^ (q ^ 2) = a) : a ∈ Set.range red := by
  classical
  have hH : ∀ c ∈ IsLocalRing.maximalIdeal (↥A), red c = 0 := fun c hc => (hker c).mpr hc
  haveI h2s : (IsLocalRing.maximalIdeal (↥A)).IsTwoSided := inferInstance
  let φ : IsLocalRing.ResidueField ↥A →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥A) red hH
  have hred : ∀ c : ↥A, red c = φ (IsLocalRing.residue A c) := fun c =>
    (Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal ↥A) red hH).symm
  letI : Algebra (IsLocalRing.ResidueField ↥A) k := φ.toAlgebra
  haveI hRFac : IsAlgClosed (IsLocalRing.ResidueField ↥A) := instIsAlgClosedResidueField_reMint A
  have halg : IsIntegral (IsLocalRing.ResidueField ↥A) a := by
    refine ⟨Polynomial.X ^ (q^2) - Polynomial.X, ?_, ?_⟩
    · refine (Polynomial.monic_X_pow (q^2)).sub_of_left ?_
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).two_le
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
      exact sub_eq_zero_of_eq ha2
  have hdeg : (minpoly (IsLocalRing.ResidueField ↥A) a).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible halg)
  obtain ⟨b, hb⟩ := minpoly.mem_range_of_degree_eq_one (IsLocalRing.ResidueField ↥A) a hdeg
  obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective (R := ↥A) b
  exact ⟨c, by rw [hred c, hc]; exact hb⟩

theorem exists_mul_eq_one_of_redRestrict_ne_zero
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(coeffSubring A K)) (hc : redRestrict red K c ≠ 0) :
    ∃ d : ↥(coeffSubring A K), c * d = 1 := by
  let cA : A := Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring) c
  have hcA : cA ∉ IsLocalRing.maximalIdeal A := fun h => hc ((hker cA).mpr h)
  obtain ⟨b, hb⟩ := (IsLocalRing.notMem_maximalIdeal.mp hcA).exists_right_inv
  have hb' : (c : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 := congrArg Subtype.val hb
  have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := fun h => by rw [h, zero_mul] at hb'; exact zero_ne_one hb'
  have hbinv : (b : AlgebraicClosure ℚ) = (c : AlgebraicClosure ℚ)⁻¹ := eq_inv_of_mul_eq_one_right hb'
  have hbK : (b : AlgebraicClosure ℚ) ∈ K.toSubalgebra.toSubring := by
    rw [hbinv]
    exact K.inv_mem (Subring.mem_inf.mp c.2).2
  refine ⟨⟨(b : AlgebraicClosure ℚ), Subring.mem_inf.mpr ⟨b.2, hbK⟩⟩, Subtype.ext ?_⟩
  exact hb'

theorem exists_uniformizer_coeffSubring
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    ∃ ϖ : ↥(coeffSubring A K), ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with hEq | hDVR
  · exfalso
    have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    have hinv : (q : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
      rw [hEq]
      show (q : AlgebraicClosure ℚ)⁻¹ ∈ K
      exact inv_mem (natCast_mem K q)
    have hcoe : (((q : ℕ) : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) :=
      map_natCast (coeffSubring A K).subtype q
    have hone : ((q : ℕ) : ↥(coeffSubring A K)) * ⟨_, hinv⟩ = 1 := by
      apply Subtype.ext
      show (((q : ℕ) : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) * (q : AlgebraicClosure ℚ)⁻¹ = 1
      rw [hcoe, mul_inv_cancel₀ hq0]
    have h := congrArg (redRestrict red K) hone
    rw [map_mul, map_natCast, CharP.cast_eq_zero k q, zero_mul, map_one] at h
    exact zero_ne_one h
  · haveI := hDVR
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
    have hmax : IsLocalRing.maximalIdeal ↥(coeffSubring A K) = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    refine ⟨ϖ, fun c => ⟨fun hc0 => ?_, ?_⟩⟩
    · have hcm : c ∈ IsLocalRing.maximalIdeal ↥(coeffSubring A K) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        obtain ⟨d, hd⟩ := hu.exists_right_inv
        have h := congrArg (redRestrict red K) hd
        rw [map_mul, hc0, zero_mul, map_one] at h
        exact zero_ne_one h
      rw [hmax, Ideal.mem_span_singleton'] at hcm
      obtain ⟨d, hd⟩ := hcm
      exact ⟨d, by rw [← hd, mul_comm]⟩
    · rintro ⟨d, rfl⟩
      rw [map_mul]
      suffices hϖ0 : redRestrict red K ϖ = 0 by rw [hϖ0, zero_mul]
      by_contra hne
      obtain ⟨e, he⟩ := exists_mul_eq_one_of_redRestrict_ne_zero red hker K ϖ hne
      exact hϖ.not_isUnit (IsUnit.of_mul_eq_one e he)

end Ws23.WNodeOrd
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.WNodeOrd"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace WNodeOrd
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.Jump P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.WParam"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem mem_toValuationSubring_of_presentation {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (g : ↥(modularFunctionFieldBar (1 * q))) (r s : MvPolynomial (Fin 2) ↥A.toSubring)
    (hgs : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) A.toSubring s
      = modularEval (1 * q) A.toSubring r)
    (hs : pointEval A.toSubring red a (a ^ q) s ≠ 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : Ws23.CentredSigma.Centred red a W) :
    g ∈ W.toValuationSubring := by
  obtain ⟨⟨x, hxa, hxord⟩, ⟨y, hya, hyord⟩⟩ := hW
  have hjx : W.HasValue (E4b80310.jE q) ((⟨x, x.2⟩ : ↥A.toSubring) : AlgebraicClosure ℚ) := hasValue_of_ord_sub_pos hxord
  have hjy : W.HasValue (E4b80310.jqE q) ((⟨y, y.2⟩ : ↥A.toSubring) : AlgebraicClosure ℚ) := hasValue_of_ord_sub_pos hyord
  have hVs := E4b80310.hasValue_evalF W hjx hjy s
  have hVr := E4b80310.hasValue_evalF W hjx hjy r
  have hσ0 : ((MvPolynomial.eval ![(⟨x, x.2⟩ : ↥A.toSubring), ⟨y, y.2⟩] s : ↥A.toSubring) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply hs
    have hred := E4b80310.red_eval red ⟨x, x.2⟩ ⟨y, y.2⟩ s
    have hx' : red ⟨x, x.2⟩ = a := hxa
    have hy' : red ⟨y, y.2⟩ = a ^ q := hya
    rw [hx', hy'] at hred
    rw [← hred]
    have : (MvPolynomial.eval ![(⟨x, x.2⟩ : ↥A.toSubring), ⟨y, y.2⟩] s : ↥A.toSubring) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hF : g * E4b80310.evalF A q s = E4b80310.evalF A q r := by
    apply Subtype.ext; rw [MulMemClass.coe_mul, E4b80310.coe_evalF, E4b80310.coe_evalF]; exact hgs
  have hs0 : E4b80310.evalF A q s ≠ 0 := hVs.ne_zero hσ0
  have hg : g = E4b80310.evalF A q r * (E4b80310.evalF A q s)⁻¹ := by rw [← hF, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hg]
  exact (hVr.mul (hVs.inv hσ0)).mem

end Ws23.WNodeOrd
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.WNodeOrd"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.Ws23.WNodeOrd"

p2m_open "ModularCurve~coeffEmb_jq" in open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing _root_.P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve _root_.ModularCurve.NodeLocalized _root_.P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized Ws23.NodePlaceAPI Ws23.Jump Ws23.WParam Ws23.WNodeOrd in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hw : a = 0 ∨ a = 1728)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0) (m : ℤ) (_ : ((jWidth a : ℕ) : ℤ) ∣ m)
      (h₁ : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (h₂ : ((frickeInvolutionBar (1 * q) (((c * (q : AlgebraicClosure ℚ) ^ m) • f : modularFunctionFieldBar (1 * q))) : modularFunctionFieldBar (1 * q)) :
          LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 ∧
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0 ∧
        ((jWidth a : ℕ) : ℤ) * (frobNodePair q a).1.ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) = -m := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hford' : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Ws23.CentredSigma.Centred red a W → W.ord f = 0 :=
    fun W h => hford W h

  obtain ⟨c₁, hc₁, h₁, h₁u⟩ := ModularCurve.NodeLocalized.exists_smul_gaussUnit red hker f hf
  have hσf0 : frickeInvolutionBar (1 * q) f ≠ 0 := (map_ne_zero_iff _ (frickeInvolutionBar (1 * q)).injective).mpr hf
  obtain ⟨c₂, hc₂, k₂, k₂u⟩ := ModularCurve.NodeLocalized.exists_smul_gaussUnit red hker (frickeInvolutionBar (1 * q) f) hσf0

  obtain ⟨K, hKfd, -, ⟨x, hx⟩⟩ := ModularCurve.exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq A red a
    (mem_range_red_of_pow_q_sq_eq_self red hker a ha2) f
  haveI := hKfd
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer_coeffSubring (q := q) red hker K

  obtain ⟨eK, ε, heK1, hε, hqϖ, G', H', w, hw', hGH, hmax, hpr1, hpr2, hnm1, hnm2, hsp1, hsp2⟩ :=
    ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728 red a ha ha2 hq hw K x hx ϖ hϖ
  obtain ⟨hPG1, hPG2⟩ :=
    ModularCurve.gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728
      red hker hq a ha ha2 hw K ϖ hϖ eK ε hε hqϖ G' H' w hw' hGH hmax heK1 hpr1 hpr2 hnm1 hnm2 hsp1 hsp2

  obtain ⟨g₀, r₀, s₀, hg₀, hp₀, hs₀⟩ := Ws23.WParam.exists_rep red a K G'
  obtain ⟨hσm, -, hσne, -⟩ := hPG1 g₀ hg₀
  have hg₀0 : g₀ ≠ 0 := by
    intro h0; apply hσne
    have : (⟨_, hσm⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 0 :=
      Subtype.ext (by show ((frickeInvolutionBar (1 * q) g₀ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _; rw [h0, map_zero]; rfl)
    rw [this, map_zero]
  set ζ : ↥(modularFunctionFieldBar (1 * q)) :=
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) * g₀⁻¹ with hζdef
  have hζg : ζ * g₀ = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) := by
    rw [hζdef, mul_assoc, inv_mul_cancel₀ hg₀0, mul_one]
  obtain ⟨hζm, hζF, hζne, hζord⟩ := hPG2 g₀ ζ hg₀ hζg
  have hσζ : frickeInvolutionBar (1 * q) ζ = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((q : AlgebraicClosure ℚ) ^ jWidth a)
      * (frickeInvolutionBar (1 * q) g₀)⁻¹ := by
    rw [hζdef, map_mul, map_inv₀, AlgEquiv.commutes]
  have hordζ : (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, hζm⟩) = 1 := by rw [← rlHom_eq red]; exact hζord

  obtain ⟨gH, rH, sH, hgH, hpH, hsH⟩ := Ws23.WParam.exists_rep red a K H'
  obtain ⟨gw, rw_, sw, hgw, hpw, hsw⟩ := Ws23.WParam.exists_rep red a K w
  obtain ⟨gwi, rwi, swi, hgwi, hpwi, hswi⟩ := Ws23.WParam.exists_rep red a K (↑(hw'.unit⁻¹) : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
  have hϖmemA : ((ϖ : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) ∈ A := (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring) ϖ).2
  have hϖser : ((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((ϖ : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [Ws23.SlopeLaw0.coe_algebraMap_eq_constSeries ⟨_, hϖmemA⟩]
    show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ) = _
    rw [modularEval, MvPolynomial.eval₂Hom_C]
    rfl
  have eqFw : gw * gwi = 1 := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, OneMemClass.coe_one, hgw, hgwi, ← Subring.coe_mul, hw'.mul_val_inv]; rfl
  have eqFGH : g₀ * gH = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((ϖ : ↥(coeffSubring A K)) : AlgebraicClosure ℚ)) ^ (jWidth a * eK) * gw := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, SubmonoidClass.coe_pow, hg₀, hgH, hgw, ← hϖser]
    have := congrArg Subtype.val hGH; push_cast at this; exact this
  have hϖ0 : ((ϖ : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0; apply hq0
    have := congrArg (fun t : ↥(coeffSubring A K) => (t : AlgebraicClosure ℚ)) hqϖ
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast] at this
    rw [this, h0, zero_pow (by omega : eK ≠ 0), zero_mul]
  have hζW : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Ws23.CentredSigma.Centred red a W →
      ζ ∈ W.toValuationSubring ∧ ζ⁻¹ ∈ W.toValuationSubring := by
    intro W hW
    have m₀ := mem_toValuationSubring_of_presentation red hker a g₀ r₀ s₀ hp₀ hs₀ W hW
    have mH := mem_toValuationSubring_of_presentation red hker a gH rH sH hpH hsH W hW
    have mw := mem_toValuationSubring_of_presentation red hker a gw rw_ sw hpw hsw W hW
    have mwi := mem_toValuationSubring_of_presentation red hker a gwi rwi swi hpwi hswi W hW
    have hgw0 : gw ≠ 0 := left_ne_zero_of_mul_eq_one eqFw
    have hgwi0 : gwi ≠ 0 := right_ne_zero_of_mul_eq_one eqFw
    have hordw : W.ord gw = 0 := by
      have h := congrArg W.ord eqFw
      rw [W.ord_mul hgw0 hgwi0, ord_one'] at h
      have := ord_nonneg_of_mem' W mw; have := ord_nonneg_of_mem' W mwi
      omega
    have hgH0 : gH ≠ 0 := by
      intro h0; rw [h0, mul_zero] at eqFGH
      exact (mul_ne_zero (pow_ne_zero _ ((map_ne_zero _).mpr hϖ0)) hgw0) eqFGH.symm
    have hord₀ : W.ord g₀ = 0 := by
      have h := congrArg W.ord eqFGH
      rw [W.ord_mul hg₀0 hgH0, W.ord_mul (pow_ne_zero _ ((map_ne_zero _).mpr hϖ0)) hgw0, hordw,
        ord_pow' _ ((map_ne_zero _).mpr hϖ0), show W.ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
          ((ϖ : ↥(coeffSubring A K)) : AlgebraicClosure ℚ)) = 0 from (W.hasValue_algebraMap _).ord_eq_zero hϖ0] at h
      have := ord_nonneg_of_mem' W m₀; have := ord_nonneg_of_mem' W mH
      push_cast at h
      omega
    have m₀inv : g₀⁻¹ ∈ W.toValuationSubring :=
      W.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hg₀0) (by rw [ord_inv' W hg₀0, hord₀, neg_zero])
    refine ⟨mul_mem (W.algebraMap_mem' _) m₀inv, ?_⟩
    rw [hζdef, mul_inv, inv_inv, ← map_inv₀]
    exact mul_mem (W.algebraMap_mem' _) m₀

  have hζpack : ∃ h : ((ζ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 := ⟨hζm, hζne⟩
  have hU := Ws23.JumpW.jump_wide red hker a ha ha2 (jWidth a) ζ (frickeInvolutionBar (1 * q) g₀) hζpack ⟨hσm, hσne⟩ hσζ hordζ
    hζW f hf hford' c₁ hc₁ h₁ h₁u c₂ hc₂ k₂ k₂u

  set n₁ : ℤ := (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, h₁⟩) with hn₁
  set uA : ↥A := ⟨c₁ / c₂ * ((q : AlgebraicClosure ℚ)) ^ (-((jWidth a : ℤ) * n₁)), hU.1⟩ with huA
  have hreduA : red uA ≠ 0 := hU.red_ne_zero red hker
  have key : frickeInvolutionBar (1 * q) (((c₁ * (q : AlgebraicClosure ℚ) ^ (-((jWidth a : ℤ) * n₁))) • f : modularFunctionFieldBar (1 * q)))
      = (uA : AlgebraicClosure ℚ) • (c₂ • frickeInvolutionBar (1 * q) f) := by
    rw [Ws23.CentredSigma.frickeInvolutionBar_smul', smul_smul]
    congr 1
    show c₁ * (q : AlgebraicClosure ℚ) ^ (-((jWidth a : ℤ) * n₁)) = c₁ / c₂ * (q : AlgebraicClosure ℚ) ^ (-((jWidth a : ℤ) * n₁)) * c₂
    field_simp
  have hmem2 := Ws23.SlopeLaw0.smul_mem_modularLocalized red uA k₂
  have h₂ : ((frickeInvolutionBar (1 * q) (((c₁ * (q : AlgebraicClosure ℚ) ^ (-((jWidth a : ℤ) * n₁))) • f : modularFunctionFieldBar (1 * q))) :
      modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [key]; exact hmem2
  have h₁F := Ws23.SlopeLaw0.modularRedLocHom_mem_one red ⟨_, h₁⟩
  refine ⟨c₁, hc₁, -((jWidth a : ℤ) * n₁), ⟨-n₁, by ring⟩, h₁, h₂, h₁F, h₁u, ?_, ?_⟩
  · have heq : (⟨_, h₂⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hmem2⟩ :=
      Subtype.ext (congrArg (fun t : ↥(modularFunctionFieldBar (1 * q)) => (t : LaurentSeries (AlgebraicClosure ℚ))) key)
    rw [heq, Ws23.SlopeLaw0.modularRedLocHom_smul red uA k₂ hmem2]
    exact mul_ne_zero ((map_ne_zero _).mpr hreduA) k₂u
  · rw [frobNodePair_fst, rlHom_eq red, neg_neg]

end
end S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_width_dvd_and_mul_ord_charLGeomPlaceOfPoint_eq_neg_of_eq_zero_or_eq_ofNat1728 (solution)
