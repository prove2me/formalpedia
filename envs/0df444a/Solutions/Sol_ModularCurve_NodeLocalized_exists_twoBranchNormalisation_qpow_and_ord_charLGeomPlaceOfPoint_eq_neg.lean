-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/da9e7a88-4f33-5cac-acf2-05e73f4cae04

import Mathlib
import Theorems.Thm_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_of_forall_centred_ord_eq_zero
import Theorems.Thm_ModularCurve_NodeLocalized_ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero
import Theorems.Thm_ModularCurve_exists_hasValue_frobNodePair_of_forall_pole_not_centred
import Theorems.Thm_ModularCurve_NodeLocalized_gaussData_nodeCoord
import Theorems.Thm_ModularCurve_NodeLocalized_exists_hasValue_nodeCoord_of_centred
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ModularCurve_modularFunctionFieldC_self_collapse_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_modularEval_kroneckerRemainder
import Theorems.Thm_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_kroneckerCongruence
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst"
p2m_attr_erase "instance" "instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet frobNodePair frobNodePair_fst ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC exists_hasValue_frobNodePair_of_forall_pole_not_centred CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData"
p2m_open "ModularCurve~coeffEmb_jq"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.AlgebraicCurve IsLocalRing"

private theorem _root_.AlgebraicCurve.Place.isRational_of_deg_eq_one {L F : Type*} [Field L] [Field F]
    [Algebra L F] (v : Place L F) (h : v.deg = 1) : v.IsRational := by
  intro z
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra L v.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra L v.ResidueField) := by
    rw [hbt]
    exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

p2m_alias "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.AlgebraicCurve.Place.isRational_of_deg_eq_one" "AlgebraicCurve.Place.isRational_of_deg_eq_one"

theorem isRational_place_modularFunctionFieldBar (M : ℕ) [NeZero M]
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) : w.IsRational :=
  w.isRational_of_deg_eq_one (deg_eq_one_modularFunctionFieldBar M w)

end ModularCurve

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet frobNodePair frobNodePair_fst ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC exists_hasValue_frobNodePair_of_forall_pole_not_centred CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData"
namespace CharPReduction
p2m_export "ModularCurve.CharPReduction" "coeffRed_coeff redRes redRes_apply redKer notMem_redKer_iff mem_localizedAtKer subring_le_localizedAtKer redLoc redRes_ne_zero_of_notMem redLoc_spec redLoc_coe constSeries modularRing jqModC_mem_modularRing jqNModC_mem_modularRing constSeries_mem_modularRing jqModC_mem_integralCoeffs modularRing_le_integralCoeffs modularLocalized modularRedLocHom modularRedLocHom_mem"
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

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap Place.deg Place.ord_zero Place.ord_mul Place.ord_inv Place.ord_zpow Place.residue_algebraMap Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.heightOneSpectrumOfIrreducible RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum RationalFunctionField.residueOfHeightOneSpectrum RationalFunctionField.residueOfHeightOneSpectrum_apply RationalFunctionField.ker_residueOfHeightOneSpectrum RationalFunctionField.placeOfPoint Place.comapSymmRingEquiv Place.coe_comapSymmRingEquiv_apply Place.congrRingEquiv Place.ord_congrRingEquiv StandardAnnulus.ord_placeOfPoint_X_sub_C_self Place.isRational_of_deg_eq_one"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg ord ord_zero ord_mul ord_inv ord_coe_unit ord_zpow toValuationSubring residue_algebraMap HasValue hasValue_one hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective ord_ofHeightOneSpectrum_ne_zero_iff comapSymmRingEquiv coe_comapSymmRingEquiv_apply congrRingEquiv ord_congrRingEquiv mem_toValuationSubring_of_ord_nonneg_alt IsRational residueInv_algebraMap evalAt evalAt_of_mem isRational_of_deg_eq_one"
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

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet frobNodePair frobNodePair_fst ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC exists_hasValue_frobNodePair_of_forall_pole_not_centred CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "exists_twoBranchNormalisation_qpow_of_forall_centred_ord_eq_zero modularEval ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero gaussData_nodeCoord exists_hasValue_nodeCoord_of_centred"
p2m_open "ModularCurve.NodeLocalized ModularCurve~coeffEmb_jq"

theorem isRational_of_level {q : ℕ} [Fact q.Prime] (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : V.IsRational :=
  isRational_place_modularFunctionFieldBar (1 * q) V

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

theorem gaussUnit_corrected {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (c : AlgebraicClosure ℚ) (m : ℤ) (f G : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : ∃ h : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (h₂ : ∃ h : ((frickeInvolutionBar (1 * q)
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c * (q : AlgebraicClosure ℚ) ^ m) * f) : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hG₁ : ∃ h : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹ : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hG₂ : ∃ h : ((frickeInvolutionBar (1 * q) G : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0) :
    (∃ h : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f
          * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹) ^ m : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0) ∧
    (∃ h : ((frickeInvolutionBar (1 * q) (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f
          * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹) ^ m) : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0) := by
  have coe_zpow : ∀ (x : ↥(modularFunctionFieldBar (1 * q))) (n : ℤ), ((x ^ n : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) ^ n := by
    intro x n
    cases n with
    | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, IntermediateField.coe_pow]
    | negSucc n => rw [zpow_negSucc, zpow_negSucc, IntermediateField.coe_inv, IntermediateField.coe_pow]
  constructor
  · rw [MulMemClass.coe_mul, coe_zpow]
    exact CharPReduction.gaussUnit_mul (1 * q) A.toSubring red h₁
      (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hG₁ m)
  · have hσ : frickeInvolutionBar (1 * q) (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f
          * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹) ^ m)
        = frickeInvolutionBar (1 * q)
            (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c * (q : AlgebraicClosure ℚ) ^ m) * f)
          * (frickeInvolutionBar (1 * q) G) ^ (-m) := by
      simp only [map_mul, map_zpow₀, AlgEquiv.commutes, mul_zpow, inv_zpow']
      ring
    rw [hσ, MulMemClass.coe_mul, coe_zpow]
    exact CharPReduction.gaussUnit_mul (1 * q) A.toSubring red h₂
      (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hG₂ (-m))

theorem hasValue_corrected {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) {qK : K}
    (hqK : qK ≠ 0) (m : ℤ) {f G : F} {aV cV : K} (hf : v.HasValue f aV) (hG : v.HasValue G cV) (hcV : cV ≠ 0) :
    v.HasValue (algebraMap K F c * f * (algebraMap K F qK * G⁻¹) ^ m) (c * aV * (qK * cV⁻¹) ^ m) :=
  ((v.hasValue_algebraMap c).mul hf).mul
    (Place.hasValue_zpow_of_hasValue ((v.hasValue_algebraMap qK).mul (hG.inv hcV))
      (mul_ne_zero hqK (inv_ne_zero hcV)) m)

theorem exists_hasValue_ne_zero_of_ord_eq_zero {q : ℕ} [Fact q.Prime] (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) {f : ↥(modularFunctionFieldBar (1 * q))} (hf : f ≠ 0)
    (hord : V.ord f = 0) : ∃ aV : AlgebraicClosure ℚ, aV ≠ 0 ∧ V.HasValue f aV := by
  have hfU := V.exists_isUnit_of_ord_eq_zero hf hord
  obtain ⟨hfmem, hfunit⟩ := hfU
  have hfV := V.exists_hasValue_of_surjective (isRational_of_level V) hfmem
  obtain ⟨aV, haV, haV0⟩ := hfV
  exact ⟨aV, haV0 hfunit, haV⟩

theorem exists_hasValue_nodeCoord_ne_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hV : ((∃ x : A, red x = a ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ cV : AlgebraicClosure ℚ, cV ≠ 0 ∧ V.HasValue ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) cV := by
  have htrio := exists_hasValue_nodeCoord_of_centred red hker hq a ha ha2 h0 h1728 V hV
  obtain ⟨cV, -, ⟨d, -, hcd⟩, hGV⟩ := htrio
  have hqA0 : ((q : ℕ) : A) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  refine ⟨(cV : AlgebraicClosure ℚ), ?_, hGV⟩
  intro hz
  have hcV : cV = 0 := Subtype.ext hz
  apply hqA0
  rw [← hcd, hcV, zero_mul]

end ModularCurve.NodeLocalized

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet frobNodePair frobNodePair_fst ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC exists_hasValue_frobNodePair_of_forall_pole_not_centred CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData"
namespace CharPReduction
p2m_export "ModularCurve.CharPReduction" "coeffRed_coeff redRes redRes_apply redKer notMem_redKer_iff mem_localizedAtKer subring_le_localizedAtKer redLoc redRes_ne_zero_of_notMem redLoc_spec redLoc_coe constSeries modularRing jqModC_mem_modularRing jqNModC_mem_modularRing constSeries_mem_modularRing jqModC_mem_integralCoeffs modularRing_le_integralCoeffs modularLocalized modularRedLocHom modularRedLocHom_mem"
p2m_open "ModularCurve.CharPReduction ModularCurve~coeffEmb_jq"

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

theorem modularRedLocHom_congr {x y : LaurentSeries L} (hxy : x = y)
    (hx : x ∈ modularLocalized N A red) (hy : y ∈ modularLocalized N A red) :
    modularRedLocHom N A red ⟨x, hx⟩ = modularRedLocHom N A red ⟨y, hy⟩ := by
  subst hxy
  rfl

theorem modularRedLocHom_inv_eq {x : LaurentSeries L} (hx : x ∈ modularLocalized N A red)
    (hx0 : modularRedLocHom N A red ⟨x, hx⟩ ≠ 0) (hi : x⁻¹ ∈ modularLocalized N A red) :
    modularRedLocHom N A red ⟨x⁻¹, hi⟩ = (modularRedLocHom N A red ⟨x, hx⟩)⁻¹ := by
  have hxne : x ≠ 0 := by
    intro h0
    apply hx0
    have h' : (⟨x, hx⟩ : modularLocalized N A red) = 0 := Subtype.ext h0
    rw [h', map_zero]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← map_mul, ← map_one (modularRedLocHom N A red)]
  congr 1
  exact Subtype.ext (mul_inv_cancel₀ hxne)

theorem modularRedLocHom_pow_eq {x : LaurentSeries L} (hx : x ∈ modularLocalized N A red) (n : ℕ)
    (hn : x ^ n ∈ modularLocalized N A red) :
    modularRedLocHom N A red ⟨x ^ n, hn⟩ = (modularRedLocHom N A red ⟨x, hx⟩) ^ n := by
  rw [← map_pow]
  congr 1

theorem modularRedLocHom_zpow_eq {x : LaurentSeries L} (hx : x ∈ modularLocalized N A red)
    (hx0 : modularRedLocHom N A red ⟨x, hx⟩ ≠ 0) (n : ℤ) (hn : x ^ n ∈ modularLocalized N A red) :
    modularRedLocHom N A red ⟨x ^ n, hn⟩ = (modularRedLocHom N A red ⟨x, hx⟩) ^ n := by
  cases n with
  | ofNat n =>
      have hn' : x ^ n ∈ modularLocalized N A red := by
        rw [Int.ofNat_eq_natCast, zpow_natCast] at hn
        exact hn
      rw [modularRedLocHom_congr N A red (by rw [Int.ofNat_eq_natCast, zpow_natCast]) hn hn',
        modularRedLocHom_pow_eq N A red hx n hn', Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc n =>
      obtain ⟨hp, hp0⟩ := gaussUnit_pow N A red ⟨hx, hx0⟩ (n + 1)
      have hn' : (x ^ (n + 1))⁻¹ ∈ modularLocalized N A red := by
        rw [zpow_negSucc] at hn
        exact hn
      rw [modularRedLocHom_congr N A red (zpow_negSucc x n) hn hn', modularRedLocHom_inv_eq N A red hp hp0 hn',
        modularRedLocHom_pow_eq N A red hx (n + 1) hp, zpow_negSucc]

end ModularCurve.CharPReduction

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet frobNodePair frobNodePair_fst ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC exists_hasValue_frobNodePair_of_forall_pole_not_centred CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "exists_twoBranchNormalisation_qpow_of_forall_centred_ord_eq_zero modularEval ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero gaussData_nodeCoord exists_hasValue_nodeCoord_of_centred"
p2m_open "ModularCurve.NodeLocalized ModularCurve~coeffEmb_jq"

section LevelCollapse

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)

theorem modularRedLocHom_mem_levelOne
    (g : CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red g ∈ modularFunctionFieldC k 1 := by
  have h := CharPReduction.modularRedLocHom_mem A.toSubring red (1 * q) g
  suffices heq : modularFunctionFieldC k (1 * q) = modularFunctionFieldC k 1 by rw [← heq]; exact h
  have key : ∀ (n : ℕ) [NeZero n], n = q → modularFunctionFieldC k n = modularFunctionFieldC k 1 := by
    intro n _ hn
    subst hn
    exact modularFunctionFieldC_self_collapse_unconditional k
  exact key (1 * q) (one_mul q)

end LevelCollapse

section ShapeBridge

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] {red : A →+* k} {a : k}

theorem forall_pole_not_centred_of_forall_centred_ord_eq_zero
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0) :
    ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f < 0 →
      ¬ ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) :=
  fun W hlt hc => absurd (hford W hc) (ne_of_lt hlt)

end ShapeBridge

section GaussValue

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] (red : A →+* k)

theorem red_natCast_mul_inv_nodeCoord [CharP k q] [IsAlgClosed k] [DecidableEq k] (hq : 5 ≤ q) (a : k)
    (ha : a ∈ ssJSet q k) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    ∃ PR : Polynomial k, Polynomial.eval a PR ≠ 0 ∧
      ∃ (h₁ : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q))⁻¹ :
            modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
          CharPReduction.modularLocalized (1 * q) A.toSubring red),
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩
          = Polynomial.aeval (jqModC k) (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k)
            * (Polynomial.aeval (jqModC k) PR)⁻¹ := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨J, hJ⟩ : ∃ J : ↥(modularFunctionFieldBar (1 * q)), J = ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ := ⟨_, rfl⟩
  obtain ⟨JQ, hJQ⟩ : ∃ JQ : ↥(modularFunctionFieldBar (1 * q)), JQ = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ := ⟨_, rfl⟩
  rw [← hJ, ← hJQ]
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

  refine ⟨MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
      (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
        (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring), ?_, ?_⟩
  · rw [eval_graphReduce red a, eval₂Hom_kroneckerPolynomial red a R]
    exact hRne

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
  have hseries : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (JQ - J ^ q)⁻¹ :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * Rser⁻¹ :=
    (congrArg Subtype.val hident).trans hcoe
  obtain ⟨h₁, -⟩ := CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hseries.symm
    (gaussUnit_of_mem_modularRing_div red hHmem hRmem hHred' hRred')
  refine ⟨h₁, ?_⟩
  have hRser0 : Rser ≠ 0 := by
    intro h0'
    apply hRred'
    have hx : (⟨Rser, hRmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 := Subtype.ext h0'
    rw [hx, map_zero]
  have hpres : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (JQ - J ^ q)⁻¹ :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        * ((⟨Rser, hRmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) : LaurentSeries (AlgebraicClosure ℚ))
      = ((⟨((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)), hHmem⟩ :
          ↥(CharPReduction.modularRing (1 * q) A.toSubring)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    show _ * Rser = ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
    rw [hseries, mul_assoc, inv_mul_cancel₀ hRser0, mul_one]
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨_, h₁⟩ hpres

  have hR' : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨Rser, hRmem⟩
      = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
          (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
            (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)) := by
    have hx : (⟨Rser, hRmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = ⟨modularEval (1 * q) A.toSubring
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring), modularEval_mem_modularRing (1 * q) _⟩ := Subtype.ext hRser
    rw [hx, redRes_modularEval]
  have hH' : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
      ⟨((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)), hHmem⟩
      = Polynomial.aeval (jqModC k) (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k) := by
    have hx : (⟨_, hHmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring))
        = ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularRing (1 * q) _⟩ :=
      Subtype.ext hHser
    rw [hx, redRes_modularEval, map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_zero, ← pow_mul, ← sq]
  rw [hR', hH'] at hspec
  show CharPReduction.redLoc _ = _
  refine (eq_mul_inv_iff_mul_eq₀ ?_).mpr hspec
  rw [← hR']
  exact hRred'

end GaussValue

end ModularCurve.NodeLocalized

namespace Ws23
namespace NodePlaceAPI

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.AlgebraicCurve IsLocalRing Polynomial"

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

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.AlgebraicCurve IsLocalRing Polynomial ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.ModularCurve"

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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23"

namespace Ws23
namespace NodePlaceAPI

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.AlgebraicCurve AlgebraicCurve.RationalFunctionField~ord_placeOfPoint_algebraMap IsLocalRing Polynomial ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.ModularCurve"

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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23.NodePlaceAPI"

end Ws23.NodePlaceAPI
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23.NodePlaceAPI"

namespace ModularCurve p2m_export "ModularCurve" "CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet frobNodePair frobNodePair_fst ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC exists_hasValue_frobNodePair_of_forall_pole_not_centred CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.derivative_X_sub_X_pow_sq (k : Type*) [CommRing k] (p : ℕ) [CharP k p] :
    Polynomial.derivative (Polynomial.X - Polynomial.X ^ (p ^ 2) : Polynomial k) = 1 := by
  rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_X_pow]
  have : ((p ^ 2 : ℕ) : k) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero k p, zero_pow two_ne_zero]
  rw [this, map_zero, zero_mul, sub_zero]

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.rootMultiplicity_X_sub_X_pow_sq_eq_one (k : Type*) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (b : k) (hb : b ^ (p ^ 2) = b) :
    (Polynomial.X - Polynomial.X ^ (p ^ 2) : Polynomial k).rootMultiplicity b = 1 := by
  set Q : Polynomial k := Polynomial.X - Polynomial.X ^ (p ^ 2) with hQ
  have hp : p.Prime := Fact.out
  have hQ0 : Q ≠ 0 := by
    intro h
    have h' : (Polynomial.X : Polynomial k) = Polynomial.X ^ (p ^ 2) := sub_eq_zero.mp h
    have hdeg := congrArg Polynomial.natDegree h'
    rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow] at hdeg
    rcases pow_eq_one_iff.mp hdeg.symm with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact two_ne_zero h1
  have hroot : Q.IsRoot b := by
    simp only [hQ, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_pow, hb,
      sub_self]
  have hge : 1 ≤ Q.rootMultiplicity b := (Polynomial.rootMultiplicity_pos hQ0).mpr hroot
  have hle : Q.rootMultiplicity b ≤ 1 := by
    by_contra hlt
    have hlt' : 1 < Q.rootMultiplicity b := not_le.mp hlt
    have hder := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hlt'
    rw [Function.iterate_one, hQ, ModularCurve.derivative_X_sub_X_pow_sq k p] at hder
    simp at hder
  omega

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet frobNodePair frobNodePair_fst ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC exists_hasValue_frobNodePair_of_forall_pole_not_centred CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "exists_twoBranchNormalisation_qpow_of_forall_centred_ord_eq_zero modularEval ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero gaussData_nodeCoord exists_hasValue_nodeCoord_of_centred"
p2m_open "ModularCurve.NodeLocalized ModularCurve~coeffEmb_jq"

theorem coe_aeval_jC1 (K : Type*) [Field K] (p : Polynomial K) :
    ((Polynomial.aeval (Ws23.NodePlaceAPI.jC1 K) p : ↥(modularFunctionFieldC K 1)) : LaurentSeries K)
      = Polynomial.aeval (jqModC K) p := by
  have h := Polynomial.aeval_algHom_apply (modularFunctionFieldC K 1).val (Ws23.NodePlaceAPI.jC1 K) p

  exact h.symm

end ModularCurve.NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23 P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.Ws23.NodePlaceAPI"

p2m_open "ModularCurve~coeffEmb_jq" in open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.AlgebraicCurve IsLocalRing _root_.P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.ModularCurve _root_.ModularCurve.NodeLocalized _root_.P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg.ModularCurve.NodeLocalized in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0) (m : ℤ)
      (h₁ : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (h₂ : ((frickeInvolutionBar (1 * q) (((c * (q : AlgebraicClosure ℚ) ^ m) • f : modularFunctionFieldBar (1 * q))) : modularFunctionFieldBar (1 * q)) :
          LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 ∧
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0 ∧
        (frobNodePair q a).1.ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) = -m := by
  obtain ⟨c, hc0, m, h₁, h₂, hu₁, hu₂⟩ :=
    exists_twoBranchNormalisation_qpow_of_forall_centred_ord_eq_zero red hker hq a ha ha2 h0 h1728 f hf hford
  have h₁F := modularRedLocHom_mem_levelOne red ⟨_, h₁⟩
  refine ⟨c, hc0, m, h₁, h₂, h₁F, hu₁, hu₂, ?_⟩
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

  have hGdata := gaussData_nodeCoord red hq a ha h0 h1728
  have hGval := red_natCast_mul_inv_nodeCoord red hq a ha h0 h1728
  obtain ⟨Gq, hGq_def⟩ : ∃ Gq : ↥(modularFunctionFieldBar (1 * q)), Gq = ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) := ⟨_, rfl⟩
  rw [← hGq_def] at hGdata hGval
  obtain ⟨hG₁, hG₂⟩ := hGdata
  obtain ⟨PR, hPRa, hG₁m, hGred⟩ := hGval
  obtain ⟨hG₁m', hG₁u⟩ := hG₁

  have hsm₁ : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) :=
    congrArg Subtype.val (Algebra.smul_def c f)
  have hsm₂ : ((frickeInvolutionBar (1 * q) (((c * (q : AlgebraicClosure ℚ) ^ m) • f : modularFunctionFieldBar (1 * q))) : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = ((frickeInvolutionBar (1 * q)
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c * (q : AlgebraicClosure ℚ) ^ m) * f) : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) :=
    congrArg (fun z : ↥(modularFunctionFieldBar (1 * q)) => ((frickeInvolutionBar (1 * q) z : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)))
      (Algebra.smul_def (c * (q : AlgebraicClosure ℚ) ^ m) f)

  have hgauss := gaussUnit_corrected red c m f Gq
    (CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hsm₁ ⟨h₁, hu₁⟩)
    (CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hsm₂ ⟨h₂, hu₂⟩) ⟨hG₁m', hG₁u⟩ hG₂
  obtain ⟨hg1, hg2⟩ := hgauss
  obtain ⟨g, hg_def⟩ : ∃ g : ↥(modularFunctionFieldBar (1 * q)), g = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f
      * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * Gq⁻¹) ^ m := ⟨_, rfl⟩
  rw [← hg_def] at hg1 hg2

  have hford_g : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → V.ord g = 0 := by
    intro V hV
    have hGv := exists_hasValue_nodeCoord_ne_zero red hker hq a ha ha2 h0 h1728 V hV
    obtain ⟨cV, hcV0, hGV⟩ := hGv
    rw [← hGq_def] at hGV
    have hfv := exists_hasValue_ne_zero_of_ord_eq_zero V hf (hford V hV)
    obtain ⟨aV, haV0, haV⟩ := hfv
    have hgV := hasValue_corrected V c hq0 m haV hGV hcV0
    rw [← hg_def] at hgV
    exact hgV.ord_eq_zero
      (mul_ne_zero (mul_ne_zero hc0 haV0) (zpow_ne_zero _ (mul_ne_zero hq0 (inv_ne_zero hcV0))))

  obtain ⟨hg1m, hg1u⟩ := hg1
  obtain ⟨hg2m, hg2u⟩ := hg2
  have hg1F := modularRedLocHom_mem_levelOne red ⟨_, hg1m⟩
  have hg2F := modularRedLocHom_mem_levelOne red ⟨_, hg2m⟩
  have hpole_g := forall_pole_not_centred_of_forall_centred_ord_eq_zero (a := a) g hford_g
  obtain ⟨c₀, hc₁, -⟩ :=
    ModularCurve.exists_hasValue_frobNodePair_of_forall_pole_not_centred red a ha ha2 g hg1m hg1F hg2m hg2F hpole_g
  have hc₀ : c₀ ≠ 0 :=
    ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero red hker a ha ha2 h0 h1728 g
      hg1m hg1F hg1u hg2m hg2F hg2u hford_g c₀ hc₁
  have hordg : (frobNodePair q a).1.ord (⟨_, hg1F⟩ : ↥(modularFunctionFieldC k 1)) = 0 := hc₁.ord_eq_zero hc₀

  have h₁' : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f : modularFunctionFieldBar (1 * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [← hsm₁]
    exact h₁
  obtain ⟨hzm, -⟩ := CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red ⟨hG₁m', hG₁u⟩ m
  have coe_zpow : ∀ (x : ↥(modularFunctionFieldBar (1 * q))) (n : ℤ), ((x ^ n : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) ^ n := by
    intro x n
    cases n with
    | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, IntermediateField.coe_pow]
    | negSucc n => rw [zpow_negSucc, zpow_negSucc, IntermediateField.coe_inv, IntermediateField.coe_pow]
  have hgsplit : (⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hg1m⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red))
      = ⟨_, h₁'⟩ * ⟨_, hzm⟩ := by
    apply Subtype.ext
    show (g : LaurentSeries (AlgebraicClosure ℚ)) = _ * _
    rw [hg_def, MulMemClass.coe_mul, coe_zpow]
  have hredg : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg1m⟩
      = CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩
        * (CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hG₁m'⟩) ^ m := by
    rw [hgsplit, map_mul, CharPReduction.modularRedLocHom_zpow_eq (1 * q) A.toSubring red hG₁m' hG₁u m hzm,
      CharPReduction.modularRedLocHom_congr (1 * q) A.toSubring red hsm₁.symm h₁' h₁]

  have hzF := modularRedLocHom_mem_levelOne red ⟨_, hG₁m'⟩
  set u : ↥(modularFunctionFieldC k 1) := ⟨_, h₁F⟩ with hu
  set z : ↥(modularFunctionFieldC k 1) := ⟨_, hzF⟩ with hz
  have coe_zpowC : ∀ (x : ↥(modularFunctionFieldC k 1)) (n : ℤ), ((x ^ n : modularFunctionFieldC k 1) : LaurentSeries k) = (x : LaurentSeries k) ^ n := by
    intro x n
    cases n with
    | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, IntermediateField.coe_pow]
    | negSucc n => rw [zpow_negSucc, zpow_negSucc, IntermediateField.coe_inv, IntermediateField.coe_pow]
  have hgC : (⟨_, hg1F⟩ : ↥(modularFunctionFieldC k 1)) = u * z ^ m := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, coe_zpowC]
    exact hredg
  have hu0 : u ≠ 0 := by
    intro h
    apply hu₁
    have h' : (u : LaurentSeries k) = 0 := by rw [h]; rfl
    exact h'
  have hz0 : z ≠ 0 := by
    intro h
    apply hG₁u
    have h' : (z : LaurentSeries k) = 0 := by rw [h]; rfl
    exact h'

  have hzval : z = Polynomial.aeval (Ws23.NodePlaceAPI.jC1 k) (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k)
      * (Polynomial.aeval (Ws23.NodePlaceAPI.jC1 k) PR)⁻¹ := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, IntermediateField.coe_inv, coe_aeval_jC1, coe_aeval_jC1]
    exact hGred
  have hXH : Polynomial.aeval (Ws23.NodePlaceAPI.jC1 k) (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k) ≠ 0 := by
    intro h0'
    have h := Ws23.NodePlaceAPI.ord_charLGeomPlaceOfPoint_aeval k a (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k)
    rw [h0', Place.ord_zero, rootMultiplicity_X_sub_X_pow_sq_eq_one k q a ha2] at h
    norm_num at h
  have hPR0 : PR ≠ 0 := fun h => hPRa (by rw [h, Polynomial.eval_zero])
  have hXPR : Polynomial.aeval (Ws23.NodePlaceAPI.jC1 k) PR ≠ 0 := by
    intro h0'
    apply transcendental_jqModC k
    refine ⟨PR, hPR0, ?_⟩
    rw [← coe_aeval_jC1, h0']
    rfl
  have hordz : (frobNodePair q a).1.ord z = 1 := by
    rw [frobNodePair_fst, hzval, Place.ord_mul _ hXH (inv_ne_zero hXPR), Place.ord_inv,
      Ws23.NodePlaceAPI.ord_charLGeomPlaceOfPoint_aeval, Ws23.NodePlaceAPI.ord_charLGeomPlaceOfPoint_aeval,
      rootMultiplicity_X_sub_X_pow_sq_eq_one k q a ha2, Polynomial.rootMultiplicity_eq_zero hPRa]
    norm_num

  have hzm0 : z ^ m ≠ 0 := zpow_ne_zero m hz0
  have hord := hordg
  rw [hgC, Place.ord_mul _ hu0 hzm0, Place.ord_zpow, hordz, mul_one] at hord
  show (frobNodePair q a).1.ord u = -m
  omega

end S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_twoBranchNormalisation_qpow_and_ord_charLGeomPlaceOfPoint_eq_neg (solution)
