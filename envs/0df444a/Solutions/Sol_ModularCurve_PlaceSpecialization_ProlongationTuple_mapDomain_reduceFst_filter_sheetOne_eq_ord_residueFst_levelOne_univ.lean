-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c0e01a16-1799-5fcf-afd7-6ded9fb87fdc

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_of_reduceFst_fixed_ordinary_levelOne_univ
import Theorems.Thm_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary_univ
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueSnd_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_modularUnit_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange"
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.LevelOnePhi.instAddCommGroup WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

namespace DivOne

open Classical

variable {q : ℕ} [Fact q.Prime]
  {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
  [CharP k q] [DecidableEq k] [IsAlgClosed k] [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
  {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

noncomputable def L (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop)
    (v : Place k ↥(modularFunctionFieldC k 1)) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : ℤ :=
  ∑ W ∈ D.support, (if P.reduceFst W = v ∧ p W then D W else 0)

noncomputable def μ (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (v : Place k ↥(modularFunctionFieldC k 1)) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : ℕ :=
  ∑ W ∈ D.support, (if P.reduceFst W = v then (D W).natAbs else 0)

theorem mapDomain_eq_sum (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (v : Place k ↥(modularFunctionFieldC k 1)) (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    Finsupp.mapDomain P.reduceFst X v = ∑ W ∈ X.support, (if P.reduceFst W = v then X W else 0) := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_congr rfl fun W _ => ?_
  simp only [Finsupp.single_apply]

theorem mapDomain_filter_eq_L (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop) [DecidablePred p]
    (v : Place k ↥(modularFunctionFieldC k 1)) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    Finsupp.mapDomain P.reduceFst (D.filter p) v = L P p v D := by
  rw [mapDomain_eq_sum]
  unfold L
  rw [Finsupp.support_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.filter_apply]
  by_cases hp : p W <;> by_cases hv : P.reduceFst W = v <;> simp [hp, hv]

theorem L_shift (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop)
    (v : Place k ↥(modularFunctionFieldC k 1)) (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (W₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW₀ : P.reduceFst W₀ = v)
    (c : ℤ) (hoff : ∀ W, P.reduceFst W = v → W ≠ W₀ → D' W = D W) (hon : D' W₀ = D W₀ + c) :
    L P p v D' = L P p v D + (if p W₀ then c else 0) := by

  set S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) := D.support ∪ D'.support ∪ {W₀} with hS
  have hW₀S : W₀ ∈ S := by simp [hS]
  have key : ∀ X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), X.support ⊆ S →
      L P p v X = ∑ W ∈ S, (if P.reduceFst W = v ∧ p W then X W else 0) := by
    intro X hX
    unfold L
    refine Finset.sum_subset hX fun W _ hW => ?_
    rw [Finsupp.notMem_support_iff.mp hW]
    simp
  rw [key D (by intro W hW; simp [hS, hW]), key D' (by intro W hW; simp [hS, hW]),
    ← Finset.add_sum_erase S _ hW₀S, ← Finset.add_sum_erase S _ hW₀S]
  have hrest : ∑ W ∈ S.erase W₀, (if P.reduceFst W = v ∧ p W then D' W else 0)
      = ∑ W ∈ S.erase W₀, (if P.reduceFst W = v ∧ p W then D W else 0) := by
    refine Finset.sum_congr rfl fun W hW => ?_
    have hne : W ≠ W₀ := Finset.ne_of_mem_erase hW
    by_cases hv : P.reduceFst W = v
    · rw [hoff W hv hne]
    · simp [hv]
  rw [hrest, hon]
  by_cases hpW : p W₀
  · simp [hpW, hW₀]; ring
  · simp [hpW]

theorem μ_shift (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (v : Place k ↥(modularFunctionFieldC k 1)) (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (W₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW₀ : P.reduceFst W₀ = v)
    (hoff : ∀ W, P.reduceFst W = v → W ≠ W₀ → D' W = D W) (hon : (D' W₀).natAbs + 1 = (D W₀).natAbs) :
    μ P v D' + 1 = μ P v D := by
  set S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) := D.support ∪ D'.support ∪ {W₀} with hS
  have hW₀S : W₀ ∈ S := by simp [hS]
  have key : ∀ X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), X.support ⊆ S →
      μ P v X = ∑ W ∈ S, (if P.reduceFst W = v then (X W).natAbs else 0) := by
    intro X hX
    unfold μ
    refine Finset.sum_subset hX fun W _ hW => ?_
    rw [Finsupp.notMem_support_iff.mp hW]
    simp
  rw [key D (by intro W hW; simp [hS, hW]), key D' (by intro W hW; simp [hS, hW]),
    ← Finset.add_sum_erase S _ hW₀S, ← Finset.add_sum_erase S _ hW₀S]
  have hrest : ∑ W ∈ S.erase W₀, (if P.reduceFst W = v then (D' W).natAbs else 0)
      = ∑ W ∈ S.erase W₀, (if P.reduceFst W = v then (D W).natAbs else 0) := by
    refine Finset.sum_congr rfl fun W hW => ?_
    have hne : W ≠ W₀ := Finset.ne_of_mem_erase hW
    by_cases hv : P.reduceFst W = v
    · rw [hoff W hv hne]
    · simp [hv]
  rw [hrest, if_pos hW₀, if_pos hW₀, ← hon]
  ring

theorem exists_of_μ_ne_zero (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (v : Place k ↥(modularFunctionFieldC k 1)) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (h : μ P v D ≠ 0) :
    ∃ W₀, P.reduceFst W₀ = v ∧ D W₀ ≠ 0 := by
  obtain ⟨W, -, hW⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hv : P.reduceFst W = v
  · refine ⟨W, hv, ?_⟩
    rw [if_pos hv] at hW
    exact Int.natAbs_ne_zero.mp hW
  · rw [if_neg hv] at hW
    exact absurd rfl hW

theorem forall_eq_zero_of_μ_eq_zero (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (v : Place k ↥(modularFunctionFieldC k 1)) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (h : μ P v D = 0) :
    ∀ W, P.reduceFst W = v → D W = 0 := by
  intro W hW
  by_cases hmem : W ∈ D.support
  · have h' := (Finset.sum_eq_zero_iff.mp h) W hmem
    rw [if_pos hW] at h'
    exact Int.natAbs_eq_zero.mp h'
  · exact Finsupp.notMem_support_iff.mp hmem

theorem exists_step (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (u : ↥(modularFunctionFieldBar (1 * q))) (hu : (u : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (v : Place k ↥(modularFunctionFieldC k 1))
    (hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v)
    (haff : IsAffineGeomPlace k 1 v) (hord : v ∉ ssPlaces q 1 k)
    (W₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW₀ : P.reduceFst W₀ = v) :
    ∃ (g : ↥(modularFunctionFieldBar (1 * q))) (hg₁ : g ∈ R.R₁.integers), R.R₁.residue ⟨g, hg₁⟩ ≠ 0 ∧ g ≠ 0 ∧
      (∀ W, P.reduceFst W = v → W.ord g = if W = W₀ then -1 else 0) ∧
      v.ord (R.residue₁ ⟨g, hg₁⟩) = (if (∃ a : A, red a ≠ 0 ∧ W₀.HasValue u (a : AlgebraicClosure ℚ)) then -1 else 0) := by
  have hfix' : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst W₀)) = P.reduceFst W₀ := by
    rw [hW₀]; exact hfix
  have haff' : IsAffineGeomPlace k 1 (P.reduceFst W₀) := by rw [hW₀]; exact haff
  have hord' : P.reduceFst W₀ ∉ ssPlaces q 1 k := by rw [hW₀]; exact hord
  obtain ⟨g, hg₁, hg₂, hr₁, hr₂, hordW₀, hothers, hpat⟩ :=
    ProlongationTuple.exists_commonUnit_pole_of_reduceFst_fixed_ordinary_levelOne_univ q A k red data hKr hα hβ P R hR hO W₀ hfix' haff' hord' ∅ {v}
  have hg0 : g ≠ 0 := fun h0 => by rw [h0, Place.ord_zero] at hordW₀; exact absurd hordW₀ (by norm_num)

  have hpole : ∀ W, P.reduceFst W = v → W ≠ W₀ → 0 ≤ W.ord g := by
    intro W hW hne
    by_contra hlt
    push_neg at hlt
    obtain ⟨-, hB, -⟩ := hothers W hne hlt
    exact hB (by rw [hW]; exact Finset.mem_singleton_self v)

  obtain ⟨Dg, hDg, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) g hg0
  have hsum : Finsupp.mapDomain P.reduceFst Dg v = -1 := by
    rw [hO g hg₁ hg₂ hr₁ hr₂ Dg hDg v hfix haff]
    rw [hW₀] at hpat
    rcases hpat with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> norm_num

  have hzero : ∀ W, P.reduceFst W = v → W ≠ W₀ → Dg W = 0 := by
    have hW₀mem : W₀ ∈ Dg.support := by
      rw [Finsupp.mem_support_iff, hDg, hordW₀]; norm_num
    rw [mapDomain_eq_sum, ← Finset.add_sum_erase _ _ hW₀mem, if_pos hW₀, hDg W₀, hordW₀] at hsum
    have hrest : ∑ W ∈ Dg.support.erase W₀, (if P.reduceFst W = v then Dg W else 0) = 0 := by linarith
    have hnn : ∀ W ∈ Dg.support.erase W₀, 0 ≤ (if P.reduceFst W = v then Dg W else 0) := by
      intro W hW
      split_ifs with hv
      · rw [hDg]; exact hpole W hv (Finset.ne_of_mem_erase hW)
      · exact le_rfl
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hrest
    intro W hW hne
    by_cases hmem : W ∈ Dg.support
    · have := hall W (Finset.mem_erase.mpr ⟨hne, hmem⟩)
      rwa [if_pos hW] at this
    · exact Finsupp.notMem_support_iff.mp hmem
  have hprof : ∀ W, P.reduceFst W = v → W.ord g = if W = W₀ then -1 else 0 := by
    intro W hW
    split_ifs with h
    · rw [h]; exact hordW₀
    · rw [← hDg]; exact hzero W hW h

  have hpole' : ∀ W, P.reduceFst W = P.reduceFst W₀ → W ≠ W₀ → 0 ≤ W.ord g := fun W hW hne =>
    hpole W (hW.trans hW₀) hne
  refine ⟨g, hg₁, hr₁, hg0, hprof, ?_⟩
  by_cases hs : ∃ a : A, red a ≠ 0 ∧ W₀.HasValue u (a : AlgebraicClosure ℚ)
  · rw [if_pos hs]
    obtain ⟨a, ha, hval⟩ := hs
    have hS1 := ProlongationTuple.ord_residueSnd_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_modularUnit_levelOne
      P R u hu g hg₁ hg₂ hr₂ W₀ hfix' haff' hpole' a ha hval
    rw [hW₀] at hpat hS1
    rcases hpat with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exfalso; rw [h2] at hS1; exact absurd hS1 (by norm_num)
  · rw [if_neg hs]
    obtain ⟨hor, -⟩ := hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary_univ P u hu W₀ hfix' haff' hord'
    obtain ⟨a, ha, hval⟩ := hor.resolve_left hs
    have hS2 := ProlongationTuple.ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_frickeInvolutionBar_modularUnit_levelOne
      P R u hu g hg₁ hg₂ hr₁ W₀ hfix' haff' hpole' a ha hval
    rw [hW₀] at hpat hS2
    rcases hpat with ⟨h1, -⟩ | ⟨h1, -⟩
    · exfalso; rw [h1] at hS2; exact absurd hS2 (by norm_num)
    · exact h1

theorem base_case (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (v : Place k ↥(modularFunctionFieldC k 1))
    (hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v)
    (haff : IsAffineGeomPlace k 1 v) (hord : v ∉ ssPlaces q 1 k)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers) (hres : R.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (hbase : ∀ W, P.reduceFst W = v → W.ord f = 0) :
    v.ord (R.residue₁ ⟨f, h₁⟩) = 0 := by

  have hrat : v.IsRational := (Place.isRational_iff_deg_eq_one v).mpr (place_deg_eq_one_of_isAlgClosed k 1 v)
  have hva : v = charLGeomPlaceOfPoint k (v.evalAt (jGeomGen k 1)) :=
    eq_charLGeomPlaceOfPoint_of_ord_pos
      (ord_sub_evalAt_pos_of_isRational hrat haff.1 (jGeomGen_sub_algebraMap_ne_zero k 1 _))
  have ha₀ : v.evalAt (jGeomGen k 1) ∉ ssJSet q k := fun hss =>
    hord ((mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k v).mpr ⟨_, hss, hva.symm⟩)

  have hf' : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
    (R.mem_integersFst_iff f).mp h₁
  obtain ⟨h₁'', e⟩ := R.residue₁_eq_modularRedLocHom f hf'
  have h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hf'⟩ ∈ modularFunctionFieldC k 1 := by
    rw [← e]; exact (R.ι (R.R₁.residue ⟨f, h₁''⟩)).2
  have hρ : (⟨CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hf'⟩, h₁F⟩ : ↥(modularFunctionFieldC k 1))
      = R.residue₁ ⟨f, h₁⟩ := by
    apply Subtype.ext
    show CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hf'⟩ = _
    rw [← e]
    rfl
  have h₁0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hf'⟩ ≠ 0 := by
    rw [← e]
    intro h0
    apply hres
    have hι : R.ι (R.R₁.residue ⟨f, h₁''⟩) = 0 := Subtype.ext h0
    have := (map_eq_zero_iff _ R.ι.injective).mp hι
    exact this
  have key := ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet red f hf' h₁F h₁0
    (v.evalAt (jGeomGen k 1)) ha₀ (fun W hW hcen => by
      obtain ⟨⟨x, hx, hxo⟩, -⟩ := hcen
      have hred : P.redFst W = charLGeomPlaceOfPoint k (v.evalAt (jGeomGen k 1)) :=
        (P.redFst_eq_charLGeomPlaceOfPoint_iff W _).mpr ⟨x, hx, hxo⟩
      have hWv : P.reduceFst W = v := by
        rw [hva]
        exact hred
      exact hW (hbase W hWv))
  rw [hρ, ← hva] at key
  exact key

theorem inv_mem_integers_of_residue_ne_zero {L F Fbar : Type*} [Field L] [Field F] [Algebra L F] [Field Fbar]
    {A₀ : ValuationSubring L} [Algebra (IsLocalRing.ResidueField A₀) Fbar]
    (R : AlgebraicCurve.RegularProlongation A₀ F Fbar) (f : F) (h : f ∈ R.integers) (hr : R.residue ⟨f, h⟩ ≠ 0) :
    ∃ h' : f⁻¹ ∈ R.integers, R.residue ⟨f⁻¹, h'⟩ = (R.residue ⟨f, h⟩)⁻¹ := by
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hr
  have hval : (((u⁻¹ : R.integersˣ) : R.integers) : F) = f⁻¹ := by
    have h1 : (((u⁻¹ : R.integersˣ) : R.integers) : F) * f = 1 := by
      have := congrArg (fun x : R.integers => (x : F)) u.inv_mul
      rw [hu] at this
      simpa using this
    exact eq_inv_of_mul_eq_one_left h1
  have hmem : f⁻¹ ∈ R.integers := by rw [← hval]; exact ((u⁻¹ : R.integersˣ) : R.integers).2
  refine ⟨hmem, ?_⟩
  have e : (⟨f⁻¹, hmem⟩ : R.integers) = ((u⁻¹ : R.integersˣ) : R.integers) := Subtype.ext hval.symm
  apply eq_inv_of_mul_eq_one_left
  rw [e, ← hu, ← map_mul, u.inv_mul, map_one]

end DivOne

open DivOne in
open Classical in

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] [DecidableEq k] [IsAlgClosed k] [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (u : modularFunctionFieldBar (1 * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q)) :
    ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
        (∀ W, D W = W.ord f) →
        ∀ v : Place k (modularFunctionFieldC k 1),
          frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
          IsAffineGeomPlace k 1 v → v ∉ ssPlaces q 1 k →
          Finsupp.mapDomain P.reduceFst
              (D.filter fun W => ((frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst W)) = P.reduceFst W ∧
        IsAffineGeomPlace k 1 (P.reduceFst W) ∧ P.reduceFst W ∉ ssPlaces q 1 k) ∧
        (∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)))) v
            = v.ord (R.residue₁ ⟨f, h₁⟩) := by
  intro f h₁ hres D hD v hfix haff hord

  suffices H : ∀ (n : ℕ) (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers), R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), (∀ W, D W = W.ord f) → μ P v D = n →
        L P (fun W => ((frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst W)) = P.reduceFst W ∧
        IsAffineGeomPlace k 1 (P.reduceFst W) ∧ P.reduceFst W ∉ ssPlaces q 1 k) ∧
        (∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)))) v D = v.ord (R.residue₁ ⟨f, h₁⟩) by
    rw [mapDomain_filter_eq_L]
    exact H _ f h₁ hres D hD rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro f h₁ hres D hD hμ
  have hf0 : f ≠ 0 := by
    intro h0; apply hres
    have : (⟨f, h₁⟩ : R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  by_cases hn : n = 0
  ·
    subst hn
    have hz := forall_eq_zero_of_μ_eq_zero P v D hμ
    have hL : L P (fun W => ((frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst W)) = P.reduceFst W ∧
        IsAffineGeomPlace k 1 (P.reduceFst W) ∧ P.reduceFst W ∉ ssPlaces q 1 k) ∧
        (∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)))) v D = 0 := by
      unfold L
      refine Finset.sum_eq_zero fun W _ => ?_
      split_ifs with h
      · exact hz W h.1
      · rfl
    rw [hL, base_case P R hR hO v hfix haff hord f h₁ hres (fun W hW => by rw [← hD W]; exact hz W hW)]
  ·
    obtain ⟨W₀, hW₀v, hW₀⟩ := exists_of_μ_ne_zero P v D (hμ ▸ hn)
    obtain ⟨g, hg₁, hgres, hg0, hprof, hpat⟩ := exists_step P R hR hO u hu v hfix haff hord W₀ hW₀v
    obtain ⟨Dg, hDg, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) g hg0
    have hsheet : ((fun W => ((frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst W)) = P.reduceFst W ∧
        IsAffineGeomPlace k 1 (P.reduceFst W) ∧ P.reduceFst W ∉ ssPlaces q 1 k) ∧
        (∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)))) W₀) ↔ (∃ a : A, red a ≠ 0 ∧ W₀.HasValue u (a : AlgebraicClosure ℚ)) := by
      constructor
      · exact fun h => h.2
      · intro h; refine ⟨?_, h⟩; rw [hW₀v]; exact ⟨hfix, haff, hord⟩
    rcases lt_or_gt_of_ne hW₀ with hneg | hpos
    ·
      obtain ⟨hg₁', eres⟩ := inv_mem_integers_of_residue_ne_zero R.R₁ g hg₁ hgres
      have h₁' : f * g⁻¹ ∈ R.R₁.integers := mul_mem h₁ hg₁'
      have eres' : R.R₁.residue ⟨f * g⁻¹, h₁'⟩ = R.R₁.residue ⟨f, h₁⟩ * (R.R₁.residue ⟨g, hg₁⟩)⁻¹ := by
        rw [← eres, ← map_mul]; rfl
      have hres' : R.R₁.residue ⟨f * g⁻¹, h₁'⟩ ≠ 0 := by
        rw [eres']; exact mul_ne_zero hres (inv_ne_zero hgres)
      have hD' : ∀ W, (D - Dg) W = W.ord (f * g⁻¹) := fun W => by
        rw [Finsupp.sub_apply, hD, hDg, Place.ord_mul _ hf0 (inv_ne_zero hg0), Place.ord_inv]; ring
      have hoff : ∀ W, P.reduceFst W = v → W ≠ W₀ → (D - Dg) W = D W := fun W hW hne => by
        rw [Finsupp.sub_apply, hDg, hprof W hW, if_neg hne, sub_zero]
      have hon : (D - Dg) W₀ = D W₀ + 1 := by
        rw [Finsupp.sub_apply, hDg, hprof W₀ hW₀v, if_pos rfl]; ring
      have hμ' : μ P v (D - Dg) + 1 = n := by
        rw [← hμ]
        refine μ_shift P v D (D - Dg) W₀ hW₀v hoff ?_
        rw [hon]; omega
      have IH' := IH (μ P v (D - Dg)) (by omega) (f * g⁻¹) h₁' hres' (D - Dg) hD' rfl
      rw [L_shift P _ v D (D - Dg) W₀ hW₀v 1 hoff hon] at IH'

      have eρ : (R.residue₁ ⟨f * g⁻¹, h₁'⟩ : ↥(modularFunctionFieldC k 1)) = R.residue₁ ⟨f, h₁⟩ * (R.residue₁ ⟨g, hg₁⟩)⁻¹ := by
        rw [ProlongationTuple.residue₁_apply, ProlongationTuple.residue₁_apply, ProlongationTuple.residue₁_apply,
          eres', map_mul, map_inv₀]
      have hρf : (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := by
        rw [ProlongationTuple.residue₁_apply]; exact (map_ne_zero_iff _ R.ι.injective).mpr hres
      have hρg : (R.residue₁ ⟨g, hg₁⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := by
        rw [ProlongationTuple.residue₁_apply]; exact (map_ne_zero_iff _ R.ι.injective).mpr hgres
      rw [eρ, Place.ord_mul _ hρf (inv_ne_zero hρg), Place.ord_inv, hpat] at IH'
      simp only [hsheet] at IH'
      split_ifs at IH' with hs <;> omega
    ·
      have h₁' : f * g ∈ R.R₁.integers := mul_mem h₁ hg₁
      have eres' : R.R₁.residue ⟨f * g, h₁'⟩ = R.R₁.residue ⟨f, h₁⟩ * R.R₁.residue ⟨g, hg₁⟩ := by
        rw [← map_mul]; rfl
      have hres' : R.R₁.residue ⟨f * g, h₁'⟩ ≠ 0 := by rw [eres']; exact mul_ne_zero hres hgres
      have hD' : ∀ W, (D + Dg) W = W.ord (f * g) := fun W => by
        rw [Finsupp.add_apply, hD, hDg, Place.ord_mul _ hf0 hg0]
      have hoff : ∀ W, P.reduceFst W = v → W ≠ W₀ → (D + Dg) W = D W := fun W hW hne => by
        rw [Finsupp.add_apply, hDg, hprof W hW, if_neg hne, add_zero]
      have hon : (D + Dg) W₀ = D W₀ + (-1) := by
        rw [Finsupp.add_apply, hDg, hprof W₀ hW₀v, if_pos rfl]
      have hμ' : μ P v (D + Dg) + 1 = n := by
        rw [← hμ]
        refine μ_shift P v D (D + Dg) W₀ hW₀v hoff ?_
        rw [hon]; omega
      have IH' := IH (μ P v (D + Dg)) (by omega) (f * g) h₁' hres' (D + Dg) hD' rfl
      rw [L_shift P _ v D (D + Dg) W₀ hW₀v (-1) hoff hon] at IH'
      have eρ : (R.residue₁ ⟨f * g, h₁'⟩ : ↥(modularFunctionFieldC k 1)) = R.residue₁ ⟨f, h₁⟩ * R.residue₁ ⟨g, hg₁⟩ := by
        rw [ProlongationTuple.residue₁_apply, ProlongationTuple.residue₁_apply, ProlongationTuple.residue₁_apply,
          eres', map_mul]
      have hρf : (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := by
        rw [ProlongationTuple.residue₁_apply]; exact (map_ne_zero_iff _ R.ι.injective).mpr hres
      have hρg : (R.residue₁ ⟨g, hg₁⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := by
        rw [ProlongationTuple.residue₁_apply]; exact (map_ne_zero_iff _ R.ι.injective).mpr hgres
      rw [eρ, Place.ord_mul _ hρf hρg, hpat] at IH'
      simp only [hsheet] at IH'
      split_ifs at IH' with hs <;> omega

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ (solution)
