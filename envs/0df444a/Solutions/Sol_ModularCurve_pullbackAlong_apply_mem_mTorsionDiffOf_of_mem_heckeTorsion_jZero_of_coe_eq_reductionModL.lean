-- Prove2me | solution 1 for ModularCurve.pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/3783b0c3-2c18-53c6-bf9b-30a15139a56c

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_HeckeOperatorModL
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Theorems.Thm_ModularCurve_reductionModL_heckeOperatorBar_of_ne
import Theorems.Thm_ModularCurve_reductionModL_heckeOperatorBar
import Theorems.Thm_ModularCurve_reductionInputsModL_of_not_dvd
import Theorems.Thm_ModularCurve_heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_apply_eq_heckeU_of_congr_coe_eq_frobeniusPushforwardModL
import Theorems.Thm_ModularCurve_apply_eq_traceAlong_pullbackAlong_of_coe_eq_heckePic0Fibre
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_traceAlong_pullbackAlong_eq_heckeT
import Theorems.Thm_ModularCurve_heckeInputsFibre_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_Module_CommFamilyAnnPart
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_AlgebraicCurve_cartierOperator_existsUnique
import Definitions.Def_ModularCurve_MTorsionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Theorems.Thm_AlgebraicCurve_Differential_pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap
import Theorems.Thm_ModularCurve_exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap
import Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd
import Theorems.Thm_ModularCurve_apply_mem_regularDifferentials_of_recipe
import Theorems.Thm_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver
import Theorems.Thm_ModularCurve_apply_mem_regularDifferentials_of_recipe
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_AlgebraicCurve_Differential_traceAlong_eq_traceDiff
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_cartier_eq_coeffMap_frobeniusEquiv_symm_heckeU
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_modularFunctionFieldC_injective_of_thetaL_ne_zero_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_isQExpansionDiffAlong_qExpansionDiffAlong
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqModC
import Theorems.Thm_AlgebraicCurve_Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing"
p2m_attr_erase "instance" "TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T"
p2m_attr_erase "simp" "ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero"
p2m_attr_erase "simp" "AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one ModularCurve.coe_jqNGen AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open ModularCurve AlgebraicCurve IsLocalRing

namespace E3TParts

theorem heckeT_eq_heckeU_of_natCast_eq_zero (R : Type*) [CommRing R] (ℓ : ℕ) (hℓ : 0 < ℓ) (k : ℕ) (hk : 2 ≤ k)
    (h0 : (ℓ : R) = 0) : LaurentSeries.heckeT R ℓ hℓ k = LaurentSeries.heckeU R ℓ hℓ := by
  have hk' : k - 1 ≠ 0 := by omega
  rw [LaurentSeries.heckeT, h0, zero_pow hk', zero_smul, add_zero]

theorem delta_of_coe_eq_reduction_heckeGen
    (M : ℕ) [NeZero M] (hcomm : HeckeOperatorsCommuteBar M) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (hE : modularFunctionFieldC (ResidueField ↥A) M = modularFunctionFieldFullC (ResidueField ↥A) M)
    (δ : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p →+ Ω[↥(modularFunctionFieldC (ResidueField ↥A) M)⁄(ResidueField ↥A)])
    (hδ : ∀ (y : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)
        (E : Divisor.degZero (K := (ResidueField ↥A)) (F := modularFunctionFieldC (ResidueField ↥A) M)) (g : modularFunctionFieldC (ResidueField ↥A) M),
        Pic0.mk E = (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) → g ≠ 0 →
        (∀ v : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M), (p : ℤ) * (E : Divisor (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) g)
    (q : ℕ) [Fact q.Prime] (hqp : q ≠ p) (hin : HeckeInputsFibre (ResidueField ↥A) M q)
    (x : JZero M) (y y' : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)
    (hy : (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) = (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (reductionModL A M x))
    (hy' : (y' : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) =
      (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (reductionModL A M (letI := heckeModuleBar M; heckeGen ⟨q, Fact.out⟩ • x))) :
    δ y' = Differential.traceAlong (heckeAlphaC (ResidueField ↥A) M q) (Differential.pullbackAlong (heckeBetaC (ResidueField ↥A) M q) (δ y)) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hred := ModularCurve.reductionModL_heckeOperatorBar_of_ne M hpM A hA
    (ModularCurve.reductionInputsModL_of_not_dvd M hpM A hA) q Fact.out hqp hE hin x
  have hgen : (letI := heckeModuleBar M; heckeGen ⟨q, Fact.out⟩ • x) = heckeOperatorBar M ⟨q, Fact.out⟩ x :=
    heckeModuleBar_heckeGen_smul hcomm ⟨q, Fact.out⟩ x
  have hyy : (y' : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) = heckePic0Fibre (ResidueField ↥A) M q (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) := by
    rw [hy', hgen, hred, AddEquiv.symm_apply_apply, ← hy]
  exact ModularCurve.apply_eq_traceAlong_pullbackAlong_of_coe_eq_heckePic0Fibre (ResidueField ↥A) p M hpM q hqp δ hδ y y' hyy

theorem qExpansionDiffAlong_traceAlong_pullbackAlong_eq_heckeT_of_ne
    (κ : Type*) [Field κ] [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (M q : ℕ) [NeZero M] [Fact q.Prime] (hpM : ¬ p ∣ M) (hqp : q ≠ p) (hqM : ¬ q ∣ M)
    (ω : Ω[↥(modularFunctionFieldC κ M)⁄κ]) :
    qExpansionDiffAlong (modularFunctionFieldC κ M).val
        (Differential.traceAlong (heckeAlphaC κ M q) (Differential.pullbackAlong (heckeBetaC κ M q) ω))
      = LaurentSeries.heckeT κ q (Fact.out : q.Prime).pos 2 (qExpansionDiffAlong (modularFunctionFieldC κ M).val ω) := by
  have hq0 : (q : κ) ≠ 0 := fun h =>
    hqp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp ((CharP.cast_eq_zero_iff κ p q).mp h)).symm
  haveI : NeZero (q : κ) := ⟨hq0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := κ) (n := q)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (Fact.out : q.Prime).ne_zero
  have hpMq : ¬ p ∣ M * q := fun h => by
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
    · exact hpM h
    · exact hqp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h).symm
  exact ModularCurve.qExpansionDiffAlong_traceAlong_pullbackAlong_eq_heckeT κ M q hpMq hqM (Units.mk0 ζ hζ0)
    (by simpa using hζ) ω

theorem congr_coe_eq_frobeniusPushforwardModL_of_coe_eq_reduction_heckeGen_self
    (M : ℕ) [NeZero M] (hcomm : HeckeOperatorsCommuteBar M) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (hE : modularFunctionFieldC (ResidueField ↥A) M = modularFunctionFieldFullC (ResidueField ↥A) M)
    (x : JZero M) (hxp : (p : ℤ) • x = 0)
    (y y_p : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)
    (hy : (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) = (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (reductionModL A M x))
    (hy_p : (y_p : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) =
      (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (reductionModL A M (letI := heckeModuleBar M; heckeGen ⟨p, Fact.out⟩ • x))) :
    (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)) (y_p : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) = frobeniusPushforwardModL (ResidueField ↥A) M p ((Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)) (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M))) := by
  have hgen : (letI := heckeModuleBar M; heckeGen ⟨p, Fact.out⟩ • x) = heckeOperatorBar M ⟨p, Fact.out⟩ x :=
    heckeModuleBar_heckeGen_smul hcomm ⟨p, Fact.out⟩ x
  have hred := ModularCurve.reductionModL_heckeOperatorBar M hpM A hA (ModularCurve.reductionInputsModL_of_not_dvd M hpM A hA) x
  have htors : (p : ℤ) • reductionModL A M x = 0 := by rw [← map_zsmul, hxp, map_zero]
  rw [hy_p, hy, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hgen, hred]
  exact ModularCurve.heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero (ResidueField ↥A) p M _ htors

theorem qExpansionDiffAlong_delta_eq_heckeU_of_coe_eq_reduction_heckeGen_self
    (M : ℕ) [NeZero M] (hcomm : HeckeOperatorsCommuteBar M) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    [IsCurveOver (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)]
    (hE : modularFunctionFieldC (ResidueField ↥A) M = modularFunctionFieldFullC (ResidueField ↥A) M)
    (C : Ω[↥(modularFunctionFieldC (ResidueField ↥A) M)⁄(ResidueField ↥A)] →+ Ω[↥(modularFunctionFieldC (ResidueField ↥A) M)⁄(ResidueField ↥A)])
    (hsemi : ∀ (f : modularFunctionFieldC (ResidueField ↥A) M) (ω : Ω[↥(modularFunctionFieldC (ResidueField ↥A) M)⁄(ResidueField ↥A)]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : modularFunctionFieldC (ResidueField ↥A) M, C (KaehlerDifferential.D (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) f) = 0)
    (hlog : ∀ f : modularFunctionFieldC (ResidueField ↥A) M,
      C (f ^ (p - 1) • KaehlerDifferential.D (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) f) = KaehlerDifferential.D (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) f)
    (δ : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p →+ Ω[↥(modularFunctionFieldC (ResidueField ↥A) M)⁄(ResidueField ↥A)])
    (hδ : ∀ (y : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)
        (E : Divisor.degZero (K := (ResidueField ↥A)) (F := modularFunctionFieldC (ResidueField ↥A) M)) (g : modularFunctionFieldC (ResidueField ↥A) M),
        Pic0.mk E = (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) → g ≠ 0 →
        (∀ v : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M), (p : ℤ) * (E : Divisor (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) g)
    (x : JZero M) (hxp : (p : ℤ) • x = 0)
    (y y_p : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)
    (hy : (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) = (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (reductionModL A M x))
    (hy_p : (y_p : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) =
      (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (reductionModL A M (letI := heckeModuleBar M; heckeGen ⟨p, Fact.out⟩ • x))) :
    qExpansionDiffAlong (modularFunctionFieldC (ResidueField ↥A) M).val (δ y_p) =
      LaurentSeries.heckeU (ResidueField ↥A) p (Fact.out : p.Prime).pos (qExpansionDiffAlong (modularFunctionFieldC (ResidueField ↥A) M).val (δ y)) :=
  ModularCurve.qExpansionDiffAlong_apply_eq_heckeU_of_congr_coe_eq_frobeniusPushforwardModL (ResidueField ↥A) p M hE C hsemi hker hlog
    δ hδ y y_p
    (congr_coe_eq_frobeniusPushforwardModL_of_coe_eq_reduction_heckeGen_self M hcomm p hpM A hA hE x hxp y y_p hy hy_p)

theorem heckeInputsFibre_of_ne (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) (q : ℕ) [Fact q.Prime] (hqp : q ≠ p) :
    HeckeInputsFibre κ M q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq0 : (q : κ) ≠ 0 := fun h =>
    hqp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp ((CharP.cast_eq_zero_iff κ p q).mp h)).symm
  have hM0 : (M : κ) ≠ 0 := fun h => hpM ((CharP.cast_eq_zero_iff κ p M).mp h)
  haveI := ModularCurve.hasPrincipalDivisors_charLDegeneracyRoof κ M q hM0 hq0
  exact ModularCurve.heckeInputsFibre_of_natCast_ne_zero κ M q hq0

theorem zsmul_eq_zero_of_mem_heckeTorsion (M : ℕ) [NeZero M] (p : ℕ) (𝔪 : Ideal HeckeAlg)
    (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪) (x : JZero M)
    (hx : letI := heckeModuleBar M; x ∈ heckeTorsion (JZero M) 𝔪) : (p : ℤ) • x = 0 := by
  letI := heckeModuleBar M
  have h := (mem_heckeTorsion_iff (JZero M) 𝔪 x).mp hx _ hp𝔪
  have hC : ((p : ℕ) : HeckeAlg) = MvPolynomial.C (p : ℤ) := by simp
  rw [hC, heckeModuleBar_C_smul] at h
  exact h

theorem apply_mem_annPart_of_forall_apply_heckeGen_smul
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime]
    {κ : Type*} [Field κ] [CharP κ p] {V : Type*} [AddCommGroup V] [Module κ V]
    (N : letI := heckeModuleBar M; Submodule HeckeAlg (JZero M))
    (Fam : Module.End.CommFamily κ V Nat.Primes)
    (Φ : letI := heckeModuleBar M; ↥N →+ V)
    (hΦ : letI := heckeModuleBar M; ∀ (ℓ : Nat.Primes) (z : ↥N), Φ (heckeGen ℓ • z) = Fam.T ℓ (Φ z))
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (e : HeckeAlg ⧸ 𝔪 →+* κ)
    (x : letI := heckeModuleBar M; ↥N)
    (hx : letI := heckeModuleBar M; (x : JZero M) ∈ heckeTorsion (JZero M) 𝔪) :
    letI := heckeModuleBar M
    Φ x ∈ Fam.annPart p (fun ℓ : Nat.Primes => e (Ideal.Quotient.mk 𝔪 (heckeGen ℓ))) := by
  letI := heckeModuleBar M
  classical

  have hpoly : ∀ (t : HeckeAlg) (z : ↥N), Φ (t • z) = Fam.eval (MvPolynomial.map (Int.castRingHom κ) t) (Φ z) := by
    intro t
    induction t using MvPolynomial.induction_on with
    | C a =>
      intro z
      have hz : (MvPolynomial.C a : HeckeAlg) • z = a • z := by
        apply Subtype.ext
        rw [Submodule.coe_smul, Submodule.coe_smul_of_tower]
        exact heckeModuleBar_C_smul a (z : JZero M)
      rw [hz, map_zsmul, MvPolynomial.map_C, Module.End.CommFamily.eval_C, eq_intCast, Module.algebraMap_end_apply,
        Int.cast_smul_eq_zsmul]
    | add t t' ht ht' =>
      intro z
      rw [add_smul, map_add, ht, ht', map_add, map_add, LinearMap.add_apply]
    | mul_X t ℓ ht =>
      intro z
      have hX : (MvPolynomial.X ℓ : HeckeAlg) = heckeGen ℓ := rfl
      rw [mul_smul, ht, hX, hΦ, map_mul, map_mul, Module.End.mul_apply, ← hX, MvPolynomial.map_X,
        Module.End.CommFamily.eval_X]

  rw [Module.End.CommFamily.mem_annPart_iff]
  intro Qbar hQ
  obtain ⟨Q, rfl⟩ := MvPolynomial.map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) Qbar
  have hmap : MvPolynomial.map (ZMod.castHom (dvd_refl p) κ) (MvPolynomial.map (Int.castRingHom (ZMod p)) Q) =
      MvPolynomial.map (Int.castRingHom κ) Q := by
    rw [MvPolynomial.map_map, RingHom.ext_int ((ZMod.castHom (dvd_refl p) κ).comp (Int.castRingHom (ZMod p))) (Int.castRingHom κ)]
  rw [hmap] at hQ ⊢

  have heval : e (Ideal.Quotient.mk 𝔪 Q) = MvPolynomial.aeval (fun ℓ : Nat.Primes => e (Ideal.Quotient.mk 𝔪 (heckeGen ℓ)))
      (MvPolynomial.map (Int.castRingHom κ) Q) := by
    have key : (e.comp (Ideal.Quotient.mk 𝔪)) =
        (MvPolynomial.aeval (R := κ) (fun ℓ : Nat.Primes => e (Ideal.Quotient.mk 𝔪 (heckeGen ℓ)))).toRingHom.comp
          (MvPolynomial.map (Int.castRingHom κ)) := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp
      · intro ℓ
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          MvPolynomial.map_X, MvPolynomial.aeval_X]
        rfl
    exact congrArg (fun f : HeckeAlg →+* κ => f Q) key
  have hQ0 : Ideal.Quotient.mk 𝔪 Q = 0 := by
    letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    apply e.injective
    rw [map_zero, heval, hQ]
  have hQmem : Q ∈ 𝔪 := Ideal.Quotient.eq_zero_iff_mem.mp hQ0

  have hQx : Q • x = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_zero]
    exact (mem_heckeTorsion_iff (JZero M) 𝔪 _).mp hx Q hQmem
  have := hpoly Q x
  rw [hQx, map_zero] at this
  exact this.symm

end E3TParts

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace E3TParts

open AlgebraicCurve

section Twisted

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def TwistedDiff (g : SemilinearAut K F) : Type _ := Ω[F⁄K]

namespace TwistedDiff

variable (g : SemilinearAut K F)

scoped instance : AddCommGroup (TwistedDiff g) := inferInstanceAs (AddCommGroup (Ω[F⁄K]))

def of : Ω[F⁄K] ≃+ TwistedDiff g := AddEquiv.refl _

scoped instance instModuleF : Module F (TwistedDiff g) :=
  Module.compHom (Ω[F⁄K]) ((SemilinearAut.toRingAut g : F ≃+* F) : F →+* F)

scoped instance instModuleK : Module K (TwistedDiff g) :=
  Module.compHom (Ω[F⁄K]) ((SemilinearAut.baseAut g : K ≃+* K) : K →+* K)

theorem smulF_def (f : F) (ω : Ω[F⁄K]) : (f • of g ω : TwistedDiff g) = of g ((g • f) • ω) := rfl

theorem smulK_def (a : K) (ω : Ω[F⁄K]) : (a • of g ω : TwistedDiff g) = of g ((SemilinearAut.baseAut g a) • ω) := rfl

scoped instance : IsScalarTower K F (TwistedDiff g) :=
  ⟨fun a f ω => by
    show of g ((g • (a • f)) • (of g).symm ω) = of g (SemilinearAut.baseAut g a • ((g • f) • (of g).symm ω))
    rw [Algebra.smul_def, smul_mul', SemilinearAut.smul_algebraMap, mul_smul, algebraMap_smul]⟩

noncomputable def deriv : Derivation K F (TwistedDiff g) where
  toFun x := of g (KaehlerDifferential.D K F (g • x))
  map_add' x y := by simp only [smul_add, map_add]
  map_smul' a x := by
    show of g (KaehlerDifferential.D K F (g • (a • x))) = of g (SemilinearAut.baseAut g a • KaehlerDifferential.D K F (g • x))
    rw [Algebra.smul_def, smul_mul', SemilinearAut.smul_algebraMap, ← Algebra.smul_def, Derivation.map_smul]
  map_one_eq_zero' := by
    show of g (KaehlerDifferential.D K F (g • (1 : F))) = 0
    rw [smul_one, Derivation.map_one_eq_zero]; rfl
  leibniz' x y := by
    show of g (KaehlerDifferential.D K F (g • (x * y))) =
      of g ((g • x) • (of g).symm (of g (KaehlerDifferential.D K F (g • y)))) +
        of g ((g • y) • (of g).symm (of g (KaehlerDifferential.D K F (g • x))))
    rw [smul_mul', Derivation.leibniz]
    rfl

theorem deriv_apply (x : F) : deriv g x = of g (KaehlerDifferential.D K F (g • x)) := rfl

end TwistedDiff
p2m_reactivate "P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts.TwistedDiff"

theorem exists_semilinearDiffMap (g : SemilinearAut K F) :
    ∃ S : Ω[F⁄K] →+ Ω[F⁄K],
      (∀ x : F, S (KaehlerDifferential.D K F x) = KaehlerDifferential.D K F (g • x)) ∧
      (∀ (f : F) (ω : Ω[F⁄K]), S (f • ω) = (g • f) • S ω) := by
  let L : Ω[F⁄K] →ₗ[F] TwistedDiff g := (TwistedDiff.deriv g).liftKaehlerDifferential
  refine ⟨((TwistedDiff.of g).symm : TwistedDiff g →+ Ω[F⁄K]).comp L.toAddMonoidHom, fun x => ?_, fun f ω => ?_⟩
  · show (TwistedDiff.of g).symm (L (KaehlerDifferential.D K F x)) = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl
  · show (TwistedDiff.of g).symm (L (f • ω)) = (g • f) • (TwistedDiff.of g).symm (L ω)
    rw [map_smul]
    rfl

theorem addMonoidHom_ext_of_twist {M : Type*} [AddCommMonoid M] (act : F → M →+ M)
    (T T' : Ω[F⁄K] →+ M)
    (hT : ∀ (f : F) (ω : Ω[F⁄K]), T (f • ω) = act f (T ω))
    (hT' : ∀ (f : F) (ω : Ω[F⁄K]), T' (f • ω) = act f (T' ω))
    (hD : ∀ x : F, T (KaehlerDifferential.D K F x) = T' (KaehlerDifferential.D K F x)) : T = T' := by
  ext ω
  have hmem : ω ∈ Submodule.span F (Set.range (KaehlerDifferential.D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx => obtain ⟨y, rfl⟩ := hx; exact hD y
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul f x _ hx => rw [hT, hT', hx]

theorem semilinearDiffMap_comp_pullbackAlong_eq (g : SemilinearAut K F) (S : Ω[F⁄K] →+ Ω[F⁄K])
    (hSD : ∀ x : F, S (KaehlerDifferential.D K F x) = KaehlerDifferential.D K F (g • x))
    (hSs : ∀ (f : F) (ω : Ω[F⁄K]), S (f • ω) = (g • f) • S ω)
    (w : F ≃ₐ[K] F) (hw : ∀ x : F, w (g • x) = g • (w x)) :
    S.comp (Differential.pullbackAlong (w : F →ₐ[K] F)).toAddMonoidHom =
      (Differential.pullbackAlong (w : F →ₐ[K] F)).toAddMonoidHom.comp S := by
  refine addMonoidHom_ext_of_twist (fun f => DistribSMul.toAddMonoidHom (Ω[F⁄K]) (g • (w f))) _ _ ?_ ?_ ?_
  · intro f ω
    show S (Differential.pullbackAlong (w : F →ₐ[K] F) (f • ω)) = (g • w f) • S (Differential.pullbackAlong (w : F →ₐ[K] F) ω)
    rw [Differential.pullbackAlong_smul, hSs]; rfl
  · intro f ω
    show Differential.pullbackAlong (w : F →ₐ[K] F) (S (f • ω)) = (g • w f) • Differential.pullbackAlong (w : F →ₐ[K] F) (S ω)
    rw [hSs, Differential.pullbackAlong_smul, AlgEquiv.coe_algHom, hw]
  · intro x
    show S (Differential.pullbackAlong (w : F →ₐ[K] F) (KaehlerDifferential.D K F x)) =
      Differential.pullbackAlong (w : F →ₐ[K] F) (S (KaehlerDifferential.D K F x))
    rw [Differential.pullbackAlong_D, hSD, hSD, Differential.pullbackAlong_D]
    show KaehlerDifferential.D K F (g • w x) = KaehlerDifferential.D K F (w (g • x))
    rw [hw]

end Twisted
p2m_reactivate "P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts.TwistedDiff"

section QExpansion

open ModularCurve

theorem coeff_derivative_field {L : Type*} [Field L] (f : LaurentSeries L) (n : ℤ) :
    (LaurentSeries.derivative L f).coeff n = (n + 1) * f.coeff (n + 1) := by
  simp [LaurentSeries.derivative_apply]

theorem coeffMap_thetaL {K K' : Type*} [Field K] [Field K'] (τ : K →+* K') (s : LaurentSeries K) :
    coeffMap τ (thetaL K s) = thetaL K' (coeffMap τ s) := by
  ext a
  rw [coeffMap_coeff, thetaL_apply, thetaL_apply, HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul, one_mul,
    one_mul, coeff_derivative_field, coeff_derivative_field, map_mul, coeffMap_coeff]
  simp

theorem qExpansionDiffAlong_semilinearDiffMap_eq_coeffMap
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (τ : K ≃+* K)
    (S : Ω[↥(modularFunctionFieldC K N)⁄K] →+ Ω[↥(modularFunctionFieldC K N)⁄K])
    (hSD : ∀ x : modularFunctionFieldC K N,
      S (KaehlerDifferential.D K (modularFunctionFieldC K N) x) =
        KaehlerDifferential.D K (modularFunctionFieldC K N) (coeffSemilinearAut N τ • x))
    (hSs : ∀ (f : modularFunctionFieldC K N) (ω : Ω[↥(modularFunctionFieldC K N)⁄K]),
      S (f • ω) = (coeffSemilinearAut N τ • f) • S ω)
    (hq : IsQExpansionDiffAlong (modularFunctionFieldC K N).val (qExpansionDiffAlong (modularFunctionFieldC K N).val))
    (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) :
    qExpansionDiffAlong (modularFunctionFieldC K N).val (S ω) =
      coeffMap (τ : K →+* K) (qExpansionDiffAlong (modularFunctionFieldC K N).val ω) := by
  have key := addMonoidHom_ext_of_twist
    (fun f : modularFunctionFieldC K N => AddMonoidHom.mulLeft (coeffMap (τ : K →+* K) (f : LaurentSeries K)))
    ((qExpansionDiffAlong (modularFunctionFieldC K N).val).toAddMonoidHom.comp S)
    ((coeffMap (τ : K →+* K)).toAddMonoidHom.comp (qExpansionDiffAlong (modularFunctionFieldC K N).val).toAddMonoidHom)
    ?_ ?_ ?_
  · exact DFunLike.congr_fun key ω
  · intro f η
    show qExpansionDiffAlong _ (S (f • η)) = coeffMap (τ : K →+* K) (f : LaurentSeries K) * qExpansionDiffAlong _ (S η)
    rw [hSs]
    exact hq.2 _ _
  · intro f η
    show coeffMap (τ : K →+* K) (qExpansionDiffAlong _ (f • η)) =
      coeffMap (τ : K →+* K) (f : LaurentSeries K) * coeffMap (τ : K →+* K) (qExpansionDiffAlong _ η)
    have h2 : qExpansionDiffAlong (modularFunctionFieldC K N).val (f • η) =
        (f : LaurentSeries K) * qExpansionDiffAlong (modularFunctionFieldC K N).val η := hq.2 _ _
    exact (congrArg (coeffMap (τ : K →+* K)) h2).trans (map_mul _ _ _)
  · intro x
    show qExpansionDiffAlong _ (S (KaehlerDifferential.D K _ x)) =
      coeffMap (τ : K →+* K) (qExpansionDiffAlong _ (KaehlerDifferential.D K _ x))
    rw [hSD]
    have e1 : qExpansionDiffAlong (modularFunctionFieldC K N).val
        (KaehlerDifferential.D K (modularFunctionFieldC K N) (coeffSemilinearAut N τ • x)) =
          thetaL K (coeffMap (τ : K →+* K) (x : LaurentSeries K)) := hq.1 _
    have e2 : qExpansionDiffAlong (modularFunctionFieldC K N).val (KaehlerDifferential.D K (modularFunctionFieldC K N) x) =
        thetaL K (x : LaurentSeries K) := hq.1 _
    exact e1.trans ((coeffMap_thetaL (τ : K →+* K) (x : LaurentSeries K)).symm.trans (congrArg _ e2).symm)

end QExpansion
p2m_reactivate "P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts.TwistedDiff"

section Cartier

theorem cartier_comp_pullbackAlong_eq {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (w : F ≃ₐ[K] F) :
    C.comp (Differential.pullbackAlong (w : F →ₐ[K] F)).toAddMonoidHom =
      (Differential.pullbackAlong (w : F →ₐ[K] F)).toAddMonoidHom.comp C := by

  set P : Ω[F⁄K] →+ Ω[F⁄K] := (Differential.pullbackAlong (w : F →ₐ[K] F)).toAddMonoidHom with hP
  set Q : Ω[F⁄K] →+ Ω[F⁄K] := (Differential.pullbackAlong (w.symm : F →ₐ[K] F)).toAddMonoidHom with hQ
  have hPs : ∀ (f : F) (ω : Ω[F⁄K]), P (f • ω) = w f • P ω := fun f ω => Differential.pullbackAlong_smul _ f ω
  have hQs : ∀ (f : F) (ω : Ω[F⁄K]), Q (f • ω) = w.symm f • Q ω := fun f ω => Differential.pullbackAlong_smul _ f ω
  have hPD : ∀ f : F, P (KaehlerDifferential.D K F f) = KaehlerDifferential.D K F (w f) :=
    fun f => Differential.pullbackAlong_D _ f
  have hQD : ∀ f : F, Q (KaehlerDifferential.D K F f) = KaehlerDifferential.D K F (w.symm f) :=
    fun f => Differential.pullbackAlong_D _ f
  have hQP : Q.comp P = AddMonoidHom.id _ := by
    refine addMonoidHom_ext_of_twist (fun f => DistribSMul.toAddMonoidHom (Ω[F⁄K]) f) _ _ ?_ ?_ ?_
    · intro f ω; show Q (P (f • ω)) = f • Q (P ω); rw [hPs, hQs, AlgEquiv.symm_apply_apply]
    · intro f ω; rfl
    · intro f; show Q (P (KaehlerDifferential.D K F f)) = KaehlerDifferential.D K F f; rw [hPD, hQD, AlgEquiv.symm_apply_apply]
  have hPQ : P.comp Q = AddMonoidHom.id _ := by
    refine addMonoidHom_ext_of_twist (fun f => DistribSMul.toAddMonoidHom (Ω[F⁄K]) f) _ _ ?_ ?_ ?_
    · intro f ω; show P (Q (f • ω)) = f • P (Q ω); rw [hQs, hPs, AlgEquiv.apply_symm_apply]
    · intro f ω; rfl
    · intro f; show P (Q (KaehlerDifferential.D K F f)) = KaehlerDifferential.D K F f; rw [hQD, hPD, AlgEquiv.apply_symm_apply]

  let C' : Ω[F⁄K] →+ Ω[F⁄K] := Q.comp (C.comp P)
  have h1 : ∀ (f : F) (ω : Ω[F⁄K]), C' (f ^ p • ω) = f • C' ω := by
    intro f ω
    show Q (C (P (f ^ p • ω))) = f • Q (C (P ω))
    rw [hPs, map_pow, hsemi, hQs, AlgEquiv.symm_apply_apply]
  have h2 : ∀ f : F, C' (KaehlerDifferential.D K F f) = 0 := by
    intro f
    show Q (C (P (KaehlerDifferential.D K F f))) = 0
    rw [hPD, hker, map_zero]
  have h3 : ∀ f : F, C' (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f := by
    intro f
    show Q (C (P (f ^ (p - 1) • KaehlerDifferential.D K F f))) = KaehlerDifferential.D K F f
    rw [hPs, hPD, map_pow, hlog, hQD, AlgEquiv.symm_apply_apply]
  have hCC : C' = C :=
    (AlgebraicCurve.cartierOperator_existsUnique p x).unique ⟨h1, h2, h3⟩ ⟨hsemi, hker, hlog⟩

  have : P.comp C' = C.comp P := by
    show P.comp (Q.comp (C.comp P)) = C.comp P
    rw [← AddMonoidHom.comp_assoc, hPQ, AddMonoidHom.id_comp]
  rw [hCC] at this
  exact this.symm

end Cartier
p2m_reactivate "P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts.TwistedDiff"

end E3TParts
p2m_reactivate "P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts.TwistedDiff P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts"

end
p2m_reactivate "P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts.TwistedDiff P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts"

namespace GlueE6W
open AlgebraicCurve KaehlerDifferential

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
  [Algebra K F] [Algebra K F'] [Algebra K F'']

theorem pullbackAlong_comp (f : F →ₐ[K] F') (g : F' →ₐ[K] F'') (ω : Ω[F⁄K]) :
    Differential.pullbackAlong (g.comp f) ω =
      Differential.pullbackAlong g (Differential.pullbackAlong f ω) := by
  have hmem : ω ∈ Submodule.span F (Set.range (D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [Differential.pullbackAlong_D, Differential.pullbackAlong_D, Differential.pullbackAlong_D, AlgHom.comp_apply]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_smul, Differential.pullbackAlong_smul, hx,
      AlgHom.comp_apply]

theorem pullbackAlong_id (ω : Ω[F⁄K]) : Differential.pullbackAlong (AlgHom.id K F) ω = ω := by
  have hmem : ω ∈ Submodule.span F (Set.range (D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx => obtain ⟨b, rfl⟩ := hx; rw [Differential.pullbackAlong_D, AlgHom.id_apply]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => rw [Differential.pullbackAlong_smul, hx, AlgHom.id_apply]

theorem pullbackAlong_congr {f g : F →ₐ[K] F'} (h : ∀ x, f x = g x) :
    Differential.pullbackAlong f = Differential.pullbackAlong g := by
  have : f = g := AlgHom.ext h
  subst this; rfl

theorem pullbackAlong_symm_apply (w : F ≃ₐ[K] F) (ω : Ω[F⁄K]) :
    Differential.pullbackAlong (w.symm : F →ₐ[K] F) (Differential.pullbackAlong (w : F →ₐ[K] F) ω) = ω := by
  rw [← pullbackAlong_comp, pullbackAlong_congr (g := AlgHom.id K F) (fun x => by simp), pullbackAlong_id]

theorem pullbackAlong_apply_symm (w : F ≃ₐ[K] F) (ω : Ω[F⁄K]) :
    Differential.pullbackAlong (w : F →ₐ[K] F) (Differential.pullbackAlong (w.symm : F →ₐ[K] F) ω) = ω := by
  rw [← pullbackAlong_comp, pullbackAlong_congr (g := AlgHom.id K F) (fun x => by simp), pullbackAlong_id]

theorem pullbackAlong_injective (w : F ≃ₐ[K] F) :
    Function.Injective (Differential.pullbackAlong (w : F →ₐ[K] F)) := fun a b h => by
  have := congrArg (Differential.pullbackAlong (w.symm : F →ₐ[K] F)) h
  rwa [pullbackAlong_symm_apply, pullbackAlong_symm_apply] at this

theorem cartier_pullbackAlong [IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f)
    (w : F ≃ₐ[K] F) (ω : Ω[F⁄K]) :
    C (Differential.pullbackAlong (w : F →ₐ[K] F) ω) = Differential.pullbackAlong (w : F →ₐ[K] F) (C ω) := by
  set P := Differential.pullbackAlong (w : F →ₐ[K] F) with hP
  set Q := Differential.pullbackAlong (w.symm : F →ₐ[K] F) with hQ
  let C' : Ω[F⁄K] →+ Ω[F⁄K] := (Q.toAddMonoidHom.comp C).comp P.toAddMonoidHom
  have hC' : C' = C := by
    apply (cartierOperator_existsUnique (K := K) (F := F) p x).unique
    · refine ⟨?_, ?_, ?_⟩
      · intro f ω'
        show Q (C (P (f ^ p • ω'))) = f • Q (C (P ω'))
        rw [Differential.pullbackAlong_smul, map_pow, hsemi, Differential.pullbackAlong_smul]
        simp only [AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply]
        try rfl
      · intro f
        show Q (C (P (D K F f))) = 0
        rw [Differential.pullbackAlong_D, hker, map_zero]
      · intro f
        show Q (C (P (f ^ (p - 1) • D K F f))) = D K F f
        rw [Differential.pullbackAlong_smul, map_pow, Differential.pullbackAlong_D, hlog, Differential.pullbackAlong_D]
        simp only [AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply]
        try rfl
    · exact ⟨hsemi, hker, hlog⟩
  have h1 : Q (C (P ω)) = C ω := by
    have := congrArg (fun T : Ω[F⁄K] →+ Ω[F⁄K] => T ω) hC'
    exact this
  have h2 := congrArg P h1
  rw [pullbackAlong_apply_symm] at h2
  exact h2

end GlueE6W
p2m_reactivate "P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts.TwistedDiff P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts"

namespace E3TDoor

open ModularCurve AlgebraicCurve IsLocalRing

noncomputable abbrev congrE (M : ℕ) [NeZero M] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hE : modularFunctionFieldC (ResidueField ↥A) M = modularFunctionFieldFullC (ResidueField ↥A) M) :
    Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) ≃+
      Pic0 (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) M) :=
  Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)

theorem congr_symm_reductionModL_mem_torsion (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime]
    (𝔪 : Ideal HeckeAlg) (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hE : modularFunctionFieldC (ResidueField ↥A) M = modularFunctionFieldFullC (ResidueField ↥A) M)
    (x : JZero M) (hx : letI := heckeModuleBar M; x ∈ heckeTorsion (JZero M) 𝔪) :
    (congrE M A hE).symm (reductionModL A M x) ∈
      Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p := by
  refine (Pic0.mem_torsion (K := ResidueField ↥A) (F := modularFunctionFieldC (ResidueField ↥A) M)).mpr ?_
  rw [← map_zsmul, ← map_zsmul, E3TParts.zsmul_eq_zero_of_mem_heckeTorsion M p 𝔪 hp𝔪 x hx, map_zero, map_zero]

noncomputable def doorMap (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime]
    (𝔪 : Ideal HeckeAlg) (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hE : modularFunctionFieldC (ResidueField ↥A) M = modularFunctionFieldFullC (ResidueField ↥A) M) :
    letI := heckeModuleBar M
    ↥(heckeTorsion (JZero M) 𝔪) →+
      ↥(Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p) :=
  letI := heckeModuleBar M
  { toFun := fun x => ⟨(congrE M A hE).symm (reductionModL A M (x : JZero M)),
        congr_symm_reductionModL_mem_torsion M p 𝔪 hp𝔪 A hE x x.2⟩
    map_zero' := by
      apply Subtype.ext
      show (congrE M A hE).symm (reductionModL A M ((0 : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M)) = 0
      rw [ZeroMemClass.coe_zero, map_zero, map_zero]
    map_add' := fun x y => by
      apply Subtype.ext
      show (congrE M A hE).symm (reductionModL A M ((x + y : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M)) =
        (congrE M A hE).symm (reductionModL A M (x : JZero M)) +
          (congrE M A hE).symm (reductionModL A M (y : JZero M))
      rw [Submodule.coe_add, map_add, map_add] }

theorem coe_doorMap_apply (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime]
    (𝔪 : Ideal HeckeAlg) (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hE : modularFunctionFieldC (ResidueField ↥A) M = modularFunctionFieldFullC (ResidueField ↥A) M)
    (x : letI := heckeModuleBar M; ↥(heckeTorsion (JZero M) 𝔪)) :
    letI := heckeModuleBar M
    ((doorMap M p 𝔪 hp𝔪 A hE x : ↥(Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)) :
        Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) =
      (congrE M A hE).symm (reductionModL A M (x : JZero M)) :=
  rfl

end E3TDoor
p2m_reactivate "P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts.TwistedDiff P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts"

section Twist
open ModularCurve AlgebraicCurve IsLocalRing

namespace E3TTwistP

theorem thetaL_jqModC_ne_zero (K : Type*) [Field K] : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have hc : (thetaL K (jqModC K)).coeff (-1) = 0 := by rw [h]; rfl
  rw [thetaL_apply, HahnSeries.coeff_single_mul, one_mul, show (-1 : ℤ) - 1 = -2 by norm_num] at hc
  have hd := LaurentSeries.derivative_iterate_coeff (R := K) 1 (jqModC K) (-2)
  simp only [Function.iterate_one, Nat.cast_one] at hd
  rw [hd, show (-2 : ℤ) + 1 = -1 by norm_num, coeff_jqModC_neg_one] at hc
  simp [descPochhammer_one, Polynomial.smeval_X] at hc

theorem cartier_delta_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (p : ℕ) [hp : Fact p.Prime]
    (C : Ω[F⁄K] →+ Ω[F⁄K]) (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (δ : Pic0.torsion K F p →+ Ω[F⁄K])
    (hδ : ∀ (y : Pic0.torsion K F p) (E : Divisor.degZero (K := K) (F := F)) (g : F),
        Pic0.mk E = (y : Pic0 K F) → g ≠ 0 → (∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D K F g)
    (y : Pic0.torsion K F p) : C (δ y) = δ y := by
  obtain ⟨D, f, hDx, hf0, -, hord⟩ := Pic0.exists_mk_eq_and_dvd_ord_of_mem_torsion (x := (y : Pic0 K F)) y.2
  have hx : δ y = f⁻¹ • KaehlerDifferential.D K F f := hδ y D f hDx hf0 (fun v => (hord v).symm)
  rw [hx]
  have key : f⁻¹ • KaehlerDifferential.D K F f = (f⁻¹) ^ p • (f ^ (p - 1) • KaehlerDifferential.D K F f) := by
    rw [smul_smul]
    congr 1
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.out.one_le
    calc f⁻¹ = f⁻¹ * (f⁻¹ * f) ^ (p - 1) := by rw [inv_mul_cancel₀ hf0, one_pow, mul_one]
      _ = (f⁻¹) ^ p * f ^ (p - 1) := by rw [mul_pow, ← mul_assoc, ← pow_succ', hp1]
  conv_lhs => rw [key]
  rw [hsemi, hlog]

theorem algEquiv_smul_comm (K : Type*) [Field K] (N : ℕ) [NeZero N] (τ : K ≃+* K)
    (w : ↥(modularFunctionFieldC K N) ≃ₐ[K] ↥(modularFunctionFieldC K N))
    (hw1 : w ⟨jqModC K, jqModC_mem K N⟩ = ⟨jqNModC K N, jqNModC_mem K N⟩)
    (hw2 : w ⟨jqNModC K N, jqNModC_mem K N⟩ = ⟨jqModC K, jqModC_mem K N⟩)
    (x : ↥(modularFunctionFieldC K N)) :
    w (coeffSemilinearAut N τ • x) = coeffSemilinearAut N τ • (w x) := by
  obtain ⟨v, hv⟩ := x
  suffices h : ∀ (hv' : v ∈ modularFunctionFieldC K N),
      w (coeffSemilinearAut N τ • ⟨v, hv'⟩) = coeffSemilinearAut N τ • (w ⟨v, hv'⟩) from h hv
  induction hv using IntermediateField.adjoin_induction with
  | mem u hu =>
    intro hv'
    rcases hu with rfl | rfl
    · have e : (⟨jqModC K, hv'⟩ : ↥(modularFunctionFieldC K N)) = ⟨jqModC K, jqModC_mem K N⟩ := rfl
      rw [e, coeffSemilinearAut_smul_jq, hw1, coeffSemilinearAut_smul_jqN]
    · have e : (⟨jqNModC K N, hv'⟩ : ↥(modularFunctionFieldC K N)) = ⟨jqNModC K N, jqNModC_mem K N⟩ := rfl
      rw [e, coeffSemilinearAut_smul_jqN, hw2, coeffSemilinearAut_smul_jq]
  | algebraMap c =>
    intro hv'
    have e : (⟨algebraMap K (LaurentSeries K) c, hv'⟩ : ↥(modularFunctionFieldC K N)) =
        algebraMap K ↥(modularFunctionFieldC K N) c := rfl
    rw [e, SemilinearAut.smul_algebraMap, AlgEquiv.commutes, AlgEquiv.commutes, SemilinearAut.smul_algebraMap]
  | add a b ha hb iha ihb =>
    intro hv'
    have e : (⟨a + b, hv'⟩ : ↥(modularFunctionFieldC K N)) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, smul_add, map_add, map_add, smul_add, iha ha, ihb hb]
  | mul a b ha hb iha ihb =>
    intro hv'
    have e : (⟨a * b, hv'⟩ : ↥(modularFunctionFieldC K N)) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, smul_mul', map_mul, map_mul, smul_mul', iha ha, ihb hb]
  | inv a ha iha =>
    intro hv'
    have e : (⟨a⁻¹, hv'⟩ : ↥(modularFunctionFieldC K N)) = (⟨a, ha⟩ : ↥(modularFunctionFieldC K N))⁻¹ := rfl
    rw [e, smul_inv'', map_inv₀, map_inv₀, smul_inv'', iha ha]

end E3TTwistP
p2m_reactivate "P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts.TwistedDiff P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts"

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem E3T_twist_self
    (M : ℕ) [NeZero M] (hcomm : HeckeOperatorsCommuteBar M) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (hE : modularFunctionFieldC (ResidueField ↥A) M = modularFunctionFieldFullC (ResidueField ↥A) M)
    (δ : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p →+
      Ω[↥(modularFunctionFieldC (ResidueField ↥A) M)⁄(ResidueField ↥A)])
    (hδ : ∀ (y : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)
        (E : Divisor.degZero (K := ResidueField ↥A) (F := modularFunctionFieldC (ResidueField ↥A) M))
        (g : modularFunctionFieldC (ResidueField ↥A) M),
        Pic0.mk E = (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) → g ≠ 0 →
        (∀ v : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M),
          (p : ℤ) * (E : Divisor (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) g)
    (Fam : Module.End.CommFamily (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) Nat.Primes)
    (hFamT : ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M →
      Fam.T ℓ = LaurentSeries.heckeT (ResidueField ↥A) (ℓ : ℕ) ℓ.2.pos 2)
    (hFamU : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ M →
      Fam.T ℓ = LaurentSeries.heckeU (ResidueField ↥A) (ℓ : ℕ) ℓ.2.pos)
    (w : ↥(modularFunctionFieldC (ResidueField ↥A) M) ≃ₐ[ResidueField ↥A] ↥(modularFunctionFieldC (ResidueField ↥A) M))
    (hw1 : w ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) M⟩ =
        ⟨jqNModC (ResidueField ↥A) M, jqNModC_mem (ResidueField ↥A) M⟩)
    (hw2 : w ⟨jqNModC (ResidueField ↥A) M, jqNModC_mem (ResidueField ↥A) M⟩ =
        ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) M⟩)
    [IsCurveOver (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)]
    (x : JZero M) (hxp : (p : ℤ) • x = 0)
    (y y_p : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)
    (hy : (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) =
      (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm
        (reductionModL A M x))
    (hy_p : (y_p : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) =
      (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm
        (reductionModL A M (letI := heckeModuleBar M; heckeGen ⟨p, Fact.out⟩ • x))) :
    qExpansionDiffAlong (modularFunctionFieldC (ResidueField ↥A) M).val (Differential.pullbackAlong w.toAlgHom (δ y_p)) =
      Fam.T ⟨p, Fact.out⟩ (qExpansionDiffAlong (modularFunctionFieldC (ResidueField ↥A) M).val
        (Differential.pullbackAlong w.toAlgHom (δ y))) := by
  haveI : PerfectField (ResidueField ↥A) := IsAlgClosed.perfectField _
  haveI := ModularCurve.finiteDimensional_adjoin_jqModC (N := M) A

  obtain ⟨C, hsemi, hker, hlog⟩ := (cartierOperator_existsUnique (K := ResidueField ↥A)
    (F := modularFunctionFieldC (ResidueField ↥A) M) p
    (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) M⟩ : modularFunctionFieldC (ResidueField ↥A) M)).exists

  have hb2 := E3TParts.qExpansionDiffAlong_delta_eq_heckeU_of_coe_eq_reduction_heckeGen_self M hcomm p hpM A hA hE
    C hsemi hker hlog δ hδ x hxp y y_p hy hy_p

  obtain ⟨S, hSD, hSs⟩ := E3TParts.exists_semilinearDiffMap
    (coeffSemilinearAut M (frobeniusEquiv (ResidueField ↥A) p))
  have F1 : ∀ ω, qExpansionDiffAlong (modularFunctionFieldC (ResidueField ↥A) M).val (S ω) =
      coeffMap ((frobeniusEquiv (ResidueField ↥A) p : (ResidueField ↥A) ≃+* (ResidueField ↥A)) :
        (ResidueField ↥A) →+* (ResidueField ↥A))
        (qExpansionDiffAlong (modularFunctionFieldC (ResidueField ↥A) M).val ω) :=
    fun ω => E3TParts.qExpansionDiffAlong_semilinearDiffMap_eq_coeffMap (ResidueField ↥A) M
      (frobeniusEquiv (ResidueField ↥A) p) S hSD hSs (isQExpansionDiffAlong_qExpansionDiffAlong _) ω

  have F2 : ∀ η, C η = η →
      LaurentSeries.heckeU (ResidueField ↥A) p (Fact.out : p.Prime).pos
        (qExpansionDiffAlong (modularFunctionFieldC (ResidueField ↥A) M).val η) =
      coeffMap ((frobeniusEquiv (ResidueField ↥A) p : (ResidueField ↥A) ≃+* (ResidueField ↥A)) :
        (ResidueField ↥A) →+* (ResidueField ↥A))
        (qExpansionDiffAlong (modularFunctionFieldC (ResidueField ↥A) M).val η) := by
    intro η hη
    have h := qExpansionDiffAlong_cartier_eq_coeffMap_frobeniusEquiv_symm_heckeU (ResidueField ↥A) p M C hsemi hker hlog η
    rw [hη] at h
    have h2 := congrArg (coeffMap ((frobeniusEquiv (ResidueField ↥A) p : (ResidueField ↥A) ≃+* (ResidueField ↥A)) :
        (ResidueField ↥A) →+* (ResidueField ↥A))) h
    have hcancel : ((frobeniusEquiv (ResidueField ↥A) p : (ResidueField ↥A) ≃+* (ResidueField ↥A)) :
          (ResidueField ↥A) →+* (ResidueField ↥A)).comp
        (frobeniusEquiv (ResidueField ↥A) p).symm.toRingHom = RingHom.id _ := by
      ext a; simp
    rw [coeffMap_coeffMap, hcancel, coeffMap_id] at h2
    exact h2.symm

  have F3 : C (δ y) = δ y := E3TTwistP.cartier_delta_eq p C hsemi hlog δ hδ y
  have F3w : C (Differential.pullbackAlong w.toAlgHom (δ y)) = Differential.pullbackAlong w.toAlgHom (δ y) := by
    have := GlueE6W.cartier_pullbackAlong (K := ResidueField ↥A) (F := modularFunctionFieldC (ResidueField ↥A) M) p
      (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) M⟩ : modularFunctionFieldC (ResidueField ↥A) M)
      C hsemi hker hlog w (δ y)
    rw [F3] at this
    exact this

  have F4 : ∀ ω, S (Differential.pullbackAlong w.toAlgHom ω) = Differential.pullbackAlong w.toAlgHom (S ω) := by
    intro ω
    have h := E3TParts.semilinearDiffMap_comp_pullbackAlong_eq (coeffSemilinearAut M (frobeniusEquiv (ResidueField ↥A) p))
      S hSD hSs w (E3TTwistP.algEquiv_smul_comm (ResidueField ↥A) M (frobeniusEquiv (ResidueField ↥A) p) w hw1 hw2)
    exact DFunLike.congr_fun h ω

  have hM0 : (M : (ResidueField ↥A)) ≠ 0 := fun h => hpM ((CharP.cast_eq_zero_iff (ResidueField ↥A) p M).mp h)
  have hinj := qExpansionDiffAlong_modularFunctionFieldC_injective_of_thetaL_ne_zero_of_natCast_ne_zero
    (ResidueField ↥A) M hM0 (modularFunctionFieldC (ResidueField ↥A) M).val
    (E3TTwistP.thetaL_jqModC_ne_zero (ResidueField ↥A))
  have hδp : δ y_p = S (δ y) := hinj (hb2.trans ((F2 _ F3).trans (F1 _).symm))

  rw [hFamT ⟨p, Fact.out⟩ hpM,
    E3TParts.heckeT_eq_heckeU_of_natCast_eq_zero (ResidueField ↥A) p (Fact.out : p.Prime).pos 2 le_rfl
      (CharP.cast_eq_zero (ResidueField ↥A) p), hδp, ← F4, F1]
  exact (F2 _ F3w).symm

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem E3T_twist_ne
    (M : ℕ) [NeZero M] (hcomm : HeckeOperatorsCommuteBar M) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (hE : modularFunctionFieldC (ResidueField ↥A) M = modularFunctionFieldFullC (ResidueField ↥A) M)
    (δ : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p →+
      Ω[↥(modularFunctionFieldC (ResidueField ↥A) M)⁄(ResidueField ↥A)])
    (hδ : ∀ (y : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)
        (E : Divisor.degZero (K := ResidueField ↥A) (F := modularFunctionFieldC (ResidueField ↥A) M))
        (g : modularFunctionFieldC (ResidueField ↥A) M),
        Pic0.mk E = (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) → g ≠ 0 →
        (∀ v : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M),
          (p : ℤ) * (E : Divisor (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) g)
    (Fam : Module.End.CommFamily (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) Nat.Primes)
    (hFamT : ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M →
      Fam.T ℓ = LaurentSeries.heckeT (ResidueField ↥A) (ℓ : ℕ) ℓ.2.pos 2)
    (hFamU : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ M →
      Fam.T ℓ = LaurentSeries.heckeU (ResidueField ↥A) (ℓ : ℕ) ℓ.2.pos)
    (w : ↥(modularFunctionFieldC (ResidueField ↥A) M) ≃ₐ[ResidueField ↥A] ↥(modularFunctionFieldC (ResidueField ↥A) M))
    (hw1 : w ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) M⟩ =
        ⟨jqNModC (ResidueField ↥A) M, jqNModC_mem (ResidueField ↥A) M⟩)
    (hw2 : w ⟨jqNModC (ResidueField ↥A) M, jqNModC_mem (ResidueField ↥A) M⟩ =
        ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) M⟩)
    (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    (x : JZero M) (y y' : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)
    (hy : (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) =
      (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm
        (reductionModL A M x))
    (hy' : (y' : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) =
      (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm
        (reductionModL A M (letI := heckeModuleBar M; heckeGen ⟨q, Fact.out⟩ • x))) :
    qExpansionDiffAlong (modularFunctionFieldC (ResidueField ↥A) M).val (Differential.pullbackAlong w.toAlgHom (δ y')) =
      Fam.T ⟨q, Fact.out⟩ (qExpansionDiffAlong (modularFunctionFieldC (ResidueField ↥A) M).val
        (Differential.pullbackAlong w.toAlgHom (δ y))) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  have ha1 : δ y' =
      Differential.traceAlong (heckeAlphaC (ResidueField ↥A) M q) (Differential.pullbackAlong (heckeBetaC (ResidueField ↥A) M q) (δ y)) :=
    E3TParts.delta_of_coe_eq_reduction_heckeGen M hcomm p hpM A hA hE δ hδ q hqp
      (E3TParts.heckeInputsFibre_of_ne (ResidueField ↥A) p M hpM q hqp) x y y' hy hy'
  rw [ha1]

  have hpMq : ¬ p ∣ M * q := fun h => by
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
    · exact hpM h
    · exact hqp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h).symm
  obtain ⟨hα, hβ⟩ := separableAlong_heckeAlphaC_heckeBetaC (ResidueField ↥A) (ℓ := p) M q hpMq

  obtain ⟨-, hW2, hW3⟩ := exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap (ResidueField ↥A) p M hpM q hqp
  obtain ⟨w', hw'α, hw'β⟩ := hW2 w hw1 hw2
  rw [Differential.pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap
    (heckeAlphaC (ResidueField ↥A) M q) (heckeBetaC (ResidueField ↥A) M q) hα hβ w w' hw'α hw'β]
  by_cases hqM : q ∣ M
  ·
    rw [hFamU ⟨q, Fact.out⟩ hqM]
    have hq0 : (q : (ResidueField ↥A)) ≠ 0 := fun h =>
      hqp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp ((CharP.cast_eq_zero_iff (ResidueField ↥A) p q).mp h)).symm
    haveI : NeZero (q : (ResidueField ↥A)) := ⟨hq0⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := (ResidueField ↥A)) (n := q)
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (Fact.out : q.Prime).ne_zero
    have hM0 : (M : (ResidueField ↥A)) ≠ 0 := fun h => hpM ((CharP.cast_eq_zero_iff (ResidueField ↥A) p M).mp h)
    ext n
    rw [LaurentSeries.coeff_heckeU, Differential.traceAlong_eq_traceDiff _ _ _ _ hβ]
    exact coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd (ResidueField ↥A) M q hM0 hqM (Units.mk0 ζ hζ0)
      (by simpa using hζ) _ n
  ·
    obtain ⟨w'', hw''α, hw''β⟩ := hW3 hqM
    have hsym := Differential.pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap
      (heckeAlphaC (ResidueField ↥A) M q) (heckeBetaC (ResidueField ↥A) M q) hα hβ AlgEquiv.refl w'' (fun x => hw''α x) (fun x => hw''β x)
      (Differential.pullbackAlong w.toAlgHom (δ y))
    rw [show (AlgEquiv.refl : ↥(modularFunctionFieldC (ResidueField ↥A) M) ≃ₐ[(ResidueField ↥A)] ↥(modularFunctionFieldC (ResidueField ↥A) M)).toAlgHom =
        AlgHom.id (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M) from rfl,
      GlueE6W.pullbackAlong_id, GlueE6W.pullbackAlong_id] at hsym
    rw [← hsym, hFamT ⟨q, Fact.out⟩ hqM]
    exact E3TParts.qExpansionDiffAlong_traceAlong_pullbackAlong_eq_heckeT_of_ne (ResidueField ↥A) p M q hpM hqp hqM _

end Twist
p2m_reactivate "P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts.TwistedDiff P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL.E3TParts"

open ModularCurve AlgebraicCurve IsLocalRing in
set_option maxHeartbeats 32000000 in
theorem solution
    (M : ℕ) [NeZero M] (hcomm : HeckeOperatorsCommuteBar M) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    [IsCurveOver (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)]
    [Algebra.EssFiniteType (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)]
    [∀ w : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M), w.DCoordGenerates]
    [CharP (modularFunctionFieldC (ResidueField ↥A) M) p]
    (hE : modularFunctionFieldC (ResidueField ↥A) M = modularFunctionFieldFullC (ResidueField ↥A) M)
    [Module (ZMod p) ↥(Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)]
    (δ : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p →+
      Ω[↥(modularFunctionFieldC (ResidueField ↥A) M)⁄(ResidueField ↥A)])
    (hδ : ∀ (y : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)
        (E : Divisor.degZero (K := ResidueField ↥A) (F := modularFunctionFieldC (ResidueField ↥A) M))
        (g : modularFunctionFieldC (ResidueField ↥A) M),
        Pic0.mk E = (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) → g ≠ 0 →
        (∀ v : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M),
          (p : ℤ) * (E : Divisor (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) g)
    (Fam : Module.End.CommFamily (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) Nat.Primes)
    (hFamT : ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M →
      Fam.T ℓ = LaurentSeries.heckeT (ResidueField ↥A) (ℓ : ℕ) ℓ.2.pos 2)
    (hFamU : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ M →
      Fam.T ℓ = LaurentSeries.heckeU (ResidueField ↥A) (ℓ : ℕ) ℓ.2.pos)
    (e : HeckeAlg ⧸ 𝔪 →+* ResidueField ↥A)
    (w : ↥(modularFunctionFieldC (ResidueField ↥A) M) ≃ₐ[ResidueField ↥A] ↥(modularFunctionFieldC (ResidueField ↥A) M))
    (hw : w ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) M⟩ =
        ⟨jqNModC (ResidueField ↥A) M, jqNModC_mem (ResidueField ↥A) M⟩ ∧
      w ⟨jqNModC (ResidueField ↥A) M, jqNModC_mem (ResidueField ↥A) M⟩ =
        ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) M⟩)
    (x : JZero M) (hx : letI := heckeModuleBar M; x ∈ heckeTorsion (JZero M) 𝔪)
    (y : Pic0.torsion (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M) p)
    (hy : (y : Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M)) =
      (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
        (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (reductionModL A M x)) :
    Differential.pullbackAlong w.toAlgHom (δ y) ∈ mTorsionDiffOf (ResidueField ↥A) p M Fam
      (fun ℓ : Nat.Primes => e (Ideal.Quotient.mk 𝔪 (heckeGen ℓ))) := by
  obtain ⟨hw1, hw2⟩ := hw

  letI := heckeModuleBar M
  set κ := ResidueField ↥A
  set θ : Nat.Primes → κ := fun ℓ : Nat.Primes => e (Ideal.Quotient.mk 𝔪 (heckeGen ℓ)) with hθ
  rw [mem_mTorsionDiffOf_iff]

  haveI : PerfectField (ResidueField ↥A) := IsAlgClosed.perfectField _
  have hR : Differential.pullbackAlong w.toAlgHom (δ y) ∈ regularDifferentials κ (modularFunctionFieldC κ M) :=
    pullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver w
      (apply_mem_regularDifferentials_of_recipe κ p M δ hδ y)

  let door := E3TDoor.doorMap M p 𝔪 hp𝔪 A hE
  let Φ : ↥(heckeTorsion (JZero M) 𝔪) →+ LaurentSeries κ :=
    ((qExpansionDiffAlong (modularFunctionFieldC κ M).val).toAddMonoidHom.comp
      (Differential.pullbackAlong w.toAlgHom).toAddMonoidHom).comp (δ.comp door)
  have hΦdef : ∀ z, Φ z = qExpansionDiffAlong (modularFunctionFieldC κ M).val
      (Differential.pullbackAlong w.toAlgHom (δ (door z))) := fun z => rfl
  have hyd : y = door ⟨x, hx⟩ := Subtype.ext hy

  have hΦ : ∀ (ℓ : Nat.Primes) (z : ↥(heckeTorsion (JZero M) 𝔪)), Φ (heckeGen ℓ • z) = Fam.T ℓ (Φ z) := by
    intro ℓ z
    obtain ⟨l, hl⟩ := ℓ
    haveI : Fact l.Prime := ⟨hl⟩
    rw [hΦdef, hΦdef]
    by_cases hlp : l = p
    · have e : (⟨l, hl⟩ : Nat.Primes) = ⟨p, Fact.out⟩ := Subtype.ext hlp
      rw [e]
      exact E3T_twist_self M hcomm p hpM 𝔪 hp𝔪 A hA hE δ hδ Fam hFamT hFamU w hw1 hw2 (z : JZero M)
        (E3TParts.zsmul_eq_zero_of_mem_heckeTorsion M p 𝔪 hp𝔪 (z : JZero M) z.2)
        (door z) (door (heckeGen ⟨p, Fact.out⟩ • z))
        (E3TDoor.coe_doorMap_apply M p 𝔪 hp𝔪 A hE z) (E3TDoor.coe_doorMap_apply M p 𝔪 hp𝔪 A hE _)
    · exact E3T_twist_ne M hcomm p hpM 𝔪 hp𝔪 A hA hE δ hδ Fam hFamT hFamU w hw1 hw2 l hlp (z : JZero M)
        (door z) (door (heckeGen ⟨l, hl⟩ • z))
        (E3TDoor.coe_doorMap_apply M p 𝔪 hp𝔪 A hE z) (E3TDoor.coe_doorMap_apply M p 𝔪 hp𝔪 A hE _)
  have hA := E3TParts.apply_mem_annPart_of_forall_apply_heckeGen_smul M p (heckeTorsion (JZero M) 𝔪) Fam Φ hΦ 𝔪 e
    ⟨x, hx⟩ hx
  rw [Module.End.CommFamily.mem_annPart_iff] at hA
  refine ⟨hR, fun Q hQ => ?_⟩
  rw [hyd, ← hΦdef]
  exact hA Q hQ

end S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL
end P2MW
export P2MW.S_ModularCurve_pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL (solution)
