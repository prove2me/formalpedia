-- Prove2me | solution 1 for ModPForms.res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e91ab41c-fa7c-59f0-980e-9bba316f45de

import Definitions.Def_ModularCurve_SSCarrier3
import Definitions.Def_CuspForm_ModPForms
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_heckeAlphaCIntegral_unconditional
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_ModularCurve_ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
import Theorems.Thm_ModPForms_modPMod_le_modPMod_of_dvd
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.LinearCombination
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModPForms_mem_modPMod_of_coe_mul_thetaJ_pow_eq_of_forall_ord_pos_of_exists_prime_dvd_mod_three_eq_two
import Theorems.Thm_ModPForms_finiteDimensional_modPMod
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModPForms_finrank_modPMod_two_le_genusFormula_add_cuspCount_sub_one
import Theorems.Thm_ModPForms_one_mem_modPMod_two_of_exists_prime_dvd_mod_three_eq_two
import Theorems.Thm_ModularCurve_sum_ord_jGeomGen_sub_eq_dedekindPsi
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModPForms_mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut"
set_option autoImplicit false

section LegE4

open AlgebraicCurve ModularCurve

private theorem k1le_thetaJ3_coeff_pow_three (K : Type) [Field K] [CharP K 3] (g : PowerSeries K) {n : ℕ}
    (hn : ¬ 3 ∣ n) : PowerSeries.coeff n (g ^ 3) = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : PowerSeries.coeff n (g ^ 3) = (PowerSeries.trunc (n + 1) (g ^ 3)).coeff n := by
    rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_self n)]
  have h2 : (PowerSeries.trunc (n + 1) g) ^ 3
      = Polynomial.map (frobenius K 3) (Polynomial.expand K 3 (PowerSeries.trunc (n + 1) g)) :=
    (Polynomial.map_frobenius_expand (p := 3) (PowerSeries.trunc (n + 1) g)).symm
  rw [h1, ← PowerSeries.trunc_trunc_pow, ← Polynomial.coe_pow, h2]
  simp [PowerSeries.coeff_trunc, Polynomial.coeff_coe, Polynomial.coeff_expand, hn]

private theorem k1le_thetaJ3_jNum_eq_pow_three :
    ModularCurve.jNum
      = (ModularCurve.eisenstein4 * ModularCurve.etaProd ^ 16 * ModularCurve.dedekindEtaUnitInv) ^ 3 := by
  have h := ModularCurve.dedekindEtaUnit_mul_inv
  unfold ModularCurve.dedekindEtaUnit at h
  unfold ModularCurve.jNum
  linear_combination (-(ModularCurve.eisenstein4 ^ 3 * ModularCurve.dedekindEtaUnitInv
    * (1 + ModularCurve.etaProd ^ 24 * ModularCurve.dedekindEtaUnitInv))) * h

private theorem k1le_thetaJ3_coeff_jqModC (K : Type) [Field K] [CharP K 3] {n : ℤ} (hn : ¬ (3 : ℤ) ∣ n + 1) :
    (ModularCurve.jqModC K).coeff n = 0 := by
  unfold ModularCurve.jqModC
  rw [HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add]
  by_cases h : n + 1 < 0
  · exact ModularCurve.ofPowerSeries_coeff_of_neg _ h
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp h)
    rw [hm, HahnSeries.ofPowerSeries_apply_coeff, k1le_thetaJ3_jNum_eq_pow_three, map_pow]
    apply k1le_thetaJ3_coeff_pow_three
    intro hdvd
    apply hn
    rw [hm]
    exact_mod_cast hdvd

private theorem k1le_thetaJ3_coeff_thetaL (K : Type) [Field K] (f : LaurentSeries K) (n : ℤ) :
    (ModularCurve.thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [ModularCurve.thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp [zsmul_eq_mul]

private theorem k1le_thetaL_jqModC_eq_neg (K : Type) [Field K] [CharP K 3] :
    ModularCurve.thetaL K (ModularCurve.jqModC K) = -ModularCurve.jqModC K := by
  ext n
  rw [k1le_thetaJ3_coeff_thetaL, HahnSeries.coeff_neg]
  by_cases h : (3 : ℤ) ∣ n + 1
  · obtain ⟨c, hc⟩ := h
    have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
    have hn : (n : K) = -1 := by
      have hn' : n = 3 * c - 1 := by omega
      rw [hn']
      push_cast
      rw [h3]
      ring
    rw [hn, neg_one_mul]
  · rw [k1le_thetaJ3_coeff_jqModC K h, mul_zero, neg_zero]

private theorem k1le_char (F : Type) [Field F] [CharP F 3] : (1728 : F) = 0 := by
  have h : ((1728 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 3 1728).mpr (by norm_num)
  exact_mod_cast h

private noncomputable def k1le_adjoinEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : E) :
    Algebra.adjoin K ({t} : Set E) ≃ₐ[K] Algebra.adjoin K ({(t : L)} : Set L) :=
  (Subalgebra.equivMapOfInjective (Algebra.adjoin K ({t} : Set E)) E.val Subtype.val_injective).trans
    (Subalgebra.equivOfEq _ _ (by rw [AlgHom.map_adjoin, Set.image_singleton]; rfl))

private theorem k1le_coe_adjoinEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : E) (a : Algebra.adjoin K ({t} : Set E)) :
    ((k1le_adjoinEquiv E t a : Algebra.adjoin K ({(t : L)} : Set L)) : L) = ((a : E) : L) :=
  rfl

private theorem k1le_isIntegral_of_coe {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t u : E)
    (hu : IsIntegral (Algebra.adjoin K ({(t : L)} : Set L)) (u : L)) :
    IsIntegral (Algebra.adjoin K ({t} : Set E)) u := by
  have h1 : IsIntegral (Algebra.adjoin K ({t} : Set E)) (u : L) := by
    refine IsIntegral.map_of_comp_eq (k1le_adjoinEquiv E t).symm.toAlgHom.toRingHom (RingHom.id L) ?_ hu
    refine RingHom.ext fun b => ?_
    have hb := k1le_coe_adjoinEquiv E t ((k1le_adjoinEquiv E t).symm b)
    rw [AlgEquiv.apply_symm_apply] at hb
    exact hb.symm
  haveI : IsScalarTower (Algebra.adjoin K ({t} : Set E)) E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (Algebra.adjoin K ({t} : Set E)) E L)
    (algebraMap E L).injective).mp h1

private theorem k1le_ord_pow {K E : Type*} [Field K] [Field E] [Algebra K E] (x : AlgebraicCurve.Place K E)
    {a : E} (ha : a ≠ 0) (i : ℕ) : x.ord (a ^ i) = (i : ℤ) * x.ord a := by
  have _ := ha
  rw [← zpow_natCast, x.ord_zpow]

private theorem k1le_thetaJ_ne_zero (F : Type) [Field F] [CharP F 3] : ModularCurve.thetaJ F ≠ 0 := by
  have hθ : ModularCurve.thetaJ F = -ModularCurve.jqModC F := k1le_thetaL_jqModC_eq_neg F
  rw [hθ, neg_ne_zero]
  exact ModularCurve.jqModC_ne_zero_def F

private theorem k1le_ord_bound (N' : ℕ) [NeZero N'] (F : Type) [Field F] [CharP F 3] (m : ℕ)
    (G : ↥(ModularCurve.modularFunctionFieldC F N')) (hG0 : G ≠ 0)
    (hfn : ModularCurve.IsModPFormFn F m (G : LaurentSeries F))
    (x : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N'))
    (hx : 0 < x.ord (ModularCurve.jGeomGen F N')) :
    0 ≤ 6 * x.ord G + 7 * (m : ℤ) * x.ord (ModularCurve.jGeomGen F N') := by
  have hjne : ModularCurve.jqModC F ≠ 0 := ModularCurve.jqModC_ne_zero_def F
  have hj0 : ModularCurve.jGeomGen F N' ≠ 0 := by
    intro h
    apply hjne
    have h' := congrArg (fun y : ↥(ModularCurve.modularFunctionFieldC F N') => (y : LaurentSeries F)) h
    simpa using h'
  have h1728 : algebraMap F (LaurentSeries F) (1728 : F) = 0 := by rw [k1le_char F, map_zero]
  unfold ModularCurve.IsModPFormFn at hfn
  obtain ⟨h1, -⟩ := hfn
  simp only [h1728, sub_zero] at h1
  have hY : IsIntegral
      (Algebra.adjoin F ({ModularCurve.jGeomGen F N'} : Set ↥(ModularCurve.modularFunctionFieldC F N')))
      (G ^ 6 * ModularCurve.jGeomGen F N' ^ (4 * m) * ModularCurve.jGeomGen F N' ^ (3 * m)) := by
    apply k1le_isIntegral_of_coe
    push_cast
    exact h1
  have hYord := x.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg hY hx.le
  rw [x.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj0),
    x.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), k1le_ord_pow x hG0, k1le_ord_pow x hj0, k1le_ord_pow x hj0]
    at hYord
  push_cast at hYord
  linarith

private theorem k1le_residue_eq_zero {K E : Type*} [Field K] [Field E] [Algebra K E] (x : AlgebraicCurve.Place K E)
    (f : E) (hf : 1 ≤ x.ord f) (hmem : f ∈ x.toValuationSubring) :
    IsLocalRing.residue x.toValuationSubring ⟨f, hmem⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hv : x.adicValuation f = 1 := (x.adicValuation_coe_eq_one_iff ⟨f, hmem⟩).2 hu
  have h0 : x.ord f = 0 := by simp [AlgebraicCurve.Place.ord, hv]
  omega

private theorem k1le_ord_uniformizer (N' : ℕ) [NeZero N'] (F : Type) [Field F] (x : ModularCurve.ssPlaces3 F N') :
    x.1.ord (ModularCurve.SSCarrier3.uniformizer x) = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.1.toValuationSubring
  unfold ModularCurve.SSCarrier3.uniformizer
  exact Classical.epsilon_spec
    (⟨(π : ↥(ModularCurve.modularFunctionFieldC F N')), x.1.ord_coe_irreducible hπ⟩ :
      ∃ ϖ : ↥(ModularCurve.modularFunctionFieldC F N'), x.1.ord ϖ = 1)

private theorem e4_ord_neg {K E : Type*} [Field K] [Field E] [Algebra K E] (x : AlgebraicCurve.Place K E) (f : E) :
    x.ord (-f) = x.ord f := by
  simp only [AlgebraicCurve.Place.ord, Valuation.map_neg]

private theorem e4_exists_mem_and_residue_ne_zero {K E : Type*} [Field K] [Field E] [Algebra K E]
    (x : AlgebraicCurve.Place K E) {f : E} (hf : f ≠ 0) (h0 : x.ord f = 0) :
    ∃ hmem : f ∈ x.toValuationSubring, IsLocalRing.residue x.toValuationSubring ⟨f, hmem⟩ ≠ 0 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
  obtain ⟨u, hu⟩ := x.exists_unit_mul_zpow hf hπ
  rw [h0, zpow_zero, mul_one] at hu
  have hmem : f ∈ x.toValuationSubring := by
    rw [hu]
    exact (u : x.toValuationSubring).2
  refine ⟨hmem, ?_⟩
  have hfu : (⟨f, hmem⟩ : x.toValuationSubring) = (u : x.toValuationSubring) := Subtype.ext hu
  rw [hfu, Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  exact u.isUnit

private theorem e4_ord_eq_zero_of_residue_ne_zero {K E : Type*} [Field K] [Field E] [Algebra K E]
    (x : AlgebraicCurve.Place K E) {f : E} (hmem : f ∈ x.toValuationSubring)
    (hres : IsLocalRing.residue x.toValuationSubring ⟨f, hmem⟩ ≠ 0) : x.ord f = 0 := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hres
  have hv : x.adicValuation f = 1 := (x.adicValuation_coe_eq_one_iff ⟨f, hmem⟩).2 hres
  simp [AlgebraicCurve.Place.ord, hv]

private theorem e4_neg_coe_jGeomGen (L : ℕ) [NeZero L] (F : Type) [Field F] [CharP F 3] :
    -((ModularCurve.jGeomGen F L : ↥(ModularCurve.modularFunctionFieldC F L)) : LaurentSeries F) =
      ModularCurve.thetaJ F := by
  have hθ : ModularCurve.thetaJ F = -ModularCurve.jqModC F := k1le_thetaL_jqModC_eq_neg F
  rw [hθ]
  simp

private theorem e4_witness_eq (L : ℕ) [NeZero L] (F : Type) [Field F] [CharP F 3]
    (φ : PowerSeries F) (G : ↥(ModularCurve.modularFunctionFieldC F L))
    (hG : (G : LaurentSeries F) * ModularCurve.thetaJ F ^ 2 = HahnSeries.ofPowerSeries ℤ F φ)
    (H : ↥(ModularCurve.modularFunctionFieldC F L))
    (hH : (H : LaurentSeries F) * ModularCurve.thetaJ F ^ 1 = HahnSeries.ofPowerSeries ℤ F φ) :
    H = G * (-ModularCurve.jGeomGen F L) := by
  apply Subtype.ext
  have hθ0 : ModularCurve.thetaJ F ^ 1 ≠ 0 := pow_ne_zero 1 (k1le_thetaJ_ne_zero F)
  apply mul_right_cancel₀ hθ0
  rw [hH]
  push_cast
  rw [e4_neg_coe_jGeomGen, pow_one, mul_assoc, ← pow_two, hG]

open Classical in

private theorem e4_res_core (L : ℕ) [NeZero L] (h3 : ¬ 3 ∣ L)
    (hε : ∃ p : ℕ, p.Prime ∧ p ∣ L ∧ p % 3 = 2) (F : Type) [Field F] [CharP F 3] [IsAlgClosed F]
    (φ : PowerSeries F) (G : ↥(ModularCurve.modularFunctionFieldC F L))
    (hG : (G : LaurentSeries F) * ModularCurve.thetaJ F ^ 2 = HahnSeries.ofPowerSeries ℤ F φ)
    (x : ModularCurve.ssPlaces3 F L) (H : ↥(ModularCurve.modularFunctionFieldC F L))
    (hH : (H : LaurentSeries F) * ModularCurve.thetaJ F ^ 1 = HahnSeries.ofPowerSeries ℤ F φ) :
    (if hm : H * ModularCurve.SSCarrier3.uniformizer x ^ (ModularCurve.SSCarrier3.aPole 1 x).toNat ∈
        x.1.toValuationSubring then
      IsLocalRing.residue x.1.toValuationSubring ⟨_, hm⟩ else 0) ≠ 0 ↔
      G ≠ 0 ∧ 3 * x.1.ord G + 7 * x.1.ord (ModularCurve.jGeomGen F L) = 0 := by
  have hHG : H = G * (-ModularCurve.jGeomGen F L) := e4_witness_eq L F φ G hG H hH
  subst hHG

  have hj : 0 < x.1.ord (ModularCurve.jGeomGen F L) := x.2
  have hj0 : ModularCurve.jGeomGen F L ≠ 0 := by
    intro h
    have h' : x.1.ord (ModularCurve.jGeomGen F L) = x.1.ord 0 := congrArg x.1.ord h
    rw [x.1.ord_zero] at h'
    omega
  have hπ1 := k1le_ord_uniformizer L F x
  have hπ0 : ModularCurve.SSCarrier3.uniformizer x ≠ 0 := by
    intro h0
    rw [h0, x.1.ord_zero] at hπ1
    exact zero_ne_one hπ1
  have hor := ModularCurve.ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
    L h3 hε F x.1 hj
  have haPole : (((ModularCurve.SSCarrier3.aPole 1 x).toNat : ℕ) : ℤ) = ModularCurve.SSCarrier3.aPole 1 x := by
    apply Int.toNat_of_nonneg
    unfold ModularCurve.SSCarrier3.aPole
    omega
  by_cases hG0 : G = 0
  ·
    subst hG0
    simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_not]
    split_ifs with hm
    · have h0 : (⟨_, hm⟩ : x.1.toValuationSubring) = 0 := Subtype.ext (by simp)
      rw [h0, map_zero]
    · rfl
  · have hG'0 : G * (-ModularCurve.jGeomGen F L) ≠ 0 := mul_ne_zero hG0 (neg_ne_zero.mpr hj0)
    have hf0 : G * (-ModularCurve.jGeomGen F L) *
        ModularCurve.SSCarrier3.uniformizer x ^ (ModularCurve.SSCarrier3.aPole 1 x).toNat ≠ 0 :=
      mul_ne_zero hG'0 (pow_ne_zero _ hπ0)
    have hordf : x.1.ord (G * (-ModularCurve.jGeomGen F L) *
        ModularCurve.SSCarrier3.uniformizer x ^ (ModularCurve.SSCarrier3.aPole 1 x).toNat) =
        x.1.ord G + x.1.ord (ModularCurve.jGeomGen F L) + ModularCurve.SSCarrier3.aPole 1 x := by
      rw [x.1.ord_mul hG'0 (pow_ne_zero _ hπ0), k1le_ord_pow x.1 hπ0, hπ1, mul_one, haPole,
        x.1.ord_mul hG0 (neg_ne_zero.mpr hj0), e4_ord_neg]
    have hkey : x.1.ord (G * (-ModularCurve.jGeomGen F L) *
        ModularCurve.SSCarrier3.uniformizer x ^ (ModularCurve.SSCarrier3.aPole 1 x).toNat) = 0 ↔
        3 * x.1.ord G + 7 * x.1.ord (ModularCurve.jGeomGen F L) = 0 := by
      rw [hordf]
      unfold ModularCurve.SSCarrier3.aPole
      push_cast
      rcases hor with h | h <;> rw [h] <;> omega
    rw [← hkey]
    simp only [ne_eq, hG0, not_false_eq_true, true_and]
    constructor
    · intro hne
      split_ifs at hne with hm
      · exact e4_ord_eq_zero_of_residue_ne_zero x.1 hm hne
      · exact absurd rfl hne
    · intro h0
      obtain ⟨hmem, hne⟩ := e4_exists_mem_and_residue_ne_zero x.1 hf0 h0
      rw [dif_pos hmem]
      exact hne

private theorem e4_res_one_ne_zero_iff (L : ℕ) [NeZero L] (h3 : ¬ 3 ∣ L)
    (hε : ∃ p : ℕ, p.Prime ∧ p ∣ L ∧ p % 3 = 2) (F : Type) [Field F] [CharP F 3] [IsAlgClosed F]
    (φ : PowerSeries F) (G : ↥(ModularCurve.modularFunctionFieldC F L))
    (hG : (G : LaurentSeries F) * ModularCurve.thetaJ F ^ 2 = HahnSeries.ofPowerSeries ℤ F φ)
    (x : ModularCurve.ssPlaces3 F L) :
    ModularCurve.SSCarrier3.res 1 φ x ≠ 0 ↔
      G ≠ 0 ∧ 3 * x.1.ord G + 7 * x.1.ord (ModularCurve.jGeomGen F L) = 0 := by
  have hwit : ∃ H : ↥(ModularCurve.modularFunctionFieldC F L),
      (H : LaurentSeries F) * ModularCurve.thetaJ F ^ 1 = HahnSeries.ofPowerSeries ℤ F φ :=
    ⟨G * (-ModularCurve.jGeomGen F L), by
      push_cast
      rw [e4_neg_coe_jGeomGen, pow_one, mul_assoc, ← pow_two, hG]⟩
  unfold ModularCurve.SSCarrier3.res
  rw [dif_pos hwit]
  exact e4_res_core L h3 hε F φ G hG x (Classical.choose hwit) (Classical.choose_spec hwit)

private theorem e4_ramificationIndexAlong_eq_one {K A B : Type*} [Field K] [Field A] [Field B] [Algebra K A]
    [Algebra K B] (ψ : A →ₐ[K] B) (hψ : Function.Surjective ψ) (v : AlgebraicCurve.Place K B) :
    AlgebraicCurve.Place.ramificationIndexAlong ψ v = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have h1 : v.ord (π : B) = 1 := v.ord_coe_irreducible hπ
  obtain ⟨g, hg⟩ := hψ π
  have h2 := AlgebraicCurve.Place.ord_restrictAlong ψ (RingHom.isIntegral_of_surjective _ hψ) v g
  rw [hg, h1] at h2
  exact_mod_cast Int.eq_one_of_mul_eq_one_right (Int.natCast_nonneg _) h2.symm

private theorem e4_ord_apply_of_surjective {K A B : Type*} [Field K] [Field A] [Field B] [Algebra K A]
    [Algebra K B] (ψ : A →ₐ[K] B) (hψ : Function.Surjective ψ) (v : AlgebraicCurve.Place K B) (a : A) :
    v.ord (ψ a) = (v.restrictAlong ψ (RingHom.isIntegral_of_surjective _ hψ)).ord a := by
  rw [AlgebraicCurve.Place.ord_restrictAlong ψ (RingHom.isIntegral_of_surjective _ hψ),
    e4_ramificationIndexAlong_eq_one ψ hψ]
  simp

private theorem fullC_eq_C (k : Type*) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (n : ℕ) [NeZero n] (hℓn : ¬ ℓ ∣ n) :
    modularFunctionFieldFullC k n = modularFunctionFieldC k n := by

  have hF1 : modularFunctionFieldFullC k 1 =
      IntermediateField.adjoin k {(jqModC k : LaurentSeries k)} := by
    apply le_antisymm
    · rw [modularFunctionFieldFullC, IntermediateField.adjoin_le_iff]
      rintro x ⟨d, _, hd, rfl⟩
      obtain rfl : d = 1 := Nat.dvd_one.mp hd
      rw [qExpand_one_apply]
      exact IntermediateField.subset_adjoin k _ (Set.mem_singleton _)
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact jqModC_mem_full k 1

  have hFn : ∀ {m m' : ℕ} [NeZero m] [NeZero m'], m = m' →
      modularFunctionFieldFullC k m = modularFunctionFieldFullC k m' := by
    intro m m' _ _ h
    subst h
    rfl
  have hcast : ((1 * n : ℕ) : k) ≠ 0 := by
    rw [one_mul]
    exact fun h => hℓn ((CharP.cast_eq_zero_iff k ℓ n).mp h)

  have hdeg := (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi k 1 n hcast).1
  rw [hFn (one_mul n), hF1, dedekindPsi_one, mul_one, one_mul] at hdeg

  have hC : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k n) = dedekindPsi n :=
    relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k n ℓ hℓn
  have hle : modularFunctionFieldC k n ≤ modularFunctionFieldFullC k n :=
    modularFunctionFieldC_le_full k n
  have hA0C : IntermediateField.adjoin k {(jqModC k : LaurentSeries k)} ≤
      modularFunctionFieldC k n := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact jqModC_mem k n

  have htower := IntermediateField.relfinrank_mul_relfinrank
    (A := IntermediateField.adjoin k {(jqModC k : LaurentSeries k)})
    (B := modularFunctionFieldC k n) (C := modularFunctionFieldFullC k n) hA0C hle
  rw [hC, hdeg] at htower
  have hψ : dedekindPsi n ≠ 0 := (dedekindPsi_pos n (NeZero.ne n)).ne'
  have h1 : (modularFunctionFieldC k n).relfinrank (modularFunctionFieldFullC k n) = 1 :=
    mul_left_cancel₀ hψ (htower.trans (mul_one _).symm)
  exact le_antisymm
    ((IntermediateField.relfinrank_eq_one_iff (A := modularFunctionFieldC k n)
      (B := modularFunctionFieldFullC k n)).mp h1) hle

private theorem e4_roof_eq (N q : ℕ) [NeZero N] [NeZero q] (h3 : ¬ 3 ∣ N * q) (F : Type) [Field F] [CharP F 3] :
    ModularCurve.charLDegeneracyRoof F N q = ModularCurve.modularFunctionFieldC F (N * q) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul F 3 N q h3]
  exact fullC_eq_C F 3 (N * q) h3

private noncomputable def e4_toNq (N q : ℕ) [NeZero N] [NeZero q] (h3 : ¬ 3 ∣ N * q) (F : Type) [Field F]
    [CharP F 3] :
    ↥(ModularCurve.charLDegeneracyRoof F N q) →ₐ[F] ↥(ModularCurve.modularFunctionFieldC F (N * q)) :=
  IntermediateField.inclusion (e4_roof_eq N q h3 F).le

private noncomputable def e4_ofNq (N q : ℕ) [NeZero N] [NeZero q] (h3 : ¬ 3 ∣ N * q) (F : Type) [Field F]
    [CharP F 3] :
    ↥(ModularCurve.modularFunctionFieldC F (N * q)) →ₐ[F] ↥(ModularCurve.charLDegeneracyRoof F N q) :=
  IntermediateField.inclusion (e4_roof_eq N q h3 F).ge

private theorem e4_coe_toNq (N q : ℕ) [NeZero N] [NeZero q] (h3 : ¬ 3 ∣ N * q) (F : Type) [Field F] [CharP F 3]
    (r : ↥(ModularCurve.charLDegeneracyRoof F N q)) :
    ((e4_toNq N q h3 F r : ↥(ModularCurve.modularFunctionFieldC F (N * q))) : LaurentSeries F) =
      (r : LaurentSeries F) :=
  IntermediateField.coe_inclusion (e4_roof_eq N q h3 F).le r

private theorem e4_coe_ofNq (N q : ℕ) [NeZero N] [NeZero q] (h3 : ¬ 3 ∣ N * q) (F : Type) [Field F] [CharP F 3]
    (y : ↥(ModularCurve.modularFunctionFieldC F (N * q))) :
    ((e4_ofNq N q h3 F y : ↥(ModularCurve.charLDegeneracyRoof F N q)) : LaurentSeries F) = (y : LaurentSeries F) :=
  IntermediateField.coe_inclusion (e4_roof_eq N q h3 F).ge y

private theorem e4_ofNq_toNq (N q : ℕ) [NeZero N] [NeZero q] (h3 : ¬ 3 ∣ N * q) (F : Type) [Field F] [CharP F 3]
    (r : ↥(ModularCurve.charLDegeneracyRoof F N q)) : e4_ofNq N q h3 F (e4_toNq N q h3 F r) = r := by
  apply Subtype.ext
  rw [e4_coe_ofNq, e4_coe_toNq]

private theorem e4_toNq_ofNq (N q : ℕ) [NeZero N] [NeZero q] (h3 : ¬ 3 ∣ N * q) (F : Type) [Field F] [CharP F 3]
    (y : ↥(ModularCurve.modularFunctionFieldC F (N * q))) : e4_toNq N q h3 F (e4_ofNq N q h3 F y) = y := by
  apply Subtype.ext
  rw [e4_coe_toNq, e4_coe_ofNq]

private theorem e4_toNq_surjective (N q : ℕ) [NeZero N] [NeZero q] (h3 : ¬ 3 ∣ N * q) (F : Type) [Field F]
    [CharP F 3] : Function.Surjective (e4_toNq N q h3 F) :=
  fun y => ⟨e4_ofNq N q h3 F y, e4_toNq_ofNq N q h3 F y⟩

private theorem e4_ofNq_surjective (N q : ℕ) [NeZero N] [NeZero q] (h3 : ¬ 3 ∣ N * q) (F : Type) [Field F]
    [CharP F 3] : Function.Surjective (e4_ofNq N q h3 F) :=
  fun r => ⟨e4_toNq N q h3 F r, e4_ofNq_toNq N q h3 F r⟩

private theorem e4_toNq_alpha_jGeomGen (N q : ℕ) [NeZero N] [NeZero q] (h3 : ¬ 3 ∣ N * q) (F : Type) [Field F]
    [CharP F 3] :
    e4_toNq N q h3 F ((ModularCurve.heckeAlphaC F N q) (ModularCurve.jGeomGen F N)) =
      ModularCurve.jGeomGen F (N * q) := by
  apply Subtype.ext
  rw [e4_coe_toNq]
  simp

private theorem e4_coe_push (N q : ℕ) [NeZero N] [NeZero q] (h3 : ¬ 3 ∣ N * q) (F : Type) [Field F] [CharP F 3]
    (g : ↥(ModularCurve.modularFunctionFieldC F N)) :
    ((e4_toNq N q h3 F (ModularCurve.heckeAlphaC F N q g) : ↥(ModularCurve.modularFunctionFieldC F (N * q))) :
      LaurentSeries F) = (g : LaurentSeries F) := by
  rw [e4_coe_toNq]
  simp

private theorem e4_leg (N q : ℕ) [NeZero N] [NeZero q] [Fact q.Prime] (h3 : ¬ 3 ∣ N * q)
    (hε : ∃ p : ℕ, p.Prime ∧ p ∣ N ∧ p % 3 = 2) (F : Type) [Field F] [CharP F 3] [IsAlgClosed F]
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N 4 F) :
    (∀ x : ModularCurve.ssPlaces3 F N, ModularCurve.SSCarrier3.res 1 φ x ≠ 0) ↔
      ∀ x' : ModularCurve.ssPlaces3 F (N * q), ModularCurve.SSCarrier3.res 1 φ x' ≠ 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3N : ¬ 3 ∣ N := fun h => h3 (Dvd.dvd.mul_right h q)
  have hεq : ∃ p : ℕ, p.Prime ∧ p ∣ N * q ∧ p % 3 = 2 := by
    obtain ⟨p, hp, hpN, hp3⟩ := hε
    exact ⟨p, hp, Dvd.dvd.mul_right hpN q, hp3⟩

  have hφ' : φ ∈ ModPForms.modPMod N (2 * ((2 : ℕ) : ℤ)) F := by
    have h : (2 * ((2 : ℕ) : ℤ)) = 4 := by norm_num
    rw [h]
    exact hφ
  obtain ⟨G, -, hGq⟩ := ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod 3 N h3N F 2 φ hφ'
  have hG : (G : LaurentSeries F) * ModularCurve.thetaJ F ^ 2 = HahnSeries.ofPowerSeries ℤ F φ := by
    have h := hGq
    unfold ModularCurve.qexpOfWeight at h
    rwa [zpow_natCast] at h
  have hαint : (ModularCurve.heckeAlphaC F N q).toRingHom.IsIntegral :=
    ModularCurve.heckeAlphaCIntegral_unconditional F N q
  set G' : ↥(ModularCurve.modularFunctionFieldC F (N * q)) := e4_toNq N q h3 F ((ModularCurve.heckeAlphaC F N q) G)
    with hG'def
  have hG' : (G' : LaurentSeries F) * ModularCurve.thetaJ F ^ 2 = HahnSeries.ofPowerSeries ℤ F φ := by
    rw [hG'def, e4_coe_push, hG]
  have hGG' : G' = 0 → G = 0 := by
    intro h0
    have h := congrArg (fun y : ↥(ModularCurve.modularFunctionFieldC F (N * q)) => (y : LaurentSeries F)) h0
    simp only [hG'def, e4_coe_push, ZeroMemClass.coe_zero] at h
    exact Subtype.ext (by rw [ZeroMemClass.coe_zero]; exact h)
  have hjq : e4_toNq N q h3 F ((ModularCurve.heckeAlphaC F N q) (ModularCurve.jGeomGen F N)) =
      ModularCurve.jGeomGen F (N * q) :=
    e4_toNq_alpha_jGeomGen N q h3 F
  have htoNq := e4_toNq_surjective N q h3 F
  have hofNq := e4_ofNq_surjective N q h3 F
  constructor
  ·
    intro h x'
    set w : AlgebraicCurve.Place F ↥(ModularCurve.charLDegeneracyRoof F N q) :=
      x'.1.restrictAlong (e4_toNq N q h3 F) (RingHom.isIntegral_of_surjective _ htoNq) with hwdef
    set x₀ : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N) :=
      w.restrictAlong (ModularCurve.heckeAlphaC F N q) hαint with hx₀def
    set e : ℕ := AlgebraicCurve.Place.ramificationIndexAlong (ModularCurve.heckeAlphaC F N q) w with hedef
    have hord : ∀ g : ↥(ModularCurve.modularFunctionFieldC F N),
        x'.1.ord (e4_toNq N q h3 F ((ModularCurve.heckeAlphaC F N q) g)) = (e : ℤ) * x₀.ord g := by
      intro g
      rw [e4_ord_apply_of_surjective (e4_toNq N q h3 F) htoNq x'.1 ((ModularCurve.heckeAlphaC F N q) g), ← hwdef,
        AlgebraicCurve.Place.ord_restrictAlong (ModularCurve.heckeAlphaC F N q) hαint w g]
    have hjord : x'.1.ord (ModularCurve.jGeomGen F (N * q)) = (e : ℤ) * x₀.ord (ModularCurve.jGeomGen F N) := by
      have h1 := hord (ModularCurve.jGeomGen F N)
      rw [hjq] at h1
      exact h1
    have hGord : x'.1.ord G' = (e : ℤ) * x₀.ord G := by
      rw [hG'def, hord]
    have hx₀ : 0 < x₀.ord (ModularCurve.jGeomGen F N) := by
      have hpos : 0 < (e : ℤ) * x₀.ord (ModularCurve.jGeomGen F N) := by
        rw [← hjord]
        exact x'.2
      have he : (0 : ℤ) ≤ (e : ℤ) := Int.natCast_nonneg e
      nlinarith
    have hD := (e4_res_one_ne_zero_iff N h3N hε F φ G hG ⟨x₀, hx₀⟩).mp (h ⟨x₀, hx₀⟩)
    rw [e4_res_one_ne_zero_iff (N * q) h3 hεq F φ G' hG' x']
    refine ⟨fun h0 => hD.1 (hGG' h0), ?_⟩
    rw [hGord, hjord]
    linear_combination (e : ℤ) * hD.2
  ·
    intro h x
    obtain ⟨w, hw⟩ := AlgebraicCurve.Place.restrictAlong_surjective (ModularCurve.heckeAlphaC F N q) hαint
      (ModularCurve.finiteAlong_heckeAlphaC F N q)
      (ModularCurve.separableAlong_heckeAlphaC_heckeBetaC F (ℓ := 3) N q h3).1 x.1
    have hw' : w.restrictAlong (ModularCurve.heckeAlphaC F N q) hαint = x.1 := hw
    set x₁ : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F (N * q)) :=
      w.restrictAlong (e4_ofNq N q h3 F) (RingHom.isIntegral_of_surjective _ hofNq) with hx₁def
    set e : ℕ := AlgebraicCurve.Place.ramificationIndexAlong (ModularCurve.heckeAlphaC F N q) w with hedef
    have he1 : 1 ≤ e := AlgebraicCurve.Place.one_le_ramificationIndexAlong (ModularCurve.heckeAlphaC F N q) hαint w
    have hord : ∀ g : ↥(ModularCurve.modularFunctionFieldC F N),
        x₁.ord (e4_toNq N q h3 F ((ModularCurve.heckeAlphaC F N q) g)) = (e : ℤ) * x.1.ord g := by
      intro g
      rw [hx₁def,
        ← e4_ord_apply_of_surjective (e4_ofNq N q h3 F) hofNq w
          (e4_toNq N q h3 F ((ModularCurve.heckeAlphaC F N q) g)),
        e4_ofNq_toNq,
        AlgebraicCurve.Place.ord_restrictAlong (ModularCurve.heckeAlphaC F N q) hαint w g, hw']
    have hjord : x₁.ord (ModularCurve.jGeomGen F (N * q)) = (e : ℤ) * x.1.ord (ModularCurve.jGeomGen F N) := by
      have h1 := hord (ModularCurve.jGeomGen F N)
      rw [hjq] at h1
      exact h1
    have hGord : x₁.ord G' = (e : ℤ) * x.1.ord G := by
      rw [hG'def, hord]
    have hx₁ : 0 < x₁.ord (ModularCurve.jGeomGen F (N * q)) := by
      rw [hjord]
      have he : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he1
      exact mul_pos he x.2
    have hD := (e4_res_one_ne_zero_iff (N * q) h3 hεq F φ G' hG' ⟨x₁, hx₁⟩).mp (h ⟨x₁, hx₁⟩)
    rw [e4_res_one_ne_zero_iff N h3N hε F φ G hG x]
    refine ⟨fun h0 => hD.1 (by rw [hG'def, h0, map_zero, map_zero]), ?_⟩
    have hsum : (e : ℤ) * (3 * x.1.ord G + 7 * x.1.ord (ModularCurve.jGeomGen F N)) = 0 := by
      have hD2 := hD.2
      rw [hGord, hjord] at hD2
      linear_combination hD2
    have he : (e : ℤ) ≠ 0 := by
      have : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he1
      exact this.ne'
    exact (mul_eq_zero.mp hsum).resolve_left he

private theorem e4_transport (F : Type) [Field F] (φ : PowerSeries F) {m m' : ℕ} [NeZero m] [NeZero m'] (h : m = m')
    (hm : ∀ x : ModularCurve.ssPlaces3 F m, ModularCurve.SSCarrier3.res 1 φ x ≠ 0) :
    ∀ x : ModularCurve.ssPlaces3 F m', ModularCurve.SSCarrier3.res 1 φ x ≠ 0 := by
  subst h
  exact hm

private theorem e4_climb (F : Type) [Field F] [CharP F 3] [IsAlgClosed F] (φ : PowerSeries F) (r : ℕ) :
    ∀ (L : ℕ) [NeZero L], (∃ p : ℕ, p.Prime ∧ p ∣ L ∧ p % 3 = 2) → φ ∈ ModPForms.modPMod L 4 F → ¬ 3 ∣ L * r →
      (∀ x : ModularCurve.ssPlaces3 F L, ModularCurve.SSCarrier3.res 1 φ x ≠ 0) →
      ∀ [NeZero (L * r)], ∀ x' : ModularCurve.ssPlaces3 F (L * r), ModularCurve.SSCarrier3.res 1 φ x' ≠ 0 := by
  induction r using induction_on_primes with
  | zero =>
    intro L _ _ _ _ _ _
    exact absurd (mul_zero L) (NeZero.ne (L * 0))
  | one =>
    intro L _ _ _ _ h _
    exact e4_transport F φ (mul_one L).symm h
  | prime_mul p a hp ih =>
    intro L _ hε hφ h3 h _
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero a := ⟨fun ha => NeZero.ne (L * (p * a)) (by rw [ha, mul_zero, mul_zero])⟩
    have h3a : ¬ 3 ∣ L * a := by
      intro hd
      apply h3
      rw [mul_comm p a, ← mul_assoc]
      exact Dvd.dvd.mul_right hd p
    have hLa := ih L hε hφ h3a h
    have hεa : ∃ p' : ℕ, p'.Prime ∧ p' ∣ L * a ∧ p' % 3 = 2 := by
      obtain ⟨p', hp', hp'L, hp'3⟩ := hε
      exact ⟨p', hp', Dvd.dvd.mul_right hp'L a, hp'3⟩
    have hφa : φ ∈ ModPForms.modPMod (L * a) 4 F :=
      ModPForms.modPMod_le_modPMod_of_dvd L (L * a) (Dvd.intro a rfl) 4 F hφ
    have h3ap : ¬ 3 ∣ L * a * p := by
      rw [mul_assoc, mul_comm a p]
      exact h3
    have hstep := (e4_leg (L * a) p h3ap hεa F φ hφa).mp hLa
    exact e4_transport F φ (by ring : L * a * p = L * (p * a)) hstep

end LegE4

section LegE1

namespace K2UE1

open ModPForms

private theorem e1_ord_pow {K E : Type*} [Field K] [Field E] [Algebra K E] (x : AlgebraicCurve.Place K E)
    {a : E} (ha : a ≠ 0) (i : ℕ) : x.ord (a ^ i) = (i : ℤ) * x.ord a := by
  have _ := ha
  rw [← zpow_natCast, x.ord_zpow]

private theorem e1_ord_neg {K E : Type*} [Field K] [Field E] [Algebra K E] (x : AlgebraicCurve.Place K E)
    (a : E) : x.ord (-a) = x.ord a := by
  simp only [AlgebraicCurve.Place.ord, Valuation.map_neg]

private theorem e1_ord_nonneg_of_mem {K E : Type*} [Field K] [Field E] [Algebra K E] (v : AlgebraicCurve.Place K E)
    {f : E} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : E) * ((π : E) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem e1_mem_of_ord_nonneg {K E : Type*} [Field K] [Field E] [Algebra K E] (v : AlgebraicCurve.Place K E)
    {f : E} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

private theorem e1_residue_eq_zero {K E : Type*} [Field K] [Field E] [Algebra K E] (x : AlgebraicCurve.Place K E)
    (f : E) (hf : 1 ≤ x.ord f) (hmem : f ∈ x.toValuationSubring) :
    IsLocalRing.residue x.toValuationSubring ⟨f, hmem⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hv : x.adicValuation f = 1 := (x.adicValuation_coe_eq_one_iff ⟨f, hmem⟩).2 hu
  have h0 : x.ord f = 0 := by simp [AlgebraicCurve.Place.ord, hv]
  omega

private theorem e1_one_le_ord_of_residue_eq_zero {K E : Type*} [Field K] [Field E] [Algebra K E]
    (x : AlgebraicCurve.Place K E) (f : E) (hf0 : f ≠ 0) (hmem : f ∈ x.toValuationSubring)
    (h : IsLocalRing.residue x.toValuationSubring ⟨f, hmem⟩ = 0) : 1 ≤ x.ord f := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
  have hnn : 0 ≤ x.ord f := e1_ord_nonneg_of_mem x hmem
  by_contra hlt
  have h0 : x.ord f = 0 := by omega
  apply h
  rw [← x.adicValuation_coe_eq_one_iff ⟨f, hmem⟩]
  have hv : x.adicValuation f ≠ 0 := x.adicValuation_ne_zero hf0
  have hlog : WithZero.log (x.adicValuation f) = 0 := by
    unfold AlgebraicCurve.Place.ord at h0
    omega
  rw [← WithZero.exp_log hv, hlog, WithZero.exp_zero]

private theorem e1_thetaJ3_coeff_pow_three (K : Type) [Field K] [CharP K 3] (g : PowerSeries K) {n : ℕ}
    (hn : ¬ 3 ∣ n) : PowerSeries.coeff n (g ^ 3) = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : PowerSeries.coeff n (g ^ 3) = (PowerSeries.trunc (n + 1) (g ^ 3)).coeff n := by
    rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_self n)]
  have h2 : (PowerSeries.trunc (n + 1) g) ^ 3
      = Polynomial.map (frobenius K 3) (Polynomial.expand K 3 (PowerSeries.trunc (n + 1) g)) :=
    (Polynomial.map_frobenius_expand (p := 3) (PowerSeries.trunc (n + 1) g)).symm
  rw [h1, ← PowerSeries.trunc_trunc_pow, ← Polynomial.coe_pow, h2]
  simp [PowerSeries.coeff_trunc, Polynomial.coeff_coe, Polynomial.coeff_expand, hn]

private theorem e1_thetaJ3_jNum_eq_pow_three :
    ModularCurve.jNum
      = (ModularCurve.eisenstein4 * ModularCurve.etaProd ^ 16 * ModularCurve.dedekindEtaUnitInv) ^ 3 := by
  have h := ModularCurve.dedekindEtaUnit_mul_inv
  unfold ModularCurve.dedekindEtaUnit at h
  unfold ModularCurve.jNum
  linear_combination (-(ModularCurve.eisenstein4 ^ 3 * ModularCurve.dedekindEtaUnitInv
    * (1 + ModularCurve.etaProd ^ 24 * ModularCurve.dedekindEtaUnitInv))) * h

private theorem e1_thetaJ3_coeff_jqModC (K : Type) [Field K] [CharP K 3] {n : ℤ} (hn : ¬ (3 : ℤ) ∣ n + 1) :
    (ModularCurve.jqModC K).coeff n = 0 := by
  unfold ModularCurve.jqModC
  rw [HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add]
  by_cases h : n + 1 < 0
  · exact ModularCurve.ofPowerSeries_coeff_of_neg _ h
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp h)
    rw [hm, HahnSeries.ofPowerSeries_apply_coeff, e1_thetaJ3_jNum_eq_pow_three, map_pow]
    apply e1_thetaJ3_coeff_pow_three
    intro hdvd
    apply hn
    rw [hm]
    exact_mod_cast hdvd

private theorem e1_thetaJ3_coeff_thetaL (K : Type) [Field K] (f : LaurentSeries K) (n : ℤ) :
    (ModularCurve.thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [ModularCurve.thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp [zsmul_eq_mul]

private theorem e1_thetaL_jqModC_eq_neg (K : Type) [Field K] [CharP K 3] :
    ModularCurve.thetaL K (ModularCurve.jqModC K) = -ModularCurve.jqModC K := by
  ext n
  rw [e1_thetaJ3_coeff_thetaL, HahnSeries.coeff_neg]
  by_cases h : (3 : ℤ) ∣ n + 1
  · obtain ⟨c, hc⟩ := h
    have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
    have hn : (n : K) = -1 := by
      have hn' : n = 3 * c - 1 := by omega
      rw [hn']
      push_cast
      rw [h3]
      ring
    rw [hn, neg_one_mul]
  · rw [e1_thetaJ3_coeff_jqModC K h, mul_zero, neg_zero]

private theorem e1_char (F : Type) [Field F] [CharP F 3] : (1728 : F) = 0 := by
  have h : ((1728 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 3 1728).mpr (by norm_num)
  exact_mod_cast h

private noncomputable def e1_adjoinEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : E) :
    Algebra.adjoin K ({t} : Set E) ≃ₐ[K] Algebra.adjoin K ({(t : L)} : Set L) :=
  (Subalgebra.equivMapOfInjective (Algebra.adjoin K ({t} : Set E)) E.val Subtype.val_injective).trans
    (Subalgebra.equivOfEq _ _ (by rw [AlgHom.map_adjoin, Set.image_singleton]; rfl))

private theorem e1_coe_adjoinEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : E) (a : Algebra.adjoin K ({t} : Set E)) :
    ((e1_adjoinEquiv E t a : Algebra.adjoin K ({(t : L)} : Set L)) : L) = ((a : E) : L) :=
  rfl

private theorem e1_isIntegral_of_coe {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t u : E)
    (hu : IsIntegral (Algebra.adjoin K ({(t : L)} : Set L)) (u : L)) :
    IsIntegral (Algebra.adjoin K ({t} : Set E)) u := by
  have h1 : IsIntegral (Algebra.adjoin K ({t} : Set E)) (u : L) := by
    refine IsIntegral.map_of_comp_eq (e1_adjoinEquiv E t).symm.toAlgHom.toRingHom (RingHom.id L) ?_ hu
    refine RingHom.ext fun b => ?_
    have hb := e1_coe_adjoinEquiv E t ((e1_adjoinEquiv E t).symm b)
    rw [AlgEquiv.apply_symm_apply] at hb
    exact hb.symm
  haveI : IsScalarTower (Algebra.adjoin K ({t} : Set E)) E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (Algebra.adjoin K ({t} : Set E)) E L)
    (algebraMap E L).injective).mp h1

private theorem e1_thetaJ_ne_zero (F : Type) [Field F] [CharP F 3] : ModularCurve.thetaJ F ≠ 0 := by
  have hθ : ModularCurve.thetaJ F = -ModularCurve.jqModC F := e1_thetaL_jqModC_eq_neg F
  rw [hθ, neg_ne_zero]
  exact ModularCurve.jqModC_ne_zero_def F

private theorem e1_ord_bound (N' : ℕ) [NeZero N'] (F : Type) [Field F] [CharP F 3] (m : ℕ)
    (G : ↥(ModularCurve.modularFunctionFieldC F N')) (hG0 : G ≠ 0)
    (hfn : ModularCurve.IsModPFormFn F m (G : LaurentSeries F))
    (x : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N'))
    (hx : 0 < x.ord (ModularCurve.jGeomGen F N')) :
    0 ≤ 6 * x.ord G + 7 * (m : ℤ) * x.ord (ModularCurve.jGeomGen F N') := by
  have hjne : ModularCurve.jqModC F ≠ 0 := ModularCurve.jqModC_ne_zero_def F
  have hj0 : ModularCurve.jGeomGen F N' ≠ 0 := by
    intro h
    apply hjne
    have h' := congrArg (fun y : ↥(ModularCurve.modularFunctionFieldC F N') => (y : LaurentSeries F)) h
    simpa using h'
  have h1728 : algebraMap F (LaurentSeries F) (1728 : F) = 0 := by rw [e1_char F, map_zero]
  unfold ModularCurve.IsModPFormFn at hfn
  obtain ⟨h1, -⟩ := hfn
  simp only [h1728, sub_zero] at h1
  have hY : IsIntegral
      (Algebra.adjoin F ({ModularCurve.jGeomGen F N'} : Set ↥(ModularCurve.modularFunctionFieldC F N')))
      (G ^ 6 * ModularCurve.jGeomGen F N' ^ (4 * m) * ModularCurve.jGeomGen F N' ^ (3 * m)) := by
    apply e1_isIntegral_of_coe
    push_cast
    exact h1
  have hYord := x.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg hY hx.le
  rw [x.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj0),
    x.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), e1_ord_pow x hG0, e1_ord_pow x hj0, e1_ord_pow x hj0]
    at hYord
  push_cast at hYord
  linarith

private theorem e1_ord_uniformizer (N' : ℕ) [NeZero N'] (F : Type) [Field F] (x : ModularCurve.ssPlaces3 F N') :
    x.1.ord (ModularCurve.SSCarrier3.uniformizer x) = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.1.toValuationSubring
  unfold ModularCurve.SSCarrier3.uniformizer
  exact Classical.epsilon_spec
    (⟨(π : ↥(ModularCurve.modularFunctionFieldC F N')), x.1.ord_coe_irreducible hπ⟩ :
      ∃ ϖ : ↥(ModularCurve.modularFunctionFieldC F N'), x.1.ord ϖ = 1)

private theorem e1_jne (F : Type) [Field F] [CharP F 3] (N' : ℕ) [NeZero N'] : ModularCurve.jGeomGen F N' ≠ 0 := by
  intro h
  apply ModularCurve.jqModC_ne_zero_def F
  have h' := congrArg (fun y : ↥(ModularCurve.modularFunctionFieldC F N') => (y : LaurentSeries F)) h
  simpa using h'

private theorem e1_theta (F : Type) [Field F] [CharP F 3] (N' : ℕ) [NeZero N'] :
    ModularCurve.thetaJ F
      = -((ModularCurve.jGeomGen F N' : ↥(ModularCurve.modularFunctionFieldC F N')) : LaurentSeries F) := by
  have hc : ((ModularCurve.jGeomGen F N' : ↥(ModularCurve.modularFunctionFieldC F N')) : LaurentSeries F)
      = ModularCurve.jqModC F := rfl
  rw [hc]
  exact e1_thetaL_jqModC_eq_neg F

private theorem e1_exists_witness (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (F : Type) [Field F] [CharP F 3] (m : ℕ)
    (φ : PowerSeries F) (hφ : φ ∈ modPMod N' (2 * (m : ℤ) + 2) F) :
    ∃ G₁ : ↥(ModularCurve.modularFunctionFieldC F N'),
      ModularCurve.IsModPFormFn F (m + 1) (G₁ : LaurentSeries F) ∧
      ((G₁ * -ModularCurve.jGeomGen F N' : ↥(ModularCurve.modularFunctionFieldC F N')) : LaurentSeries F) *
          ModularCurve.thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ := by
  have hφ' : φ ∈ modPMod N' (2 * ((m + 1 : ℕ) : ℤ)) F := by
    have h2 : (2 * ((m + 1 : ℕ) : ℤ)) = 2 * (m : ℤ) + 2 := by push_cast; ring
    rw [h2]
    exact hφ
  obtain ⟨G₁, hfn, hq⟩ :=
    ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod 3 N' hpN' F (m + 1) φ hφ'
  refine ⟨G₁, hfn, ?_⟩
  have hq' : (G₁ : LaurentSeries F) * ModularCurve.thetaJ F ^ (m + 1) = HahnSeries.ofPowerSeries ℤ F φ := by
    have h := hq
    unfold ModularCurve.qexpOfWeight at h
    rwa [zpow_natCast] at h
  have key : ((G₁ * -ModularCurve.jGeomGen F N' : ↥(ModularCurve.modularFunctionFieldC F N')) : LaurentSeries F)
      = (G₁ : LaurentSeries F) * ModularCurve.thetaJ F := by
    rw [e1_theta F N']
    push_cast
    rfl
  rw [← hq', pow_succ', ← mul_assoc, key]

private theorem e1_unique (F : Type) [Field F] [CharP F 3] (N' : ℕ) [NeZero N'] (m : ℕ) {y : LaurentSeries F}
    {G G' : ↥(ModularCurve.modularFunctionFieldC F N')}
    (h : (G : LaurentSeries F) * ModularCurve.thetaJ F ^ m = y) (h' : (G' : LaurentSeries F) * ModularCurve.thetaJ F ^ m = y) :
    G = G' := by
  apply Subtype.ext
  exact mul_right_cancel₀ (pow_ne_zero m (e1_thetaJ_ne_zero F)) (h.trans h'.symm)

open Classical in

private noncomputable def e1_G (F : Type) [Field F] (N' : ℕ) [NeZero N'] (m : ℕ) (φ : PowerSeries F) :
    ↥(ModularCurve.modularFunctionFieldC F N') :=
  if h : ∃ G : ↥(ModularCurve.modularFunctionFieldC F N'),
      (G : LaurentSeries F) * ModularCurve.thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ then Classical.choose h else 0

private theorem e1_G_eq (F : Type) [Field F] (N' : ℕ) [NeZero N'] (m : ℕ) (φ : PowerSeries F)
    (h : ∃ G : ↥(ModularCurve.modularFunctionFieldC F N'),
      (G : LaurentSeries F) * ModularCurve.thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ) :
    e1_G F N' m φ = Classical.choose h := by
  unfold e1_G
  rw [dif_pos h]

private theorem e1_G_spec (F : Type) [Field F] (N' : ℕ) [NeZero N'] (m : ℕ) (φ : PowerSeries F)
    (h : ∃ G : ↥(ModularCurve.modularFunctionFieldC F N'),
      (G : LaurentSeries F) * ModularCurve.thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ) :
    (e1_G F N' m φ : LaurentSeries F) * ModularCurve.thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ := by
  rw [e1_G_eq F N' m φ h]
  exact Classical.choose_spec h

private theorem e1_G_ex (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (F : Type) [Field F] [CharP F 3] (m : ℕ)
    (φ : PowerSeries F) (hφ : φ ∈ modPMod N' (2 * (m : ℤ) + 2) F) :
    ∃ G : ↥(ModularCurve.modularFunctionFieldC F N'),
      (G : LaurentSeries F) * ModularCurve.thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ := by
  obtain ⟨G₁, -, hG₁⟩ := e1_exists_witness N' hpN' F m φ hφ
  exact ⟨_, hG₁⟩

private theorem e1_G_shape (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (F : Type) [Field F] [CharP F 3] (m : ℕ)
    (φ : PowerSeries F) (hφ : φ ∈ modPMod N' (2 * (m : ℤ) + 2) F) :
    ∃ G₁ : ↥(ModularCurve.modularFunctionFieldC F N'),
      ModularCurve.IsModPFormFn F (m + 1) (G₁ : LaurentSeries F) ∧ e1_G F N' m φ = G₁ * -ModularCurve.jGeomGen F N' := by
  obtain ⟨G₁, hfn, hG₁⟩ := e1_exists_witness N' hpN' F m φ hφ
  exact ⟨G₁, hfn, e1_unique F N' m (e1_G_spec F N' m φ ⟨_, hG₁⟩) hG₁⟩

private theorem e1_mem (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F 3] [IsAlgClosed F] (m : ℕ) (φ : PowerSeries F) (hφ : φ ∈ modPMod N' (2 * (m : ℤ) + 2) F)
    (x : ModularCurve.ssPlaces3 F N') :
    e1_G F N' m φ * ModularCurve.SSCarrier3.uniformizer x ^ (ModularCurve.SSCarrier3.aPole m x).toNat ∈
      x.1.toValuationSubring := by
  obtain ⟨G₁, hfn, hG⟩ := e1_G_shape N' hpN' F m φ hφ
  rw [hG]
  by_cases hG0 : G₁ = 0
  · rw [hG0, zero_mul, zero_mul]
    exact zero_mem _
  have hj0 := e1_jne F N'
  have hπ1 := e1_ord_uniformizer N' F x
  have hπ0 : ModularCurve.SSCarrier3.uniformizer x ≠ 0 := by
    intro h0
    rw [h0, x.1.ord_zero] at hπ1
    exact zero_ne_one hπ1
  have hne : G₁ * -ModularCurve.jGeomGen F N' *
      ModularCurve.SSCarrier3.uniformizer x ^ (ModularCurve.SSCarrier3.aPole m x).toNat ≠ 0 :=
    mul_ne_zero (mul_ne_zero hG0 (neg_ne_zero.mpr hj0)) (pow_ne_zero _ hπ0)
  apply e1_mem_of_ord_nonneg x.1 hne
  have hbound := e1_ord_bound N' F (m + 1) G₁ hG0 hfn x.1 x.2
  have he := ModularCurve.ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed N' hpN' hε F x.1 x.2
  have hA : 0 ≤ 7 * (m : ℤ) * x.1.ord (ModularCurve.jGeomGen F N') :=
    mul_nonneg (mul_nonneg (by norm_num) (Int.natCast_nonneg m)) x.2.le
  have hn : (((ModularCurve.SSCarrier3.aPole m x).toNat : ℕ) : ℤ) = ModularCurve.SSCarrier3.aPole m x := by
    apply Int.toNat_of_nonneg
    unfold ModularCurve.SSCarrier3.aPole
    omega
  rw [x.1.ord_mul (mul_ne_zero hG0 (neg_ne_zero.mpr hj0)) (pow_ne_zero _ hπ0),
    x.1.ord_mul hG0 (neg_ne_zero.mpr hj0), e1_ord_neg, e1_ord_pow x.1 hπ0, hπ1, mul_one, hn]
  have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
  rw [hcast] at hbound
  unfold ModularCurve.SSCarrier3.aPole
  rcases he with he | he <;> rw [he] at hbound ⊢ <;> omega

private theorem e1_res_eq (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F 3] [IsAlgClosed F] (m : ℕ) (φ : PowerSeries F) (hφ : φ ∈ modPMod N' (2 * (m : ℤ) + 2) F)
    (x : ModularCurve.ssPlaces3 F N') :
    ModularCurve.SSCarrier3.res m φ x =
      IsLocalRing.residue x.1.toValuationSubring ⟨_, e1_mem N' hpN' hε F m φ hφ x⟩ := by
  have hex := e1_G_ex N' hpN' F m φ hφ
  have hch : Classical.choose hex = e1_G F N' m φ := (e1_G_eq F N' m φ hex).symm
  unfold ModularCurve.SSCarrier3.res
  rw [dif_pos hex]
  have hm : Classical.choose hex * ModularCurve.SSCarrier3.uniformizer x ^ (ModularCurve.SSCarrier3.aPole m x).toNat ∈
      x.1.toValuationSubring := by
    rw [hch]
    exact e1_mem N' hpN' hε F m φ hφ x
  rw [dif_pos hm]
  congr 1
  apply Subtype.ext
  show Classical.choose hex * _ = e1_G F N' m φ * _
  rw [hch]

private theorem e1_hsep (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (F : Type) [Field F] [CharP F 3] :
    IsSeparable (IntermediateField.adjoin F ({ModularCurve.jqModC F} : Set (LaurentSeries F))) (ModularCurve.jqNModC F N') := by
  apply ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero
  intro h
  exact hpN' ((CharP.cast_eq_zero_iff F 3 N').1 h)

private theorem e1_finite (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (F : Type) [Field F] [CharP F 3] :
    Finite (ModularCurve.ssPlaces3 F N') := by
  have h := ModularCurve.finite_setOf_ord_jGeomGen_sub_pos F N' (e1_hsep N' hpN' F) 0
  simp only [map_zero, sub_zero] at h
  exact h.to_subtype

private def bSer (F : Type) [Field F] (d : ℕ) : PowerSeries F :=
  PowerSeries.mk fun n : ℕ =>
    ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
      (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ) : F)

private theorem e1_coeff_zero_bSer_two (F : Type) [Field F] : PowerSeries.coeff 0 (bSer F 2) = 0 := by
  unfold bSer
  rw [PowerSeries.coeff_mk]
  simp

private theorem e1_coeff_one_bSer_two (F : Type) [Field F] : PowerSeries.coeff 1 (bSer F 2) = 1 := by
  unfold bSer
  rw [PowerSeries.coeff_mk]
  norm_num [ArithmeticFunction.sigma_apply]

private theorem e1_dedekindPsi_two : ModularCurve.dedekindPsi 2 = 3 := by
  rw [ModularCurve.dedekindPsi]
  decide +kernel

private theorem e1_bound_two : ModularCurve.genusFormula 2 + (ModularCurve.cuspCount 2 : ℚ) - 1 = 1 := by
  have hc : ModularCurve.cuspCount 2 = 2 := by decide
  have h2 : ModularCurve.nuTwo 2 = 1 := by rw [ModularCurve.nuTwo, Nat.card_eq_fintype_card]; decide
  have h3 : ModularCurve.nuThree 2 = 0 := by rw [ModularCurve.nuThree, Nat.card_eq_fintype_card]; decide
  rw [ModularCurve.genusFormula, hc, e1_dedekindPsi_two, h2, h3]
  norm_num

private theorem e1_place_two (F : Type) [Field F] [CharP F 3] [IsAlgClosed F] (x y : ModularCurve.ssPlaces3 F 2) :
    x = y ∧ x.1.ord (ModularCurve.jGeomGen F 2) = 3 := by
  have hp2 : ¬ 3 ∣ 2 := by decide
  have hε : ∃ q : ℕ, q.Prime ∧ q ∣ 2 ∧ q % 3 = 2 := ⟨2, Nat.prime_two, dvd_rfl, rfl⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModularCurve.ssPlaces3 F 2) := e1_finite 2 hp2 F
  haveI : Fintype (ModularCurve.ssPlaces3 F 2) := Fintype.ofFinite _
  classical
  set T : Finset (AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F 2)) :=
    (Finset.univ : Finset (ModularCurve.ssPlaces3 F 2)).map ⟨Subtype.val, Subtype.val_injective⟩ with hTdef
  have hj : ModularCurve.jGeomGen F 2 - algebraMap F ↥(ModularCurve.modularFunctionFieldC F 2) 0
      = ModularCurve.jGeomGen F 2 := by rw [map_zero, sub_zero]
  have hT : ∀ w, w ∈ T ↔
      0 < w.ord (ModularCurve.jGeomGen F 2 - algebraMap F ↥(ModularCurve.modularFunctionFieldC F 2) 0) := by
    intro w
    rw [hj, hTdef, Finset.mem_map]
    constructor
    · rintro ⟨z, -, rfl⟩
      exact z.2
    · intro hw
      exact ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩
  have hsum := ModularCurve.sum_ord_jGeomGen_sub_eq_dedekindPsi 3 2 hp2 F (e1_hsep 2 hp2 F) 0 T hT
  rw [hj, e1_dedekindPsi_two, hTdef, Finset.sum_map] at hsum

  have hge : ∀ z : ModularCurve.ssPlaces3 F 2, (3 : ℤ) ≤ z.1.ord (ModularCurve.jGeomGen F 2) := by
    intro z
    rcases ModularCurve.ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed 2 hp2 hε F z.1 z.2
      with h | h <;> omega
  have hrest : ∀ s : Finset (ModularCurve.ssPlaces3 F 2),
      0 ≤ ∑ z ∈ s, (z : ModularCurve.ssPlaces3 F 2).1.ord (ModularCurve.jGeomGen F 2) :=
    fun s => Finset.sum_nonneg fun z _ => le_trans (by norm_num) (hge z)
  have hx := Finset.add_sum_erase Finset.univ
    (fun z : ModularCurve.ssPlaces3 F 2 => z.1.ord (ModularCurve.jGeomGen F 2)) (Finset.mem_univ x)
  simp only [Function.Embedding.coeFn_mk] at hsum
  constructor
  · by_contra hxy
    have hy : y ∈ Finset.univ.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_univ y⟩
    have hy' := Finset.add_sum_erase (Finset.univ.erase x)
      (fun z : ModularCurve.ssPlaces3 F 2 => z.1.ord (ModularCurve.jGeomGen F 2)) hy
    have h1 := hge x
    have h2 := hge y
    have h3 := hrest ((Finset.univ.erase x).erase y)
    push_cast at hsum
    linarith
  · have h1 := hge x
    have h3 := hrest (Finset.univ.erase x)
    push_cast at hsum
    rcases ModularCurve.ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed 2 hp2 hε F x.1 x.2
      with h | h
    · exact h
    · linarith

private theorem e1_forall_res_one_bSer_two_ne_zero
    (F : Type) [Field F] [CharP F 3] [IsAlgClosed F]
    (hB : bSer F 2 ∈ ModPForms.modPMod 2 4 F) :
    ∀ x : ModularCurve.ssPlaces3 F 2, ModularCurve.SSCarrier3.res 1 (bSer F 2) x ≠ 0 := by
  intro x hres
  have hp2 : ¬ 3 ∣ 2 := by decide
  have hε : ∃ q : ℕ, q.Prime ∧ q ∣ 2 ∧ q % 3 = 2 := ⟨2, Nat.prime_two, dvd_rfl, rfl⟩
  have hφ : bSer F 2 ∈ modPMod 2 (2 * ((1 : ℕ) : ℤ) + 2) F := by
    norm_num
    exact hB

  rw [e1_res_eq 2 hp2 hε F 1 (bSer F 2) hφ x] at hres
  have hex := e1_G_ex 2 hp2 F 1 (bSer F 2) hφ
  have hGspec := e1_G_spec F 2 1 (bSer F 2) hex
  set G := e1_G F 2 1 (bSer F 2) with hGdef
  have hG0 : G ≠ 0 := by
    intro h0
    have h1 := congrArg (fun f : LaurentSeries F => f.coeff 1) hGspec
    simp only [h0, ZeroMemClass.coe_zero, zero_mul, HahnSeries.coeff_zero] at h1
    rw [show ((1 : ℤ)) = ((1 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, e1_coeff_one_bSer_two] at h1
    exact one_ne_zero h1.symm
  have hπ1 := e1_ord_uniformizer 2 F x
  have hπ0 : ModularCurve.SSCarrier3.uniformizer x ≠ 0 := by
    intro h0
    rw [h0, x.1.ord_zero] at hπ1
    exact zero_ne_one hπ1
  have hmem := e1_mem 2 hp2 hε F 1 (bSer F 2) hφ x
  have hne : G * ModularCurve.SSCarrier3.uniformizer x ^ (ModularCurve.SSCarrier3.aPole 1 x).toNat ≠ 0 :=
    mul_ne_zero hG0 (pow_ne_zero _ hπ0)
  have h1 := e1_one_le_ord_of_residue_eq_zero x.1 _ hne hmem hres

  have he3 := (e1_place_two F x x).2
  have ha : ModularCurve.SSCarrier3.aPole 1 x = 4 := by
    unfold ModularCurve.SSCarrier3.aPole
    rw [he3]
    decide
  rw [x.1.ord_mul hG0 (pow_ne_zero _ hπ0), e1_ord_pow x.1 hπ0, hπ1, mul_one, ha] at h1
  have hordG : -3 ≤ x.1.ord G := by
    have : ((4 : ℤ).toNat : ℤ) = 4 := by decide
    omega

  have hvan : ∀ w : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F 2),
      0 < w.ord (ModularCurve.jGeomGen F 2) →
        0 ≤ 6 * w.ord G + 7 * ((1 : ℕ) : ℤ) * w.ord (ModularCurve.jGeomGen F 2) := by
    intro w hw
    have hwx := (e1_place_two F ⟨w, hw⟩ x).1
    have hw' : w = x.1 := congrArg Subtype.val hwx
    rw [hw', he3]
    push_cast
    linarith
  have hW2 := mem_modPMod_of_coe_mul_thetaJ_pow_eq_of_forall_ord_pos_of_exists_prime_dvd_mod_three_eq_two
    2 hp2 hε F 1 (bSer F 2) hφ G hGspec hvan

  have hW2' : bSer F 2 ∈ modPMod 2 2 F := by
    have h2 : (2 * ((1 : ℕ) : ℤ)) = 2 := by norm_num
    rw [h2] at hW2
    exact hW2
  have hone : (1 : PowerSeries F) ∈ modPMod 2 2 F :=
    one_mem_modPMod_two_of_exists_prime_dvd_mod_three_eq_two 2 hε F
  haveI : FiniteDimensional F ↥(modPMod 2 2 F) := finiteDimensional_modPMod 2 2 F
  have hle : (Module.finrank F ↥(modPMod 2 2 F) : ℚ) ≤ 1 := by
    have h := finrank_modPMod_two_le_genusFormula_add_cuspCount_sub_one 2 F
    linarith [e1_bound_two]
  have hle' : Module.finrank F ↥(modPMod 2 2 F) ≤ 1 := by exact_mod_cast hle
  have hli : LinearIndependent F ![(⟨1, hone⟩ : ↥(modPMod 2 2 F)), ⟨bSer F 2, hW2'⟩] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := congrArg (fun w : ↥(modPMod 2 2 F) => (w : PowerSeries F)) hst
    simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero] at h
    have h0 := congrArg (PowerSeries.coeff 0) h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp only [map_add, map_smul, map_zero, smul_eq_mul, e1_coeff_zero_bSer_two, e1_coeff_one_bSer_two,
      PowerSeries.coeff_one, if_true, mul_one, mul_zero, add_zero] at h0 h1
    simp only [one_ne_zero, if_false, mul_zero, zero_add] at h1
    exact ⟨h0, h1⟩
  have h2 := hli.fintype_card_le_finrank
  simp at h2
  omega

end K2UE1

end LegE1

section LegE23

namespace R3cK2ULegE

private def _root_.R3cK2ULegE.bSer (F : Type) [Field F] (d : ℕ) : PowerSeries F :=
  PowerSeries.mk fun n : ℕ =>
    ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
      (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ) : F)

p2m_export "R3cK2ULegE" "bSer"
private theorem k1le_thetaJ3_coeff_pow_three (K : Type) [Field K] [CharP K 3] (g : PowerSeries K) {n : ℕ}
    (hn : ¬ 3 ∣ n) : PowerSeries.coeff n (g ^ 3) = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : PowerSeries.coeff n (g ^ 3) = (PowerSeries.trunc (n + 1) (g ^ 3)).coeff n := by
    rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_self n)]
  have h2 : (PowerSeries.trunc (n + 1) g) ^ 3
      = Polynomial.map (frobenius K 3) (Polynomial.expand K 3 (PowerSeries.trunc (n + 1) g)) :=
    (Polynomial.map_frobenius_expand (p := 3) (PowerSeries.trunc (n + 1) g)).symm
  rw [h1, ← PowerSeries.trunc_trunc_pow, ← Polynomial.coe_pow, h2]
  simp [PowerSeries.coeff_trunc, Polynomial.coeff_coe, Polynomial.coeff_expand, hn]

private theorem k1le_thetaJ3_jNum_eq_pow_three :
    ModularCurve.jNum
      = (ModularCurve.eisenstein4 * ModularCurve.etaProd ^ 16 * ModularCurve.dedekindEtaUnitInv) ^ 3 := by
  have h := ModularCurve.dedekindEtaUnit_mul_inv
  unfold ModularCurve.dedekindEtaUnit at h
  unfold ModularCurve.jNum
  linear_combination (-(ModularCurve.eisenstein4 ^ 3 * ModularCurve.dedekindEtaUnitInv
    * (1 + ModularCurve.etaProd ^ 24 * ModularCurve.dedekindEtaUnitInv))) * h

private theorem k1le_thetaJ3_coeff_jqModC (K : Type) [Field K] [CharP K 3] {n : ℤ} (hn : ¬ (3 : ℤ) ∣ n + 1) :
    (ModularCurve.jqModC K).coeff n = 0 := by
  unfold ModularCurve.jqModC
  rw [HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add]
  by_cases h : n + 1 < 0
  · exact ModularCurve.ofPowerSeries_coeff_of_neg _ h
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp h)
    rw [hm, HahnSeries.ofPowerSeries_apply_coeff, k1le_thetaJ3_jNum_eq_pow_three, map_pow]
    apply k1le_thetaJ3_coeff_pow_three
    intro hdvd
    apply hn
    rw [hm]
    exact_mod_cast hdvd

private theorem k1le_thetaJ3_coeff_thetaL (K : Type) [Field K] (f : LaurentSeries K) (n : ℤ) :
    (ModularCurve.thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [ModularCurve.thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp [zsmul_eq_mul]

private theorem k1le_thetaL_jqModC_eq_neg (K : Type) [Field K] [CharP K 3] :
    ModularCurve.thetaL K (ModularCurve.jqModC K) = -ModularCurve.jqModC K := by
  ext n
  rw [k1le_thetaJ3_coeff_thetaL, HahnSeries.coeff_neg]
  by_cases h : (3 : ℤ) ∣ n + 1
  · obtain ⟨c, hc⟩ := h
    have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
    have hn : (n : K) = -1 := by
      have hn' : n = 3 * c - 1 := by omega
      rw [hn']
      push_cast
      rw [h3]
      ring
    rw [hn, neg_one_mul]
  · rw [k1le_thetaJ3_coeff_jqModC K h, mul_zero, neg_zero]

private theorem k1le_char (F : Type) [Field F] [CharP F 3] : (1728 : F) = 0 := by
  have h : ((1728 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 3 1728).mpr (by norm_num)
  exact_mod_cast h

private noncomputable def k1le_adjoinEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : E) :
    Algebra.adjoin K ({t} : Set E) ≃ₐ[K] Algebra.adjoin K ({(t : L)} : Set L) :=
  (Subalgebra.equivMapOfInjective (Algebra.adjoin K ({t} : Set E)) E.val Subtype.val_injective).trans
    (Subalgebra.equivOfEq _ _ (by rw [AlgHom.map_adjoin, Set.image_singleton]; rfl))

private theorem k1le_coe_adjoinEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t : E) (a : Algebra.adjoin K ({t} : Set E)) :
    ((k1le_adjoinEquiv E t a : Algebra.adjoin K ({(t : L)} : Set L)) : L) = ((a : E) : L) :=
  rfl

private theorem k1le_isIntegral_of_coe {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (t u : E)
    (hu : IsIntegral (Algebra.adjoin K ({(t : L)} : Set L)) (u : L)) :
    IsIntegral (Algebra.adjoin K ({t} : Set E)) u := by
  have h1 : IsIntegral (Algebra.adjoin K ({t} : Set E)) (u : L) := by
    refine IsIntegral.map_of_comp_eq (k1le_adjoinEquiv E t).symm.toAlgHom.toRingHom (RingHom.id L) ?_ hu
    refine RingHom.ext fun b => ?_
    have hb := k1le_coe_adjoinEquiv E t ((k1le_adjoinEquiv E t).symm b)
    rw [AlgEquiv.apply_symm_apply] at hb
    exact hb.symm
  haveI : IsScalarTower (Algebra.adjoin K ({t} : Set E)) E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (Algebra.adjoin K ({t} : Set E)) E L)
    (algebraMap E L).injective).mp h1

private theorem k1le_ord_pow {K E : Type*} [Field K] [Field E] [Algebra K E] (x : AlgebraicCurve.Place K E)
    {a : E} (ha : a ≠ 0) (i : ℕ) : x.ord (a ^ i) = (i : ℤ) * x.ord a := by
  have _ := ha
  rw [← zpow_natCast, x.ord_zpow]

private theorem k1le_thetaJ_ne_zero (F : Type) [Field F] [CharP F 3] : ModularCurve.thetaJ F ≠ 0 := by
  have hθ : ModularCurve.thetaJ F = -ModularCurve.jqModC F := k1le_thetaL_jqModC_eq_neg F
  rw [hθ, neg_ne_zero]
  exact ModularCurve.jqModC_ne_zero_def F

private theorem k1le_ord_bound (N' : ℕ) [NeZero N'] (F : Type) [Field F] [CharP F 3] (m : ℕ)
    (G : ↥(ModularCurve.modularFunctionFieldC F N')) (hG0 : G ≠ 0)
    (hfn : ModularCurve.IsModPFormFn F m (G : LaurentSeries F))
    (x : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N'))
    (hx : 0 < x.ord (ModularCurve.jGeomGen F N')) :
    0 ≤ 6 * x.ord G + 7 * (m : ℤ) * x.ord (ModularCurve.jGeomGen F N') := by
  have hjne : ModularCurve.jqModC F ≠ 0 := ModularCurve.jqModC_ne_zero_def F
  have hj0 : ModularCurve.jGeomGen F N' ≠ 0 := by
    intro h
    apply hjne
    have h' := congrArg (fun y : ↥(ModularCurve.modularFunctionFieldC F N') => (y : LaurentSeries F)) h
    simpa using h'
  have h1728 : algebraMap F (LaurentSeries F) (1728 : F) = 0 := by rw [k1le_char F, map_zero]
  unfold ModularCurve.IsModPFormFn at hfn
  obtain ⟨h1, -⟩ := hfn
  simp only [h1728, sub_zero] at h1
  have hY : IsIntegral
      (Algebra.adjoin F ({ModularCurve.jGeomGen F N'} : Set ↥(ModularCurve.modularFunctionFieldC F N')))
      (G ^ 6 * ModularCurve.jGeomGen F N' ^ (4 * m) * ModularCurve.jGeomGen F N' ^ (3 * m)) := by
    apply k1le_isIntegral_of_coe
    push_cast
    exact h1
  have hYord := x.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg hY hx.le
  rw [x.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hj0),
    x.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), k1le_ord_pow x hG0, k1le_ord_pow x hj0, k1le_ord_pow x hj0]
    at hYord
  push_cast at hYord
  linarith

private theorem k1le_residue_eq_zero {K E : Type*} [Field K] [Field E] [Algebra K E] (x : AlgebraicCurve.Place K E)
    (f : E) (hf : 1 ≤ x.ord f) (hmem : f ∈ x.toValuationSubring) :
    IsLocalRing.residue x.toValuationSubring ⟨f, hmem⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hv : x.adicValuation f = 1 := (x.adicValuation_coe_eq_one_iff ⟨f, hmem⟩).2 hu
  have h0 : x.ord f = 0 := by simp [AlgebraicCurve.Place.ord, hv]
  omega

private theorem k1le_ord_uniformizer (N' : ℕ) [NeZero N'] (F : Type) [Field F] (x : ModularCurve.ssPlaces3 F N') :
    x.1.ord (ModularCurve.SSCarrier3.uniformizer x) = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.1.toValuationSubring
  unfold ModularCurve.SSCarrier3.uniformizer
  exact Classical.epsilon_spec
    (⟨(π : ↥(ModularCurve.modularFunctionFieldC F N')), x.1.ord_coe_irreducible hπ⟩ :
      ∃ ϖ : ↥(ModularCurve.modularFunctionFieldC F N'), x.1.ord ϖ = 1)

private theorem k1le_branch (N' : ℕ) [NeZero N'] (F : Type) [Field F] [CharP F 3] (m : ℕ)
    (x : ModularCurve.ssPlaces3 F N') (g : ↥(ModularCurve.modularFunctionFieldC F N'))
    (hfn : ModularCurve.IsModPFormFn F m (g : LaurentSeries F))
    (hmem : g * ModularCurve.SSCarrier3.uniformizer x ^ (ModularCurve.SSCarrier3.aPole m x).toNat ∈
      x.1.toValuationSubring) :
    IsLocalRing.residue x.1.toValuationSubring ⟨_, hmem⟩ = 0 := by
  by_cases hg : g = 0
  · subst hg
    have h0 : (⟨_, hmem⟩ : x.1.toValuationSubring) = 0 := Subtype.ext (by simp)
    rw [h0, map_zero]
  · apply k1le_residue_eq_zero
    have hπ1 := k1le_ord_uniformizer N' F x
    have hπ0 : ModularCurve.SSCarrier3.uniformizer x ≠ 0 := by
      intro h0
      rw [h0, x.1.ord_zero] at hπ1
      exact zero_ne_one hπ1
    have hA : 0 ≤ 7 * (m : ℤ) * x.1.ord (ModularCurve.jGeomGen F N') :=
      mul_nonneg (mul_nonneg (by norm_num) (Int.natCast_nonneg m)) x.2.le
    have hbound := k1le_ord_bound N' F m g hg hfn x.1 x.2
    have hn : (((ModularCurve.SSCarrier3.aPole m x).toNat : ℕ) : ℤ) = ModularCurve.SSCarrier3.aPole m x := by
      apply Int.toNat_of_nonneg
      unfold ModularCurve.SSCarrier3.aPole
      omega
    rw [x.1.ord_mul hg (pow_ne_zero _ hπ0), k1le_ord_pow x.1 hπ0, hπ1, mul_one, hn]
    unfold ModularCurve.SSCarrier3.aPole
    omega

private theorem e3_mem_of_ord_nonneg {K E : Type*} [Field K] [Field E] [Algebra K E]
    (x : AlgebraicCurve.Place K E) {f : E} (hf : 0 ≤ x.ord f) : f ∈ x.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
  obtain ⟨u, hu⟩ := x.exists_unit_mul_zpow hf0 hπ
  rw [hu]
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hf
  rw [hn, zpow_natCast]
  exact mul_mem (u : x.toValuationSubring).2 (pow_mem π.2 n)

private theorem e3_aPole_nonneg (N' : ℕ) [NeZero N'] (F : Type) [Field F] (m : ℕ)
    (x : ModularCurve.ssPlaces3 F N') : 0 ≤ ModularCurve.SSCarrier3.aPole m x := by
  unfold ModularCurve.SSCarrier3.aPole
  have hA : 0 ≤ 7 * (m : ℤ) * x.1.ord (ModularCurve.jGeomGen F N') :=
    mul_nonneg (mul_nonneg (by norm_num) (Int.natCast_nonneg m)) x.2.le
  omega

private theorem e3_weight_two_ord_ge_one (L : ℕ) [NeZero L] (F : Type) [Field F] [CharP F 3]
    (G : ↥(ModularCurve.modularFunctionFieldC F L)) (hG0 : G ≠ 0)
    (hfn : ModularCurve.IsModPFormFn F 1 (G : LaurentSeries F))
    (x : ModularCurve.ssPlaces3 F L) :
    1 ≤ x.1.ord (G * ModularCurve.SSCarrier3.uniformizer x ^
      (ModularCurve.SSCarrier3.aPole 1 x).toNat) := by
  have hπ1 := k1le_ord_uniformizer L F x
  have hπ0 : ModularCurve.SSCarrier3.uniformizer x ≠ 0 := by
    intro h0
    rw [h0, x.1.ord_zero] at hπ1
    exact zero_ne_one hπ1
  have hbound := k1le_ord_bound L F 1 G hG0 hfn x.1 x.2
  have hn : (((ModularCurve.SSCarrier3.aPole 1 x).toNat : ℕ) : ℤ) =
      ModularCurve.SSCarrier3.aPole 1 x :=
    Int.toNat_of_nonneg (e3_aPole_nonneg L F 1 x)
  rw [x.1.ord_mul hG0 (pow_ne_zero _ hπ0), k1le_ord_pow x.1 hπ0, hπ1, mul_one, hn]
  unfold ModularCurve.SSCarrier3.aPole
  push_cast
  omega

private theorem e3_weight_two_mem_and_residue_zero (L : ℕ) [NeZero L] (F : Type) [Field F]
    [CharP F 3] (G : ↥(ModularCurve.modularFunctionFieldC F L))
    (hfn : ModularCurve.IsModPFormFn F 1 (G : LaurentSeries F))
    (x : ModularCurve.ssPlaces3 F L) :
    ∃ hmem : G * ModularCurve.SSCarrier3.uniformizer x ^
        (ModularCurve.SSCarrier3.aPole 1 x).toNat ∈ x.1.toValuationSubring,
      IsLocalRing.residue x.1.toValuationSubring ⟨_, hmem⟩ = 0 := by
  have hmem : G * ModularCurve.SSCarrier3.uniformizer x ^
      (ModularCurve.SSCarrier3.aPole 1 x).toNat ∈ x.1.toValuationSubring := by
    by_cases hG0 : G = 0
    · rw [hG0, zero_mul]
      exact zero_mem _
    · refine e3_mem_of_ord_nonneg x.1 ?_
      have h1 := e3_weight_two_ord_ge_one L F G hG0 hfn x
      omega
  exact ⟨hmem, k1le_branch L F 1 x G hfn hmem⟩

private theorem e3_witness_unique {L : ℕ} [NeZero L] {F : Type} [Field F] [CharP F 3] (m : ℕ)
    {G₁ G₂ : ↥(ModularCurve.modularFunctionFieldC F L)}
    (h : (G₁ : LaurentSeries F) * ModularCurve.thetaJ F ^ m =
      (G₂ : LaurentSeries F) * ModularCurve.thetaJ F ^ m) :
    G₁ = G₂ := by
  apply Subtype.ext
  exact mul_right_cancel₀ (pow_ne_zero m (k1le_thetaJ_ne_zero F)) h

open ModularCurve ModularCurve.SSCarrier3 in

private theorem e3_res_one_add_eq_of_mem_modPMod_two
    (L : ℕ) [NeZero L] (hpL : ¬ 3 ∣ L) (F : Type) [Field F] [CharP F 3]
    (φ ψ : PowerSeries F) (hψ : ψ ∈ ModPForms.modPMod L 2 F) (x : ssPlaces3 F L) :
    res 1 (φ + ψ) x = res 1 φ x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

  have hψ' : ψ ∈ ModPForms.modPMod L (2 * ((1:ℕ):ℤ)) F := by simpa using hψ
  obtain ⟨Gψ, hfnψ, hqψ⟩ :=
    ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod 3 L hpL F 1 ψ hψ'
  have hqψ' : (Gψ : LaurentSeries F) * thetaJ F ^ 1 = HahnSeries.ofPowerSeries ℤ F ψ := by
    have h := hqψ
    unfold qexpOfWeight at h
    rwa [zpow_natCast] at h

  obtain ⟨hψmem, hψres⟩ := e3_weight_two_mem_and_residue_zero L F Gψ hfnψ x

  have hiff : (∃ G : ↥(modularFunctionFieldC F L),
        (G : LaurentSeries F) * thetaJ F ^ 1 = HahnSeries.ofPowerSeries ℤ F φ) ↔
      (∃ G : ↥(modularFunctionFieldC F L),
        (G : LaurentSeries F) * thetaJ F ^ 1 = HahnSeries.ofPowerSeries ℤ F (φ + ψ)) := by
    constructor
    · rintro ⟨G, hG⟩
      refine ⟨G + Gψ, ?_⟩
      have hcoe : ((G + Gψ : ↥(modularFunctionFieldC F L)) : LaurentSeries F) =
          (G : LaurentSeries F) + (Gψ : LaurentSeries F) := rfl
      rw [hcoe, add_mul, hG, hqψ', map_add]
    · rintro ⟨G, hG⟩
      refine ⟨G - Gψ, ?_⟩
      push_cast
      rw [sub_mul, hqψ', hG, map_add, add_sub_cancel_right]

  unfold res
  by_cases hφ : ∃ G : ↥(modularFunctionFieldC F L),
      (G : LaurentSeries F) * thetaJ F ^ 1 = HahnSeries.ofPowerSeries ℤ F φ
  · have hφψ := hiff.mp hφ
    rw [dif_pos hφ, dif_pos hφψ]

    have hch : Classical.choose hφψ = Classical.choose hφ + Gψ := by
      apply e3_witness_unique 1
      rw [Classical.choose_spec hφψ]
      have hcoe : ((Classical.choose hφ + Gψ : ↥(modularFunctionFieldC F L)) : LaurentSeries F) =
          ((Classical.choose hφ : ↥(modularFunctionFieldC F L)) : LaurentSeries F) +
            (Gψ : LaurentSeries F) := rfl
      rw [hcoe, add_mul, Classical.choose_spec hφ, hqψ', map_add]

    set πa := uniformizer x ^ (aPole 1 x).toNat
    have hmiff : Classical.choose hφψ * πa ∈ x.1.toValuationSubring ↔
        Classical.choose hφ * πa ∈ x.1.toValuationSubring := by
      rw [hch, add_mul]
      constructor
      · intro hh
        have h' : Classical.choose hφ * πa = Classical.choose hφ * πa + Gψ * πa - Gψ * πa := by ring
        rw [h']; exact sub_mem hh hψmem
      · intro hh
        exact add_mem hh hψmem
    by_cases hmφ : Classical.choose hφ * πa ∈ x.1.toValuationSubring
    · rw [dif_pos (hmiff.mpr hmφ), dif_pos hmφ]

      have hsplit : (⟨_, hmiff.mpr hmφ⟩ : x.1.toValuationSubring) =
          ⟨_, hmφ⟩ + ⟨_, hψmem⟩ := by
        apply Subtype.ext
        simp only [AddMemClass.mk_add_mk]
        rw [hch, add_mul]
      rw [hsplit, map_add, hψres, add_zero]
    · rw [dif_neg (hmiff.not.mpr hmφ), dif_neg hmφ]
  · rw [dif_neg hφ, dif_neg (hiff.not.mp hφ)]

private def e2_t (D n : ℕ) : ℤ :=
  if D ∣ n then ((ArithmeticFunction.sigma 1 (n / D) : ℕ) : ℤ) else 0

private def e2_b (d n : ℕ) : ℤ :=
  if n = 0 then ((d : ℤ) - 2) / 3 else 8 * (2 * e2_t 2 n - (d : ℤ) * e2_t d n)

private theorem e2_coeff_bSer (F : Type) [Field F] (d n : ℕ) :
    PowerSeries.coeff n (bSer F d) =
      ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) - e2_t d n : ℤ) : F) := by
  simp only [bSer, PowerSeries.coeff_mk, e2_t]

private theorem e2_t_of_not_dvd {D n : ℕ} (h : ¬ D ∣ n) : e2_t D n = 0 := by
  unfold e2_t
  rw [if_neg h]

private theorem e2_t_mul_left (D m : ℕ) (hD : 0 < D) :
    e2_t D (D * m) = ((ArithmeticFunction.sigma 1 m : ℕ) : ℤ) := by
  unfold e2_t
  rw [if_pos (dvd_mul_right D m), Nat.mul_div_cancel_left m hD]

private theorem e2_sum_divisors_filter_dvd (D n : ℕ) (hD : 0 < D) (hn : n ≠ 0) :
    (∑ e ∈ n.divisors.filter (fun e => D ∣ e), (e : ℤ)) = (D : ℤ) * e2_t D n := by
  by_cases hDn : D ∣ n
  · obtain ⟨m, rfl⟩ := hDn
    rw [e2_t_mul_left D m hD, ArithmeticFunction.sigma_one_apply, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_nbij' (fun e => e / D) (fun c => D * c) ?_ ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter, Nat.mem_divisors] at he
      obtain ⟨⟨hem, -⟩, c, rfl⟩ := he
      show D * c / D ∈ m.divisors
      rw [Nat.mul_div_cancel_left c hD, Nat.mem_divisors]
      exact ⟨Nat.dvd_of_mul_dvd_mul_left hD hem, fun h => hn (by rw [h, mul_zero])⟩
    · intro c hc
      rw [Nat.mem_divisors] at hc
      show D * c ∈ (D * m).divisors.filter (fun e => D ∣ e)
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.mul_dvd_mul_left D hc.1, hn⟩, dvd_mul_right D c⟩
    · intro e he
      simp only [Finset.mem_filter] at he
      show D * (e / D) = e
      exact Nat.mul_div_cancel' he.2
    · intro c _
      show D * c / D = c
      exact Nat.mul_div_cancel_left c hD
    · intro e he
      simp only [Finset.mem_filter] at he
      show (e : ℤ) = (D : ℤ) * ((e / D : ℕ) : ℤ)
      rw [← Nat.cast_mul, Nat.mul_div_cancel' he.2]
  · rw [e2_t_of_not_dvd hDn, mul_zero]
    refine Finset.sum_eq_zero ?_
    intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    exact absurd (he.2.trans he.1.1) hDn

private theorem e2_sigmaPrimeTo_eq (D n : ℕ) (hD : 0 < D) (hn : n ≠ 0) :
    ((ModularCurve.sigmaPrimeTo D n : ℕ) : ℤ) =
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) - (D : ℤ) * e2_t D n := by
  have hsplit : (∑ e ∈ n.divisors.filter (fun e => D ∣ e), (e : ℤ)) +
      (∑ e ∈ n.divisors.filter (fun e => ¬ D ∣ e), (e : ℤ)) = ∑ e ∈ n.divisors, (e : ℤ) :=
    Finset.sum_filter_add_sum_filter_not n.divisors (fun e => D ∣ e) (fun e => (e : ℤ))
  have hmult := e2_sum_divisors_filter_dvd D n hD hn
  unfold ModularCurve.sigmaPrimeTo
  rw [Nat.cast_sum, ArithmeticFunction.sigma_one_apply, Nat.cast_sum]
  linear_combination hsplit - hmult

private theorem e2_eisen_of_ne_zero (D : ℕ) (hD : 0 < D) {n : ℕ} (hn : n ≠ 0) :
    ModularCurve.eisensteinTwoCoeff D n =
      24 * (((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) - (D : ℤ) * e2_t D n) := by
  rw [ModularCurve.eisensteinTwoCoeff_of_ne_zero D hn, e2_sigmaPrimeTo_eq D n hD hn]

private theorem e2_t_mul (p m n : ℕ) :
    e2_t (p * m) n = if m ∣ n then e2_t p (n / m) else 0 := by
  by_cases hmn : m ∣ n
  · rw [if_pos hmn]
    by_cases hp : p ∣ n / m
    · have hpm : p * m ∣ n := by
        rw [mul_comm]
        exact (Nat.dvd_div_iff_mul_dvd hmn).mp hp
      unfold e2_t
      rw [if_pos hpm, if_pos hp, Nat.div_div_eq_div_mul, mul_comm m p]
    · have hpm : ¬ p * m ∣ n := fun h =>
        hp ((Nat.dvd_div_iff_mul_dvd hmn).mpr (by rwa [mul_comm] at h))
      rw [e2_t_of_not_dvd hpm, e2_t_of_not_dvd hp]
  · rw [if_neg hmn]
    have hpm : ¬ p * m ∣ n := fun h => hmn ((dvd_mul_left m p).trans h)
    exact e2_t_of_not_dvd hpm

private theorem e2_eisen_mul (p m : ℕ) (hp : 0 < p) (hm : 0 < m) (n : ℕ) :
    ModularCurve.eisensteinTwoCoeff (p * m) n =
      (m : ℤ) * (if m ∣ n then ModularCurve.eisensteinTwoCoeff p (n / m) else 0) +
        ModularCurve.eisensteinTwoCoeff m n := by
  by_cases hn : n = 0
  · subst hn
    rw [if_pos (dvd_zero m), Nat.zero_div]
    simp only [ModularCurve.eisensteinTwoCoeff_zero]
    push_cast
    ring
  · rw [e2_eisen_of_ne_zero (p * m) (mul_pos hp hm) hn, e2_eisen_of_ne_zero m hm hn, e2_t_mul p m n]
    by_cases hmn : m ∣ n
    · obtain ⟨k, rfl⟩ := hmn
      have hk : k ≠ 0 := fun h => hn (by rw [h, mul_zero])
      rw [if_pos (dvd_mul_right m k), if_pos (dvd_mul_right m k), Nat.mul_div_cancel_left k hm,
        e2_eisen_of_ne_zero p hp hk, e2_t_mul_left m k hm]
      push_cast
      ring
    · rw [if_neg hmn, if_neg hmn, e2_t_of_not_dvd hmn]
      ring

private theorem e2_one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp

private theorem e2_qCoeff_add {N : ℕ} {k : ℤ} (f g : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (n : ℕ) :
    ModularFormClass.qCoeff ((f + g : ModularForm (CongruenceSubgroup.Gamma0 N) k) : UpperHalfPlane → ℂ) n =
      ModularFormClass.qCoeff f n + ModularFormClass.qCoeff g n := by
  have h := ModularForm.qExpansion_add one_pos (e2_one_mem_strictPeriods N) f g
  simp [ModularFormClass.qCoeff, h]

private theorem e2_qCoeff_sub {N : ℕ} {k : ℤ} (f g : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (n : ℕ) :
    ModularFormClass.qCoeff ((f - g : ModularForm (CongruenceSubgroup.Gamma0 N) k) : UpperHalfPlane → ℂ) n =
      ModularFormClass.qCoeff f n - ModularFormClass.qCoeff g n := by
  have h := ModularForm.qExpansion_sub one_pos (e2_one_mem_strictPeriods N) f g
  simp [ModularFormClass.qCoeff, h]

private theorem e2_qCoeff_smul {N : ℕ} {k : ℤ} (a : ℂ) (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (n : ℕ) :
    ModularFormClass.qCoeff ((a • f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : UpperHalfPlane → ℂ) n =
      a * ModularFormClass.qCoeff f n := by
  have h := ModularForm.qExpansion_smul one_pos (e2_one_mem_strictPeriods N) a f
  simp [ModularFormClass.qCoeff, h]

private theorem e2_qParam_heckeDiag {d : ℕ} (hd : d ≠ 0) (τ : UpperHalfPlane) :
    Function.Periodic.qParam 1 ((ModularForm.heckeDiagMatrix d • τ : UpperHalfPlane) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ d := by
  rw [ModularForm.coe_heckeDiagMatrix_smul hd]
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private theorem e2_exists_degeneracy_qCoeff {k : ℤ} {M N d : ℕ} [NeZero N] (hd : d * M ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 M) k) (a : ℕ → ℤ)
    (ha : ∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N) k,
      ∀ n, ModularFormClass.qCoeff g n = (((if d ∣ n then a (n / d) else 0 : ℤ) : ℤ) : ℂ) := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (zero_dvd_iff.mp (by simpa using hd))
  obtain ⟨g, hg⟩ := ModularForm.exists_degeneracy_Gamma0 (N := N) (M := M) (d := d) hd f
  have hΓM : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hΓN : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓM⟩
  have hf : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => ((a n : ℤ) : ℂ) • Function.Periodic.qParam 1 (τ : ℂ) ^ n) (f τ) := by
    intro τ
    have h := UpperHalfPlane.hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓM) (ModularFormClass.holo f)
      (ModularFormClass.bdd_at_infty f) τ
    have hfun : (fun n : ℕ => ((a n : ℤ) : ℂ) • Function.Periodic.qParam 1 (τ : ℂ) ^ n) =
        fun n : ℕ => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (⇑f)) •
          Function.Periodic.qParam 1 (τ : ℂ) ^ n := by
      funext n
      rw [← ha n]
      rfl
    rw [hfun]
    exact h
  have hg' : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ => (((if d ∣ n then a (n / d) else 0 : ℤ) : ℤ) : ℂ) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ n) (g τ) := by
    intro τ
    have hgτ : g τ = f (ModularForm.heckeDiagMatrix d • τ) := congrFun hg τ
    rw [hgτ]
    have h := hf (ModularForm.heckeDiagMatrix d • τ)
    simp only [e2_qParam_heckeDiag hd0, ← pow_mul] at h
    have hinj : Function.Injective (fun i : ℕ => d * i) := mul_right_injective₀ hd0
    refine (hinj.hasSum_iff ?_).mp ?_
    · intro n hn
      have hdn : ¬ d ∣ n := fun ⟨i, hi⟩ => hn ⟨i, hi.symm⟩
      simp [hdn]
    · convert h using 1
      funext i
      simp [Function.comp, Nat.mul_div_cancel_left i (Nat.pos_of_ne_zero hd0)]
  exact ⟨g, fun n => (ModularFormClass.qExpansion_coeff_unique one_pos hΓN hg' n).symm⟩

private theorem e2_exists_level_raise {k : ℤ} {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 M) k) (a : ℕ → ℤ)
    (ha : ∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N) k, ∀ n, ModularFormClass.qCoeff g n = (a n : ℂ) := by
  obtain ⟨g, hg⟩ := e2_exists_degeneracy_qCoeff (N := N) (M := M) (d := 1) (by rw [one_mul]; exact hMN)
    f a ha
  refine ⟨g, fun n => ?_⟩
  rw [hg n, if_pos (one_dvd n), Nat.div_one]

private theorem e2_cast_step (p m : ℕ) (hp : 0 < p) (hm : 0 < m) (n : ℕ) :
    (m : ℂ) * (((if m ∣ n then ModularCurve.eisensteinTwoCoeff p (n / m) else 0 : ℤ) : ℤ) : ℂ) +
        ((ModularCurve.eisensteinTwoCoeff m n : ℤ) : ℂ) =
      ((ModularCurve.eisensteinTwoCoeff (p * m) n : ℤ) : ℂ) := by
  exact_mod_cast (e2_eisen_mul p m hp hm n).symm

private theorem e2_exists_form : ∀ D : ℕ, 2 ≤ D →
    ∃ E : ModularForm (CongruenceSubgroup.Gamma0 D) 2,
      ∀ n, ModularFormClass.qCoeff E n = (ModularCurve.eisensteinTwoCoeff D n : ℂ) := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro hD2
    by_cases hprime : D.Prime
    · haveI : Fact D.Prime := ⟨hprime⟩
      exact ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff D
    · obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd (show D ≠ 1 by omega)
      obtain ⟨m, rfl⟩ := hpD
      have hp2 : 2 ≤ p := hp.two_le
      have hm2 : 2 ≤ m := by
        rcases m with _ | _ | m
        · omega
        · exact (hprime (by simpa using hp)).elim
        · omega
      have hmlt : m < p * m := by nlinarith [hp2, hm2]
      have hp0 : 0 < p := by omega
      have hm0 : 0 < m := by omega
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : NeZero (p * m) := ⟨(mul_pos hp0 hm0).ne'⟩
      obtain ⟨Ep, hEp⟩ := ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff p
      obtain ⟨Em, hEm⟩ := ih m hmlt hm2
      obtain ⟨gp, hgp⟩ := e2_exists_degeneracy_qCoeff (N := p * m) (M := p) (d := m)
        ⟨1, by ring⟩ Ep (ModularCurve.eisensteinTwoCoeff p) hEp
      obtain ⟨gm, hgm⟩ := e2_exists_level_raise (N := p * m) (dvd_mul_left m p) Em
        (ModularCurve.eisensteinTwoCoeff m) hEm
      refine ⟨(m : ℂ) • gp + gm, fun n => ?_⟩
      rw [e2_qCoeff_add, e2_qCoeff_smul, hgp n, hgm n]
      exact e2_cast_step p m hp0 hm0 n

private theorem e2_third (b e1 e2 : ℂ) (h3 : 3 * b = e1 - e2) : 3⁻¹ * (e1 - e2) = b := by
  linear_combination (-(3 : ℂ)⁻¹) * h3

private theorem e2_three_mul_b (d : ℕ) (hd2 : 2 ≤ d) (hd3 : d % 3 = 2) (n : ℕ) :
    3 * e2_b d n = ModularCurve.eisensteinTwoCoeff d n - ModularCurve.eisensteinTwoCoeff 2 n := by
  by_cases hn : n = 0
  · subst hn
    unfold e2_b
    rw [if_pos rfl]
    simp only [ModularCurve.eisensteinTwoCoeff_zero]
    push_cast
    omega
  · unfold e2_b
    rw [if_neg hn, e2_eisen_of_ne_zero d (by omega) hn, e2_eisen_of_ne_zero 2 (by norm_num) hn]
    push_cast
    ring

private theorem e2_coeff_identity (d c n : ℕ) (hc : d = 3 * c + 2) (hn : n ≠ 0) :
    (((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) - e2_t d n) -
        (((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) - e2_t 2 n) =
      e2_b d n + 3 * (-5 * e2_t 2 n + (8 * (c : ℤ) + 5) * e2_t d n) := by
  unfold e2_b
  rw [if_neg hn]
  have hdZ : (d : ℤ) = 3 * (c : ℤ) + 2 := by omega
  linear_combination (8 * e2_t d n) * hdZ

private theorem e2_cong_Bd_sub_B2_mem_modPMod_two
    (d : ℕ) (hd3 : d % 3 = 2) (F : Type) [Field F] [CharP F 3] :
    bSer F d - bSer F 2 ∈ ModPForms.modPMod (2 * d) 2 F := by
  have hd2 : 2 ≤ d := by omega
  haveI : NeZero (2 * d) := ⟨by omega⟩
  obtain ⟨Ed, hEd⟩ := e2_exists_form d hd2
  obtain ⟨E2, hE2⟩ := e2_exists_form 2 le_rfl
  obtain ⟨gd, hgd⟩ := e2_exists_level_raise (N := 2 * d) (dvd_mul_left d 2) Ed
    (ModularCurve.eisensteinTwoCoeff d) hEd
  obtain ⟨g2, hg2⟩ := e2_exists_level_raise (N := 2 * d) (dvd_mul_right 2 d) E2
    (ModularCurve.eisensteinTwoCoeff 2) hE2

  have hbcoeff : ∀ n, ModularFormClass.qCoeff
      (((3⁻¹ : ℂ) • (gd - g2) : ModularForm (CongruenceSubgroup.Gamma0 (2 * d)) 2) : UpperHalfPlane → ℂ) n =
        ((e2_b d n : ℤ) : ℂ) := by
    intro n
    rw [e2_qCoeff_smul, e2_qCoeff_sub, hgd n, hg2 n]
    have h3 : (3 : ℂ) * ((e2_b d n : ℤ) : ℂ) = ((ModularCurve.eisensteinTwoCoeff d n : ℤ) : ℂ) -
        ((ModularCurve.eisensteinTwoCoeff 2 n : ℤ) : ℂ) := by
      exact_mod_cast e2_three_mul_b d hd2 hd3 n
    exact e2_third _ _ _ h3

  have hbmem : (PowerSeries.mk fun n : ℕ => ((e2_b d n : ℤ) : F)) ∈ ModPForms.modPMod (2 * d) 2 F := by
    apply Submodule.subset_span
    exact ⟨(3⁻¹ : ℂ) • (gd - g2), e2_b d, hbcoeff, rfl⟩

  have hc1mem : (1 : PowerSeries F) ∈ ModPForms.modPMod (2 * d) 2 F := by
    apply ModPForms.one_mem_modPMod_two_of_exists_prime_dvd_mod_three_eq_two
    exact ⟨2, Nat.prime_two, ⟨d, rfl⟩, rfl⟩

  have h3F : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have h3Z : ((3 : ℤ) : F) = 0 := by exact_mod_cast h3F
  obtain ⟨c, hc⟩ : ∃ c : ℕ, d = 3 * c + 2 := ⟨d / 3, by omega⟩
  have heq : bSer F d - bSer F 2 =
      (PowerSeries.mk fun n : ℕ => ((e2_b d n : ℤ) : F)) - (((e2_b d 0 : ℤ) : F)) • (1 : PowerSeries F) := by
    ext n
    simp only [map_sub, e2_coeff_bSer, PowerSeries.coeff_mk, map_smul, PowerSeries.coeff_one, smul_eq_mul]
    by_cases hn : n = 0
    · subst hn
      simp [e2_t]
    · rw [if_neg hn, mul_zero, sub_zero, ← Int.cast_sub, e2_coeff_identity d c n hc hn, Int.cast_add,
        Int.cast_mul, h3Z, zero_mul, add_zero]
  rw [heq]
  exact Submodule.sub_mem _ hbmem (Submodule.smul_mem _ _ hc1mem)

#print axioms e3_res_one_add_eq_of_mem_modPMod_two
#print axioms e2_cong_Bd_sub_B2_mem_modPMod_two

end R3cK2ULegE

end LegE23

section K2UAssembly

private theorem k2u_exists_prime_dvd_mod_three_eq_two (d : ℕ) :
    d % 3 = 2 → ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ p % 3 = 2 := by
  induction d using induction_on_primes with
  | zero =>
    intro h
    exact absurd h (by decide)
  | one =>
    intro h
    exact absurd h (by decide)
  | prime_mul p a hp ih =>
    intro h
    have hmod : p * a % 3 = p % 3 * (a % 3) % 3 := Nat.mul_mod p a 3
    have hp3 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hp3 with hp0 | hp1 | hp2
    · exfalso
      rw [hp0, zero_mul, Nat.zero_mod] at hmod
      omega
    · rw [hp1, one_mul, Nat.mod_mod] at hmod
      obtain ⟨q, hq, hqa, hq3⟩ := ih (by omega)
      exact ⟨q, hq, Dvd.dvd.mul_left hqa p, hq3⟩
    · exact ⟨p, hp, Dvd.intro a rfl, hp2⟩

private theorem k2u_at_level (d : ℕ) (hd3 : d % 3 = 2) (F : Type) [Field F] [CharP F 3] [IsAlgClosed F]
    (M : ℕ) [NeZero M] (h3M : ¬ 3 ∣ M) (h2d : 2 * d ∣ M) :
    ∀ x : ModularCurve.ssPlaces3 F M, ModularCurve.SSCarrier3.res 1 (K2UE1.bSer F d) x ≠ 0 := by
  have hB2 : K2UE1.bSer F 2 ∈ ModPForms.modPMod 2 4 F :=
    ModPForms.mk_sigma_one_sub_sigma_one_div_mem_modPMod_four_of_dvd 2 2 dvd_rfl F
  have h1 := K2UE1.e1_forall_res_one_bSer_two_ne_zero F hB2
  have hε2 : ∃ p : ℕ, p.Prime ∧ p ∣ 2 ∧ p % 3 = 2 := ⟨2, Nat.prime_two, dvd_rfl, rfl⟩
  obtain ⟨r, hr⟩ : 2 ∣ M := dvd_trans (Dvd.intro d rfl) h2d
  haveI : NeZero (2 * r) := ⟨by rw [← hr]; exact NeZero.ne M⟩
  have h3r : ¬ 3 ∣ 2 * r := by
    rw [← hr]
    exact h3M
  have hclimb := e4_climb F (K2UE1.bSer F 2) r 2 hε2 hB2 h3r h1
  have hM := e4_transport F (K2UE1.bSer F 2) hr.symm hclimb
  have hE2 : K2UE1.bSer F d - K2UE1.bSer F 2 ∈ ModPForms.modPMod (2 * d) 2 F :=
    R3cK2ULegE.e2_cong_Bd_sub_B2_mem_modPMod_two d hd3 F
  have hψ : K2UE1.bSer F d - K2UE1.bSer F 2 ∈ ModPForms.modPMod M 2 F :=
    ModPForms.modPMod_le_modPMod_of_dvd (2 * d) M h2d 2 F hE2
  intro x
  have hEq := R3cK2ULegE.e3_res_one_add_eq_of_mem_modPMod_two M h3M F (K2UE1.bSer F 2)
    (K2UE1.bSer F d - K2UE1.bSer F 2) hψ x
  have hsum : K2UE1.bSer F 2 + (K2UE1.bSer F d - K2UE1.bSer F 2) = K2UE1.bSer F d := by abel
  rw [hsum] at hEq
  rw [hEq]
  exact hM x

end K2UAssembly

open ModPForms in
theorem solution
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (d : ℕ) (hd : d ∣ N') (hd3 : d % 3 = 2)
    (F : Type) [Field F] [CharP F 3] [IsAlgClosed F] :
    let B : PowerSeries F := PowerSeries.mk fun n : ℕ =>
      ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
        (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ) : F)
    B ∈ modPMod N' 4 F → ∀ x : ModularCurve.ssPlaces3 F N', ModularCurve.SSCarrier3.res 1 B x ≠ 0 := by
  intro B hB
  show ∀ x : ModularCurve.ssPlaces3 F N', ModularCurve.SSCarrier3.res 1 (K2UE1.bSer F d) x ≠ 0
  have hB' : K2UE1.bSer F d ∈ ModPForms.modPMod N' 4 F := hB
  have hε : ∃ p : ℕ, p.Prime ∧ p ∣ N' ∧ p % 3 = 2 := by
    obtain ⟨p, hp, hpd, hp3⟩ := k2u_exists_prime_dvd_mod_three_eq_two d hd3
    exact ⟨p, hp, dvd_trans hpd hd, hp3⟩
  by_cases h2d : 2 * d ∣ N'
  · exact k2u_at_level d hd3 F N' hpN' h2d
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h3 : ¬ 3 ∣ N' * 2 := by
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · exact hpN' h
      · omega
    have h2d' : 2 * d ∣ N' * 2 := by
      obtain ⟨c, hc⟩ := hd
      exact ⟨c, by rw [hc]; ring⟩
    exact (e4_leg N' 2 h3 hε F (K2UE1.bSer F d) hB').mpr (k2u_at_level d hd3 F (N' * 2) h3 h2d')

end S_ModPForms_res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed
end P2MW
export P2MW.S_ModPForms_res_one_ne_zero_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed (solution)
