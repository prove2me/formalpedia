-- Prove2me | solution 1 for ModPForms.modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/092ea912-82e8-52bd-a036-3c370a93e52c

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice
import Theorems.Thm_ModPForms_finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two
import Theorems.Thm_ModPForms_heckeU_mem_modPCusp_four_of_mem_modPCusp_mul_three_of_exists_prime_dvd_mod_three_eq_two
import Theorems.Thm_ModPForms_heckeU_mem_modPCusp_of_dvd
import Theorems.Thm_ModPForms_dimFormulaCusp_le_finrank_modPCusp
import Theorems.Thm_ModPForms_exists_isModPCuspFormFn_qexpOfWeight_eq_of_mem_modPCusp
import Theorems.Thm_ModularCurve_card_le_dimFormulaCusp_of_isModPCuspFormFn_of_linearIndependent_of_char_three
import Theorems.Thm_ModularCurve_mem_riemannRochSpace_iff_isModPCuspFormFn_of_forall_eq_weightFloor_sub
import Theorems.Thm_ModularCurve_ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub
import Theorems.Thm_ModularCurve_exists_divisor_forall_eq_weightFloor_fieldC
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_constantsAreBase_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_genusFormula_mul_expand
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_nuTwo_prime
import Theorems.Thm_ModularCurve_nuThree_prime
import Theorems.Thm_ModularCurve_cuspCount_prime
import Theorems.Thm_CuspForm_intLattice_free_and_finite
import Theorems.Thm_CuspForm_exists_addMonoidHom_intLattice_qCoeff_saturated
import Theorems.Thm_CuspForm_exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral
import Theorems.Thm_CuspForm_exists_int_mul_qCoeff_alSlash_of_mem_intLattice
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "instance" "ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase CuspForm.instSMulHeckeAlgebraNewLatticeRed CuspForm.instSMulWithZeroHeckeAlgebraNewLatticeRed CuspForm.instAddCommGroupNewLatticeRed CuspForm.instModuleHeckeAlgebraNewLatticeRed CuspForm.instDistribMulActionHeckeAlgebraNewLatticeRed CuspForm.instSMulHeckeAlgebraNewLattice CuspForm.instMulActionHeckeAlgebraNewLatticeRed CuspForm.instMulActionWithZeroHeckeAlgebraNewLatticeRed CuspForm.instModuleHeckeAlgebraNewLattice HeckeEis.instFiniteProjLineCusps HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.numberField_of_finiteDimensional"
p2m_attr_erase "simp" "ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero"
p2m_attr_erase "simp" "ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CuspForm.coe_traceLin_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero"
p2m_attr_erase "simp" "TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk"
p2m_attr_erase "simp" "HeckeEis.coeffCoboundaryMap_apply HeckeEis.coe_linePow ModularCurve.symPoly_zero ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

namespace ModPCuspWeightLevelAux

p2m_open "AlgebraicCurve~genus ModularCurve"

section Reductions

variable {M : ℕ} {k : ℤ}

private noncomputable def redMap (K : Type) [Field K]
    (a : ↥(CuspForm.intLattice M k) →+ (ℕ → ℤ)) : ↥(CuspForm.intLattice M k) →ₗ[ℤ] PowerSeries K :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun f => PowerSeries.mk fun n => ((a f n : ℤ) : K)
      map_zero' := by ext n; simp
      map_add' := fun f g => by ext n; simp }

@[scoped simp] private theorem coeff_redMap (K : Type) [Field K]
    (a : ↥(CuspForm.intLattice M k) →+ (ℕ → ℤ)) (f : ↥(CuspForm.intLattice M k)) (n : ℕ) :
    PowerSeries.coeff n (redMap K a f) = ((a f n : ℤ) : K) := by
  simp [redMap]

open scoped TensorProduct in

private theorem range_eq_modPCusp (K : Type) [Field K]
    (a : ↥(CuspForm.intLattice M k) →+ (ℕ → ℤ))
    (ha : ∀ (f : ↥(CuspForm.intLattice M k)) (n : ℕ),
      ((a f n : ℤ) : ℂ) = ModularFormClass.qCoeff (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) n) :
    LinearMap.range ((redMap K a).liftBaseChange K) = ModPForms.modPCusp M k K := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c f =>
      rw [LinearMap.liftBaseChange_tmul]
      refine Submodule.smul_mem _ c (Submodule.subset_span ⟨(f : CuspForm (CongruenceSubgroup.Gamma0 M) k),
        a f, fun n => (ha f n).symm, ?_⟩)
      ext n
      simp
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · rw [ModPForms.modPCusp, Submodule.span_le]
    rintro φ ⟨f, c, hc, rfl⟩
    have hf : f ∈ CuspForm.intLattice M k := Submodule.subset_span fun n => ⟨c n, hc n⟩
    refine ⟨(1 : K) ⊗ₜ ⟨f, hf⟩, ?_⟩
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    ext n
    rw [coeff_redMap, PowerSeries.coeff_mk]
    have h := (ha ⟨f, hf⟩ n).trans (hc n)
    exact_mod_cast congrArg (fun z : ℤ => (z : K)) (Int.cast_injective h)

open scoped TensorProduct in

private theorem finiteDimensional_modPCusp [NeZero M] (K : Type) [Field K] :
    FiniteDimensional K ↥(ModPForms.modPCusp M k K) := by
  obtain ⟨a, ha, -, -⟩ := CuspForm.exists_addMonoidHom_intLattice_qCoeff_saturated M k
  obtain ⟨-, hfin⟩ := CuspForm.intLattice_free_and_finite M k
  rw [← range_eq_modPCusp K a ha]
  infer_instance

end Reductions

section Descent

variable {F K : Type} [Field F] [Field K] [Algebra F K]

private theorem generators_eq_image (M : ℕ) (k : ℤ) :
    {ψ : PowerSeries K | ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) (a : ℕ → ℤ),
        (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ ψ = PowerSeries.mk fun n => ((a n : ℤ) : K)} =
      PowerSeries.map (algebraMap F K) ''
        {φ : PowerSeries F | ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) (a : ℕ → ℤ),
          (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : F)} := by
  ext ψ
  constructor
  · rintro ⟨f, a, hfa, rfl⟩
    refine ⟨PowerSeries.mk fun n => ((a n : ℤ) : F), ⟨f, a, hfa, rfl⟩, ?_⟩
    ext n
    simp [PowerSeries.coeff_map]
  · rintro ⟨φ, ⟨f, a, hfa, rfl⟩, rfl⟩
    refine ⟨f, a, hfa, ?_⟩
    ext n
    simp [PowerSeries.coeff_map]

private theorem modPCusp_eq_span_image (M : ℕ) (k : ℤ) :
    ModPForms.modPCusp M k K = Submodule.span K (PowerSeries.map (algebraMap F K) ''
        {φ : PowerSeries F | ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) (a : ℕ → ℤ),
          (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : F)}) := by
  rw [ModPForms.modPCusp, generators_eq_image (F := F) M k]

private theorem mem_span_of_map_mem_span {S : Set (PowerSeries F)} {φ : PowerSeries F}
    (h : PowerSeries.map (algebraMap F K) φ ∈ Submodule.span K (PowerSeries.map (algebraMap F K) '' S)) :
    φ ∈ Submodule.span F S := by

  have hinj : Function.Injective (Algebra.linearMap F K) := fun x y hxy => (algebraMap F K).injective hxy
  obtain ⟨π, hπ⟩ := (Algebra.linearMap F K).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  have hπ1 : ∀ x : F, π (algebraMap F K x) = x := fun x => by
    simpa using LinearMap.congr_fun hπ x

  let Pc : PowerSeries K →+ PowerSeries F :=
    { toFun := fun ψ => PowerSeries.mk fun n => π (PowerSeries.coeff n ψ)
      map_zero' := by ext n; simp
      map_add' := fun ψ χ => by ext n; simp }
  have hPc : ∀ ψ n, PowerSeries.coeff n (Pc ψ) = π (PowerSeries.coeff n ψ) := fun ψ n => by
    simp [Pc]
  have key : ∀ ψ ∈ Submodule.span K (PowerSeries.map (algebraMap F K) '' S), ∀ c : K,
      Pc (c • ψ) ∈ Submodule.span F S := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      intro c
      have hc : Pc (c • PowerSeries.map (algebraMap F K) g) = π c • g := by
        ext n
        rw [hPc, PowerSeries.coeff_smul, PowerSeries.coeff_map, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul,
          mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
      rw [hc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hg)
    | zero => intro c; rw [smul_zero, map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => intro c; rw [smul_add, map_add]; exact Submodule.add_mem _ (hx c) (hy c)
    | smul d x _ hx => intro c; rw [smul_smul]; exact hx (c * d)
  have hφ : Pc (PowerSeries.map (algebraMap F K) φ) = φ := by
    ext n
    rw [hPc, PowerSeries.coeff_map, hπ1]
  have h1 := key _ h 1
  rw [one_smul, hφ] at h1
  exact h1

end Descent

section Arithmetic

private theorem nuThree_eq_zero {N : ℕ} (hq : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2) : nuThree N = 0 := by
  obtain ⟨q, hq, hqN, hq2⟩ := hq
  have hq3 : q ≠ 3 := by rintro rfl; norm_num at hq2
  have hzero : nuThree q = 0 := by rw [nuThree_prime hq hq3, if_neg (by omega)]
  rw [nuThree] at hzero ⊢
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hfin : Finite {x : ZMod q // x ^ 2 + x + 1 = 0} := inferInstance
  have hemp : IsEmpty {x : ZMod q // x ^ 2 + x + 1 = 0} :=
    (Nat.card_eq_zero.mp hzero).resolve_right (not_infinite_iff_finite.mpr hfin)
  refine Nat.card_eq_zero.mpr (Or.inl ⟨fun x => hemp.false ⟨ZMod.castHom hqN (ZMod q) x.1, ?_⟩⟩)
  have h := congrArg (ZMod.castHom hqN (ZMod q)) x.2
  rw [map_add, map_add, map_pow, map_one, map_zero] at h
  exact h

private theorem four_mul_add_nuTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (4 : ℚ) * (((p + 1) / 4 : ℕ) : ℚ) + (nuTwo p : ℚ) = p + 1 := by
  rw [nuTwo_prime hp hp2]
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  by_cases h4 : p % 4 = 1
  · rw [if_pos h4]
    have h : 4 * ((p + 1) / 4) + 2 = p + 1 := by omega
    exact_mod_cast h
  · rw [if_neg h4]
    have h : 4 * ((p + 1) / 4) + 0 = p + 1 := by omega
    exact_mod_cast h

private theorem three_mul_add_nuThree {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    (3 : ℚ) * (((p + 1) / 3 : ℕ) : ℚ) + (nuThree p : ℚ) = p + 1 := by
  rw [nuThree_prime hp hp3]
  have h0 : p % 3 ≠ 0 := fun h =>
    hp3 (((hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)).resolve_left (by norm_num)).symm)
  by_cases h1 : p % 3 = 1
  · rw [if_pos h1]
    have h : 3 * ((p + 1) / 3) + 2 = p + 1 := by omega
    exact_mod_cast h
  · rw [if_neg h1]
    have h : 3 * ((p + 1) / 3) + 0 = p + 1 := by omega
    exact_mod_cast h

private theorem genusFormula_mul_sub {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : N ≠ 0) (hpN : ¬ p ∣ N)
    (h3 : p = 3 → nuThree N = 0) :
    genusFormula (N * p) - genusFormula N =
      (p : ℚ) * (genusFormula N - 1) + (((p + 1) / 4 : ℕ) : ℚ) * (nuTwo N : ℚ)
        + (((p + 1) / 3 : ℕ) : ℚ) * (nuThree N : ℚ) + (((p : ℚ) - 1) / 2) * (cuspCount N : ℚ) := by
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  have hexp := genusFormula_mul_expand hp.ne_zero hN hcop
  rw [dedekindPsi_prime hp, cuspCount_prime hp] at hexp
  push_cast at hexp
  rw [Nat.mul_comm N p]
  have hg : genusFormula N = 1 + (dedekindPsi N : ℚ) / 12 - (nuTwo N : ℚ) / 4 - (nuThree N : ℚ) / 3
      - (cuspCount N : ℚ) / 2 := rfl
  have h2 := four_mul_add_nuTwo hp hp2
  by_cases hp3 : p = 3
  · have hν : (nuThree N : ℚ) = 0 := by exact_mod_cast h3 hp3
    linear_combination hexp + (1 - (p : ℚ)) * hg - ((nuTwo N : ℚ) / 4) * h2
      + ((((p : ℚ) + 1 - (nuThree p : ℚ)) / 3) - (((p + 1) / 3 : ℕ) : ℚ)) * hν
  · have h3' := three_mul_add_nuThree hp hp3
    linear_combination hexp + (1 - (p : ℚ)) * hg - ((nuTwo N : ℚ) / 4) * h2 - ((nuThree N : ℚ) / 3) * h3'

private noncomputable def dimF (N m : ℕ) : ℚ :=
  (2 * (m : ℚ) - 1) * (genusFormula N - 1) + ((m / 2 : ℕ) : ℚ) * (nuTwo N : ℚ)
    + ((2 * m / 3 : ℕ) : ℚ) * (nuThree N : ℚ) + ((m : ℚ) - 1) * (cuspCount N : ℚ) + (if m = 1 then 1 else 0)

private theorem dimF_one (N : ℕ) : dimF N 1 = genusFormula N := by
  norm_num [dimF]

private theorem dimF_succ_div_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) :
    dimF N ((p + 1) / 2) =
      (p : ℚ) * (genusFormula N - 1) + (((p + 1) / 4 : ℕ) : ℚ) * (nuTwo N : ℚ)
        + (((p + 1) / 3 : ℕ) : ℚ) * (nuThree N : ℚ) + (((p : ℚ) - 1) / 2) * (cuspCount N : ℚ) := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have h2m : 2 * ((p + 1) / 2) = p + 1 := by omega
  have hm1 : (p + 1) / 2 ≠ 1 := by have := hp.two_le; omega
  have hdiv4 : (p + 1) / 2 / 2 = (p + 1) / 4 := by omega
  have hdiv3 : 2 * ((p + 1) / 2) / 3 = (p + 1) / 3 := by rw [h2m]
  have hcast : (((p + 1) / 2 : ℕ) : ℚ) = ((p : ℚ) + 1) / 2 := by
    have h : (2 : ℚ) * (((p + 1) / 2 : ℕ) : ℚ) = p + 1 := by exact_mod_cast h2m
    linarith
  rw [dimF, if_neg hm1, hdiv4, hdiv3, hcast]
  ring

end Arithmetic

section UpperBound

variable (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (K : Type) [Field K] [CharP K p]
  [IsAlgClosed K]

omit [IsAlgClosed K] in

private theorem linearIndependent_of_qexpOfWeight_eq (S : IntermediateField K (LaurentSeries K)) (k : ℤ)
    {ι : Type} [Fintype ι] (φ : ι → PowerSeries K) (hli : LinearIndependent K φ) (G : ι → ↥S)
    (hq : ∀ i, qexpOfWeight K k (G i : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K (φ i)) :
    LinearIndependent K G := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcL : ∑ i, HahnSeries.ofPowerSeries ℤ K (PowerSeries.C (c i)) * (G i : LaurentSeries K) = 0 := by
    have h := congrArg S.val hc
    rw [map_sum, map_zero] at h
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h
    have hsd : c i • G i = algebraMap K ↥S (c i) * G i := Algebra.smul_def (c i) (G i)
    rw [hsd, map_mul]
    rfl
  have hsum : HahnSeries.ofPowerSeries ℤ K (∑ i, c i • φ i) = HahnSeries.ofPowerSeries ℤ K 0 := by
    have h1 : (∑ i, HahnSeries.ofPowerSeries ℤ K (PowerSeries.C (c i)) * (G i : LaurentSeries K)) * thetaJ K ^ k
        = 0 := by
      rw [hcL, zero_mul]
    rw [Finset.sum_mul] at h1
    rw [map_zero, map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h1
    rw [PowerSeries.smul_eq_C_mul, map_mul, mul_assoc, ← hq i]
    rfl
  exact Fintype.linearIndependent_iff.mp hli c (HahnSeries.ofPowerSeries_injective hsum)

include hpN in
private theorem card_le_dimF (m : ℕ) (hm : 1 ≤ m) (hp : (p = 3 ∧ nuThree N = 0) ∨ 5 ≤ p)
    {ι : Type} [Fintype ι] (φ : ι → PowerSeries K) (hφ : ∀ i, φ i ∈ ModPForms.modPCusp N (2 * (m : ℤ)) K)
    (hli : LinearIndependent K φ) : (Fintype.card ι : ℚ) ≤ dimF N m := by
  choose G hG hq using fun i =>
    ModPForms.exists_isModPCuspFormFn_qexpOfWeight_eq_of_mem_modPCusp p N hpN K m (φ i) (hφ i)

  have hliGC : LinearIndependent K G :=
    linearIndependent_of_qexpOfWeight_eq K (modularFunctionFieldC K N) (m : ℤ) φ hli G hq
  rcases hp with ⟨rfl, hν⟩ | hp5
  · have hle := modularFunctionFieldC_le_full K N
    have hli' : LinearIndependent K
        (fun i => (⟨(G i : LaurentSeries K), hle (G i).2⟩ : ↥(modularFunctionFieldFullC K N))) :=
      linearIndependent_of_qexpOfWeight_eq K (modularFunctionFieldFullC K N) (m : ℤ) φ hli
        (fun i => (⟨(G i : LaurentSeries K), hle (G i).2⟩ : ↥(modularFunctionFieldFullC K N))) (fun i => hq i)
    exact card_le_dimFormulaCusp_of_isModPCuspFormFn_of_linearIndependent_of_char_three N hpN hν K m hm
      (fun i => (⟨(G i : LaurentSeries K), hle (G i).2⟩ : ↥(modularFunctionFieldFullC K N))) (fun i => hG i) hli'
  · haveI : IsCurveOver K ↥(modularFunctionFieldC K N) := isCurveOver_modularFunctionFieldC_of_perfectField K N
    have hCB := constantsAreBase_modularFunctionFieldC_of_perfectField K N
    haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K ↥(modularFunctionFieldC K N))) :=
      Module.finite_of_finrank_pos (by
        rw [show Module.finrank K ↥(LSpace (0 : Divisor K ↥(modularFunctionFieldC K N)))
            = ell (0 : Divisor K ↥(modularFunctionFieldC K N)) from rfl, ell_zero_eq_one_of_constantsAreBase hCB]
        exact Nat.one_pos)
    obtain ⟨D, hD⟩ := exists_divisor_forall_eq_weightFloor_fieldC K N m
    obtain ⟨E, hE⟩ : ∃ E : Divisor K ↥(modularFunctionFieldC K N), ∀ w : Place K ↥(modularFunctionFieldC K N),
        E w = weightFloor K N m w - (if w.ord (jGeomGen K N) < 0 then 1 else 0) := by
      by_cases hj : jGeomGen K N = 0
      · refine ⟨D, fun w => ?_⟩
        rw [hD, hj, Place.ord_zero]
        simp
      · obtain ⟨Dj, hDj, -⟩ :=
          (hasPrincipalDivisors_modularFunctionFieldC_of_perfectField K N).exists_divisor _ hj
        refine ⟨D - Dj.mapRange (fun z => if z < 0 then (1 : ℤ) else 0) (by simp), fun w => ?_⟩
        rw [Finsupp.sub_apply, Finsupp.mapRange_apply, hD, hDj]
    haveI : FiniteDimensional K ↥(LSpace E) := finiteDimensional_lSpace E
    have hmem : ∀ i, G i ∈ riemannRochSpace E := fun i =>
      (mem_riemannRochSpace_iff_isModPCuspFormFn_of_forall_eq_weightFloor_sub p hp5 N hpN K m hm E hE
        (G i)).mpr (hG i)
    have hli3 : LinearIndependent K (fun i => (⟨G i, hmem i⟩ : ↥(riemannRochSpace E))) :=
      LinearIndependent.of_comp (riemannRochSpace E).subtype hliGC
    have hcard : Fintype.card ι ≤ Module.finrank K ↥(LSpace E) := hli3.fintype_card_le_finrank
    calc (Fintype.card ι : ℚ) ≤ (ell E : ℚ) := by exact_mod_cast hcard
      _ ≤ dimF N m := ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub p hp5 N hpN K m hm E hE

include hpN in
private theorem finrank_le_dimF (m : ℕ) (hm : 1 ≤ m) (hp : (p = 3 ∧ nuThree N = 0) ∨ 5 ≤ p) :
    (Module.finrank K ↥(ModPForms.modPCusp N (2 * (m : ℤ)) K) : ℚ) ≤ dimF N m := by
  haveI := finiteDimensional_modPCusp (M := N) (k := 2 * (m : ℤ)) K
  let b := Module.finBasis K ↥(ModPForms.modPCusp N (2 * (m : ℤ)) K)
  have hlib : LinearIndependent K (fun i => (b i : PowerSeries K)) :=
    b.linearIndependent.map' (ModPForms.modPCusp N (2 * (m : ℤ)) K).subtype (Submodule.ker_subtype _)
  have h := card_le_dimF p N hpN K m hm hp (fun i => (b i : PowerSeries K)) (fun i => (b i).2) hlib
  rw [Fintype.card_fin] at h
  exact h

end UpperBound

section Lowering

private theorem heckeU_mem_modPCusp (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (hq3 : p = 3 → ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2) (K : Type) [Field K] [CharP K p]
    (φ : PowerSeries K) (hφ : φ ∈ ModPForms.modPCusp (N * p) 2 K) :
    PowerSeries.heckeU p φ ∈ ModPForms.modPCusp N ((p : ℤ) + 1) K := by
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  by_cases hp3 : p = 3
  · subst hp3
    have h4 : ((3 : ℕ) : ℤ) + 1 = 4 := by norm_num
    rw [h4]
    exact ModPForms.heckeU_mem_modPCusp_four_of_mem_modPCusp_mul_three_of_exists_prime_dvd_mod_three_eq_two N hpN
      (hq3 rfl) K φ hφ
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  haveI : NeZero (N * p) := ⟨Nat.mul_ne_zero (NeZero.ne N) hp0⟩
  suffices hle : ModPForms.modPCusp (N * p) 2 K ≤
      (ModPForms.modPCusp N ((p : ℤ) + 1) K).comap
        (PowerSeries.heckeU p : PowerSeries K →ₗ[K] PowerSeries K) from hle hφ
  rw [ModPForms.modPCusp, Submodule.span_le]
  rintro _ ⟨f, a, hfa, rfl⟩
  show PowerSeries.heckeU p (PowerSeries.mk fun n => ((a n : ℤ) : K)) ∈ ModPForms.modPCusp N ((p : ℤ) + 1) K
  have hf : f ∈ CuspForm.intLattice (N * p) 2 := Submodule.subset_span fun n => ⟨a n, hfa n⟩
  let A : ModularForm.AtkinLehnerDatum (N * p) p :=
    FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd N p hp hpN
  obtain ⟨g, hg, hcong⟩ :=
    CuspForm.exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral p hp5 A f hf 1 (by omega)
      (fun n => by
        simpa only [pow_one] using CuspForm.exists_int_mul_qCoeff_alSlash_of_mem_intLattice p hp5 A f hf n)
  change g ∈ CuspForm.intLattice N ((p : ℤ) + 1) at hg
  obtain ⟨aN, haN, -, -⟩ := CuspForm.exists_addMonoidHom_intLattice_qCoeff_saturated N ((p : ℤ) + 1)
  have key : PowerSeries.heckeU p (PowerSeries.mk fun n => ((a n : ℤ) : K)) =
      PowerSeries.mk fun n => ((aN ⟨g, hg⟩ n : ℤ) : K) := by
    ext n
    rw [PowerSeries.coeff_heckeU, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    obtain ⟨m, hm⟩ := hcong n
    have h1 : ModularFormClass.qCoeff (ModularForm.heckeU 2 p ⇑f) n = ModularFormClass.qCoeff f (p * n) := by
      rw [ModularFormClass.qCoeff_heckeU (f : CuspForm (CongruenceSubgroup.Gamma0 (N * p)) 2)
        (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 (N * p)) hp0, ModularForm.coeffHeckeU_apply,
        Nat.mul_comm n p]
    have hgN : ((aN ⟨g, hg⟩ n : ℤ) : ℂ) = ModularFormClass.qCoeff g n := haN ⟨g, hg⟩ n
    rw [h1, ← hgN, hfa (p * n)] at hm
    have hZ : aN ⟨g, hg⟩ n - a (p * n) = p * m := by exact_mod_cast hm
    have hK : ((aN ⟨g, hg⟩ n - a (p * n) : ℤ) : K) = 0 := by
      rw [CharP.intCast_eq_zero_iff K p, hZ]
      exact dvd_mul_right _ _
    rw [Int.cast_sub, sub_eq_zero] at hK
    exact hK.symm
  rw [key]
  exact Submodule.subset_span ⟨g, aN ⟨g, hg⟩, fun n => (haN ⟨g, hg⟩ n).symm, rfl⟩

end Lowering

section Assembly

private theorem main (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (hq3 : p = 3 → ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] :
    ModPForms.modPCusp N ((p : ℤ) + 1) K ≤ ModPForms.modPCusp (N * p) 2 K := by
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI : NeZero (N * p) := ⟨Nat.mul_ne_zero (NeZero.ne N) hp0⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hν : p = 3 → nuThree N = 0 := fun h3 => nuThree_eq_zero (hq3 h3)
  have hcase : (p = 3 ∧ nuThree N = 0) ∨ 5 ≤ p := by
    by_cases hp3 : p = 3
    · exact Or.inl ⟨hp3, hν hp3⟩
    · exact Or.inr (hp.five_le_of_ne_two_of_ne_three hp2 hp3)
  haveI : FiniteDimensional K ↥(ModPForms.modPCusp (N * p) 2 K) := finiteDimensional_modPCusp K
  haveI : FiniteDimensional K ↥(ModPForms.modPCusp N ((p : ℤ) + 1) K) := finiteDimensional_modPCusp K
  haveI : FiniteDimensional K ↥(ModPForms.modPCusp N 2 K) := finiteDimensional_modPCusp K

  let T : ↥(ModPForms.modPCusp (N * p) 2 K) →ₗ[K] PowerSeries K :=
    (PowerSeries.heckeU p : PowerSeries K →ₗ[K] PowerSeries K).domRestrict (ModPForms.modPCusp (N * p) 2 K)
  have hTW : LinearMap.range T ≤ ModPForms.modPCusp N ((p : ℤ) + 1) K := by
    rintro _ ⟨φ, rfl⟩
    exact heckeU_mem_modPCusp p hp2 N hpN hq3 K φ φ.2
  have hTV : LinearMap.range T ≤ ModPForms.modPCusp (N * p) 2 K := by
    rintro _ ⟨φ, rfl⟩
    exact ModPForms.heckeU_mem_modPCusp_of_dvd (N * p) 2 p (dvd_mul_left p N) K φ φ.2

  have hrn := LinearMap.finrank_range_add_finrank_ker T
  have hB : Module.finrank K ↥(LinearMap.ker T) ≤ Module.finrank K ↥(ModPForms.modPCusp N 2 K) :=
    ModPForms.finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two p N hpN K
  have hS1 : ∀ M : ℕ, ModPForms.modPCusp M (2 * ((1 : ℕ) : ℤ)) K = ModPForms.modPCusp M 2 K := fun M => by
    norm_num
  have hlow : genusFormula (N * p) ≤ (Module.finrank K ↥(ModPForms.modPCusp (N * p) 2 K) : ℚ) := by
    have h := ModPForms.dimFormulaCusp_le_finrank_modPCusp (N * p) 1 le_rfl K
    change dimF (N * p) 1 ≤ _ at h
    rw [dimF_one, hS1] at h
    exact h
  have hupN : (Module.finrank K ↥(ModPForms.modPCusp N 2 K) : ℚ) ≤ genusFormula N := by
    have h := finrank_le_dimF p N hpN K 1 le_rfl hcase
    rw [dimF_one, hS1] at h
    exact h
  have h2m : 2 * ((p + 1) / 2) = p + 1 := by omega
  have hS : ModPForms.modPCusp N (2 * (((p + 1) / 2 : ℕ) : ℤ)) K = ModPForms.modPCusp N ((p : ℤ) + 1) K := by
    congr 1
    exact_mod_cast h2m
  have hupW : (Module.finrank K ↥(ModPForms.modPCusp N ((p : ℤ) + 1) K) : ℚ)
      ≤ genusFormula (N * p) - genusFormula N := by
    have h := finrank_le_dimF p N hpN K ((p + 1) / 2) (by have := hp.two_le; omega) hcase
    rw [hS, dimF_succ_div_two hp hp2, ← genusFormula_mul_sub hp hp2 (NeZero.ne N) hpN hν] at h
    exact h

  have hfin : Module.finrank K ↥(LinearMap.range T) ≤ Module.finrank K ↥(ModPForms.modPCusp N ((p : ℤ) + 1) K) :=
    Submodule.finrank_mono hTW
  have heq : Module.finrank K ↥(LinearMap.range T) = Module.finrank K ↥(ModPForms.modPCusp N ((p : ℤ) + 1) K) := by
    apply le_antisymm hfin
    have h2 : (Module.finrank K ↥(LinearMap.range T) : ℚ)
        = Module.finrank K ↥(ModPForms.modPCusp (N * p) 2 K) - Module.finrank K ↥(LinearMap.ker T) := by
      have h := congrArg (fun n : ℕ => (n : ℚ)) hrn
      push_cast at h
      linarith
    have hB' : (Module.finrank K ↥(LinearMap.ker T) : ℚ) ≤ Module.finrank K ↥(ModPForms.modPCusp N 2 K) := by
      exact_mod_cast hB
    have h3 : (Module.finrank K ↥(ModPForms.modPCusp N ((p : ℤ) + 1) K) : ℚ)
        ≤ Module.finrank K ↥(LinearMap.range T) := by
      rw [h2]
      linarith
    exact_mod_cast h3
  have hrange : LinearMap.range T = ModPForms.modPCusp N ((p : ℤ) + 1) K :=
    Submodule.eq_of_le_of_finrank_eq hTW heq
  rw [← hrange]
  exact hTV

end Assembly

end ModPCuspWeightLevelAux
p2m_reactivate "P2MW.S_ModPForms_modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two.ModPCuspWeightLevelAux"

open ModPCuspWeightLevelAux in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N' : ℕ) (hpN' : ¬ p ∣ N') (hside : 3 < p ∨ 3 < N')
    (hq3 : p = 3 → ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F p] :
    ModPForms.modPCusp N' ((p : ℤ) + 1) F ≤ ModPForms.modPCusp (N' * p) 2 F := by
  have _ := hside
  haveI : NeZero N' := ⟨fun h => hpN' (h ▸ dvd_zero p)⟩
  haveI : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hK := main p hp2 N' hpN' hq3 (AlgebraicClosure F)
  rw [ModPForms.modPCusp, Submodule.span_le]
  intro φ hφ
  have hmap : PowerSeries.map (algebraMap F (AlgebraicClosure F)) φ ∈
      ModPForms.modPCusp N' ((p : ℤ) + 1) (AlgebraicClosure F) := by
    rw [modPCusp_eq_span_image (F := F)]
    exact Submodule.subset_span ⟨φ, hφ, rfl⟩
  have h2 := hK hmap
  rw [modPCusp_eq_span_image (F := F)] at h2
  rw [SetLike.mem_coe]
  exact mem_span_of_map_mem_span h2

end S_ModPForms_modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two
end P2MW
export P2MW.S_ModPForms_modPCusp_add_one_le_modPCusp_mul_two_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two (solution)
