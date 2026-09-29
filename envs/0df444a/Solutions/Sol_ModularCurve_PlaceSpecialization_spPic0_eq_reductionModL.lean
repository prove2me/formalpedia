-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.spPic0_eq_reductionModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ada8f217-8192-5fb4-9212-42320650f245

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_constantReduction_isGood_isPlaceReductionModL
import Theorems.Thm_ModularCurve_reductionInputsModL_of_not_dvd
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_JZero_divisible
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Pic0_subsingleton_of_forall_isPrincipal
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_exists_finset_place_eq_of_ord_jqModC_sub_pos
import Theorems.Thm_ModularCurve_IsPlaceReductionModL_coordinate_clauses
import Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_genus_eq_zero
import Theorems.Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_spPic0_eq_reductionModL
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.cuspCount_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU"
p2m_attr_erase "simp" "ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "ModularCurve~jBar ValuationSubring AlgebraicCurve IsLocalRing"

namespace SpecializationComparison

private theorem degree_eq_zero_of_mem_principal (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : D ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))) :
    Divisor.degree D = 0 := by
  obtain ⟨f, hf, hDf⟩ := hD
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D₀, hD₀, hdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) f hf
  have hDD : D = D₀ := Finsupp.ext fun v => by rw [hDf v, hD₀ v]
  rw [hDD, hdeg]

private theorem placeMap_eq_of_agree (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {s r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)}
    (hagree : ∀ D ∈ integralPrincipalDivisors A (IsLocalRing.residue ↥A) N,
      Finsupp.mapDomain s D = Finsupp.mapDomain r D)
    (hnc : ∃ D ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)),
      Finsupp.mapDomain s D ≠ 0) :
    s = r :=
  IsPlaceReductionAlong.eq_of_agree (ModularCurve.reductionInputsModL_of_not_dvd N hℓN A hA).choose_spec.2
    hagree (ModularCurve.deg_eq_one_modularFunctionFieldBar N) (degree_eq_zero_of_mem_principal N)
    (ModularCurve.JZero.divisible N) hnc

private theorem agree_of_two_specs {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {s r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)}
    (hs : IsPlaceReductionModL A N s) (hr : IsPlaceReductionModL A N r) :
    ∀ D ∈ integralPrincipalDivisors A (IsLocalRing.residue ↥A) N,
      Finsupp.mapDomain s D = Finsupp.mapDomain r D := by
  rintro D ⟨y, hy, hyk, hy0, hD⟩
  exact Finsupp.ext fun Q => by rw [hs.2 y hy hyk hy0 D hD Q, hr.2 y hy hyk hy0 D hD Q]

private theorem hnc_of_spec (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    {r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)}
    (hr : IsPlaceReductionModL A N r) :
    ∃ D ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)),
      Finsupp.mapDomain r D ≠ 0 := by
  have _ := hℓN; have _ := hA
  set κ := ResidueField ↥A

  have hy : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar N := by
    rw [coeffMap_jqModC A.subtype,
        show jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) jq by
          rw [coeffEmb, ← jqModC_rat, coeffMap_jqModC]]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full N (jq_mem N))
  have hyk : coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) ∈ modularFunctionFieldFullC κ N := by
    rw [coeffMap_jqModC (IsLocalRing.residue ↥A)]; exact jqModC_mem_full κ N
  have hy0 : coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) ≠ 0 := by
    rw [coeffMap_jqModC (IsLocalRing.residue ↥A)]; exact jqModC_ne_zero_def κ

  set jBar : ↥(modularFunctionFieldBar N) := ⟨coeffMap A.subtype (jqModC ↥A), hy⟩
  have hj_ne : jBar ≠ 0 := by
    intro h
    apply jqModC_ne_zero_def (AlgebraicClosure ℚ)
    have : (jBar : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [h]; rfl
    rwa [show (jBar : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (jqModC ↥A) from rfl,
        coeffMap_jqModC A.subtype] at this
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D₀, hD₀, _hdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
      (F := ↥(modularFunctionFieldBar N)) jBar hj_ne
  refine ⟨D₀, ⟨jBar, hj_ne, hD₀⟩, ?_⟩

  have hmapD : ∀ Q, Finsupp.mapDomain r D₀ Q =
      Q.ord (⟨coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A), hyk⟩ :
        modularFunctionFieldFullC κ N) :=
    hr.2 (jqModC ↥A) hy hyk hy0 D₀ hD₀

  intro hzero
  have hQ := hmapD (qInftyPlaceMod κ (jqModC_mem_full κ N))
  rw [hzero, Finsupp.zero_apply] at hQ
  rw [ord_qInftyPlaceMod,
      show qSeriesBar κ (modularFunctionFieldFullC κ N)
          ⟨coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A), hyk⟩
        = coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) from rfl,
      coeffMap_jqModC (IsLocalRing.residue ↥A), order_jqModC_def] at hQ
  exact absurd hQ (by decide)

private theorem exists_constantReduction_placeMap_eq_full (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (sp : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hsp : IsPlaceReductionModL A N sp) :
    ∃ R : ConstantReduction A (modularFunctionFieldBar N) (modularFunctionFieldFullC (ResidueField ↥A) N),
      R.placeMap = sp := by
  obtain ⟨R₀, -, hR₀⟩ := ModularCurve.exists_constantReduction_isGood_isPlaceReductionModL N hℓN A hA
  exact ⟨R₀, placeMap_eq_of_agree N hℓN A hA (agree_of_two_specs hR₀ hsp) (hnc_of_spec N hℓN A hA hR₀)⟩

private theorem exists_constantReduction_placeMap_eq_var (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)] :
    ∀ (Y : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
      (hY : modularFunctionFieldFullC (ResidueField ↥A) N = Y)
      (sp : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (ResidueField ↥A) ↥Y),
      IsPlaceReductionModL A N (fun P => hY ▸ sp P) →
        ∃ R : ConstantReduction A (modularFunctionFieldBar N) ↥Y, R.placeMap = sp := by
  intro Y hY sp hsp
  subst hY
  exact exists_constantReduction_placeMap_eq_full N hℓN A hA sp hsp

section fg

private theorem addMonoidHom_eq_zero_of_divisible_of_range_le_fg {J G : Type*}
    [AddCommGroup J] [AddCommGroup G] (Φ : J →+ G)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : J, ∃ y : J, n • y = x)
    (H : AddSubgroup G) (hH : H.FG) (hle : Φ.range ≤ H) : Φ = 0 := by
  set D : Submodule ℤ G := AddSubgroup.toIntSubmodule Φ.range
  have hmemD : ∀ j : J, Φ j ∈ D := fun j => ⟨j, rfl⟩
  have hHfg : (AddSubgroup.toIntSubmodule H).FG :=
    (Submodule.fg_iff_addSubgroup_fg _).mpr (by simpa using hH)
  have hDle : D ≤ AddSubgroup.toIntSubmodule H := AddSubgroup.toIntSubmodule.monotone hle
  have hDfg : D.FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ hHfg
    have hc : (D.comap (AddSubgroup.toIntSubmodule H).subtype).FG := IsNoetherian.noetherian _
    have hmap := hc.map (AddSubgroup.toIntSubmodule H).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hDle] at hmap
  set I : Ideal ℤ := Ideal.span {((2 : ℕ) : ℤ)}
  have hsmul : D ≤ I • D := by
    rintro x ⟨j, rfl⟩
    obtain ⟨j', rfl⟩ := hdiv 2 two_ne_zero j
    rw [map_nsmul, ← natCast_zsmul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hmemD j')
  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I D hDfg hsmul
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Ideal.mem_span_singleton] at hr1
    omega
  ext j
  obtain ⟨j', rfl⟩ := hdiv r.natAbs (Int.natAbs_ne_zero.mpr hr0) j
  rw [map_nsmul, AddMonoidHom.zero_apply, ← natCast_zsmul]
  have h1 : r • Φ j' = 0 := hr _ (hmemD j')
  rcases Int.natAbs_eq r with h | h
  · rw [← h, h1]
  · have h' : (r.natAbs : ℤ) = -r := by omega
    rw [h', neg_zsmul, h1, neg_zero]

end fg

section engine

variable {K F k Fbar : Type*} [Field K] [Field F] [Algebra K F] [Field k] [Field Fbar]
  [Algebra k Fbar]

private theorem isPrincipal_mapDomain_sub_mapDomain_of_divisible
    (s r : Place K F → Place k Fbar)
    (hs : ∀ D : Divisor K F, Divisor.IsPrincipal D →
      Divisor.IsPrincipal (Finsupp.mapDomain s D))
    (hr : ∀ D : Divisor K F, Divisor.IsPrincipal D →
      Divisor.IsPrincipal (Finsupp.mapDomain r D))
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 K F, ∃ y : Pic0 K F, n • y = x)
    (X : Finset (Place k Fbar)) (hX : ∀ w, s w = r w ∨ (s w ∈ X ∧ r w ∈ X))
    (D : Divisor K F) (hD : D.degree = 0) :
    Divisor.IsPrincipal (Finsupp.mapDomain s D - Finsupp.mapDomain r D) := by
  classical

  let δ : Divisor K F →+ Divisor k Fbar :=
    Finsupp.mapDomain.addMonoidHom s - Finsupp.mapDomain.addMonoidHom r
  have hδ : ∀ E, δ E = Finsupp.mapDomain s E - Finsupp.mapDomain r E := fun E => rfl
  have hδprin : ∀ E ∈ Divisor.principal (K := K) (F := F),
      δ E ∈ Divisor.principal (K := k) (F := Fbar) := fun E hE =>
    (Divisor.principal (K := k) (F := Fbar)).sub_mem (hs E hE) (hr E hE)

  let V : Finset (Divisor k Fbar) :=
    (X ×ˢ X).image fun p => Finsupp.single p.1 1 - Finsupp.single p.2 1
  have hδV : ∀ E, δ E ∈ AddSubgroup.closure (V : Set (Divisor k Fbar)) := by
    intro E
    induction E using Finsupp.induction with
    | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
    | single_add w n E _ _ ih =>
      rw [map_add]
      refine AddSubgroup.add_mem _ ?_ ih
      rw [hδ, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
      rcases hX w with h | ⟨h1, h2⟩
      · rw [h, sub_self]; exact AddSubgroup.zero_mem _
      · have hmem : Finsupp.single (s w) (1 : ℤ) - Finsupp.single (r w) 1 ∈
            AddSubgroup.closure (V : Set (Divisor k Fbar)) :=
          AddSubgroup.subset_closure (by
            simp only [V, Finset.coe_image, Finset.coe_product]
            exact ⟨(s w, r w), ⟨h1, h2⟩, rfl⟩)
        have : Finsupp.single (s w) n - Finsupp.single (r w) n =
            n • (Finsupp.single (s w) (1 : ℤ) - Finsupp.single (r w) 1) := by
          rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [this]
        exact AddSubgroup.zsmul_mem _ hmem n

  let Φ : Pic0 K F →+ Pic k Fbar :=
    QuotientAddGroup.map _ _ (δ.comp (Divisor.degZero (K := K) (F := F)).subtype) (by
      rintro ⟨E, hE0⟩ hE
      rw [AddSubgroup.mem_addSubgroupOf] at hE
      rw [AddSubgroup.mem_comap]
      exact hδprin E hE)
  have hΦmk : ∀ E : Divisor.degZero (K := K) (F := F),
      Φ (Pic0.mk E) = QuotientAddGroup.mk (δ (E : Divisor K F)) := fun E => rfl

  let H : AddSubgroup (Pic k Fbar) :=
    (AddSubgroup.closure (V : Set (Divisor k Fbar))).map
      (QuotientAddGroup.mk' (Divisor.principal (K := k) (F := Fbar)))
  have hH : H.FG := by
    refine ⟨V.image (QuotientAddGroup.mk' (Divisor.principal (K := k) (F := Fbar))), ?_⟩
    rw [Finset.coe_image, ← AddMonoidHom.map_closure]
  have hle : Φ.range ≤ H := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨E, rfl⟩ := Pic0.mk_surjective x
    rw [hΦmk]
    exact AddSubgroup.mem_map_of_mem _ (hδV E)
  have hΦ0 := addMonoidHom_eq_zero_of_divisible_of_range_le_fg Φ hdiv H hH hle

  have hD0 : D ∈ Divisor.degZero (K := K) (F := F) := hD
  have h := hΦmk ⟨D, hD0⟩
  rw [hΦ0, AddMonoidHom.zero_apply, eq_comm, QuotientAddGroup.eq_zero_iff] at h
  rw [← hδ]
  exact h

private theorem exists_place_notMem [Infinite K] [HasPrincipalDivisors K F]
    (hdeg : ∀ v : Place K F, v.deg = 1) (x : F) {v₀ : Place K F} (hx : v₀.ord x < 0)
    (B : Finset (Place K F)) : ∃ v : Place K F, v ∉ B := by
  classical
  have hx0 : x ≠ 0 := fun h => by rw [h, Place.ord_zero] at hx; exact lt_irrefl _ hx

  have hzero : ∀ c : K, ∃ v : Place K F, 0 < v.ord (x - algebraMap K F c) := by
    intro c
    have hxc : x - algebraMap K F c ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rcases eq_or_ne c 0 with rfl | hc
      · exact hx0 (by simpa using h)
      · have := AlgebraicCurve.ConstantReduction.ord_algebraMap v₀ (F := F) hc
        rw [← h] at this; omega
    have hneg : v₀.ord (x - algebraMap K F c) < 0 := by
      rcases eq_or_ne c 0 with rfl | hc
      · simpa using hx
      · rw [sub_eq_add_neg, v₀.ord_add_eq_of_lt hx0 (neg_ne_zero.mpr ((map_ne_zero _).mpr hc))
          (by rw [← map_neg, AlgebraicCurve.ConstantReduction.ord_algebraMap v₀ (F := F)
            (neg_ne_zero.mpr hc)]; exact hx)]
        exact hx
    obtain ⟨D, hD, hD0⟩ := HasPrincipalDivisors.exists_divisor (K := K) (x - algebraMap K F c) hxc
    by_contra hall
    simp only [not_exists, not_lt] at hall

    have hle : ∀ v, D v * (v.deg : ℤ) ≤ 0 := fun v => by
      rw [hdeg, Nat.cast_one, mul_one, hD]; exact hall v
    have hsum : D.degree = D.sum fun v n => n * (v.deg : ℤ) := by
      simp [Divisor.degree, Finsupp.liftAddHom_apply, AddMonoidHom.mulRight]
    have hlt : D.sum (fun v n => n * (v.deg : ℤ)) < 0 := by
      have hv₀ : v₀ ∈ D.support := by
        rw [Finsupp.mem_support_iff, hD]; exact hneg.ne
      calc D.sum (fun v n => n * (v.deg : ℤ))
          = ∑ v ∈ D.support, D v * (v.deg : ℤ) := rfl
        _ < ∑ v ∈ D.support, (0 : ℤ) :=
          Finset.sum_lt_sum (fun v _ => hle v) ⟨v₀, hv₀, by
            rw [hdeg, Nat.cast_one, mul_one, hD]; exact hneg⟩
        _ = 0 := Finset.sum_const_zero
    rw [← hsum, hD0] at hlt
    exact lt_irrefl _ hlt

  have hinj : ∀ (c c' : K) (v : Place K F), 0 < v.ord (x - algebraMap K F c) →
      0 < v.ord (x - algebraMap K F c') → c = c' := by
    intro c c' v hc hc'
    by_contra hne
    have hk : algebraMap K F (c' - c) ≠ 0 := (map_ne_zero _).mpr (sub_ne_zero.mpr (Ne.symm hne))
    have hg : x - algebraMap K F c' ≠ 0 := fun h => by
      rw [h, Place.ord_zero] at hc'; exact lt_irrefl _ hc'
    have h0 : v.ord (algebraMap K F (c' - c)) = 0 :=
      AlgebraicCurve.ConstantReduction.ord_algebraMap v (F := F) (sub_ne_zero.mpr (Ne.symm hne))
    have := v.ord_add_eq_of_lt hk hg (by rw [h0]; exact hc')
    rw [h0, show algebraMap K F (c' - c) + (x - algebraMap K F c') = x - algebraMap K F c by
      rw [map_sub]; ring] at this
    rw [this] at hc
    exact lt_irrefl _ hc

  by_contra hB
  simp only [not_exists, not_not] at hB
  choose z hz using hzero
  have hzinj : Function.Injective z := fun c c' h => hinj c c' (z c) (hz c) (h ▸ hz c')
  have hfin : (Set.univ : Set K).Finite :=
    (B.finite_toSet.preimage hzinj.injOn).subset fun c _ => hB (z c)
  exact Set.infinite_univ hfin

end engine

private theorem isPrincipal_mapDomain_sub_mapDomain_jZero (N : ℕ) [NeZero N]
    {k Fbar : Type*} [Field k] [Field Fbar] [Algebra k Fbar]
    (s r : Place (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) → Place k Fbar)
    (hs : ∀ D : Divisor (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N),
      Divisor.IsPrincipal D → Divisor.IsPrincipal (Finsupp.mapDomain s D))
    (hr : ∀ D : Divisor (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N),
      Divisor.IsPrincipal D → Divisor.IsPrincipal (Finsupp.mapDomain r D))
    (X : Finset (Place k Fbar)) (hX : ∀ w, s w = r w ∨ (s w ∈ X ∧ r w ∈ X))
    (D : Divisor (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N))
    (hD : D.degree = 0) :
    Divisor.IsPrincipal (Finsupp.mapDomain s D - Finsupp.mapDomain r D) :=
  isPrincipal_mapDomain_sub_mapDomain_of_divisible s r hs hr
    (ModularCurve.JZero.divisible N) X hX D hD

private theorem exists_apply_eq_of_surjective (N : ℕ) [NeZero N]
    {k : Type*} [Field k] [IsAlgClosed k] {W : Type*}
    (sp r : W → Place k (ModularCurve.modularFunctionFieldFullC k N))
    (hsurj : Function.Surjective sp)
    (X : Finset (Place k (ModularCurve.modularFunctionFieldFullC k N)))
    (hX : ∀ w, sp w = r w ∨ (sp w ∈ X ∧ r w ∈ X)) :
    ∃ w₀, sp w₀ = r w₀ := by
  haveI := ModularCurve.isCurveOver_modularFunctionFieldFullC k N
  haveI : HasPrincipalDivisors k ↥(ModularCurve.modularFunctionFieldFullC k N) :=
    IsCurveOver.hasPrincipalDivisors
  have hpole : (ModularCurve.qInftyPlaceMod k (ModularCurve.jqModC_mem_full k N)).ord
      (⟨ModularCurve.jqModC k, ModularCurve.jqModC_mem_full k N⟩ :
        ModularCurve.modularFunctionFieldFullC k N) < 0 := by
    rw [ModularCurve.ord_qInftyPlaceMod]
    have h := ModularCurve.order_jqModC_def k
    change (ModularCurve.jqModC k).order < 0
    omega
  obtain ⟨Q, hQ⟩ := exists_place_notMem (IsCurveOver.forall_deg_eq_one_of_isAlgClosed)
    (⟨ModularCurve.jqModC k, ModularCurve.jqModC_mem_full k N⟩ :
      ModularCurve.modularFunctionFieldFullC k N) hpole X
  obtain ⟨w, rfl⟩ := hsurj Q
  rcases hX w with h | ⟨h1, -⟩
  · exact ⟨w, h⟩
  · exact absurd h1 hQ

private theorem mapDomain_mem_of_closure {α β M : Type*} [AddCommGroup M]
    (H : AddSubgroup (β →₀ M)) (s : α → β) (T : Set (α →₀ M))
    (hT : ∀ E ∈ T, Finsupp.mapDomain s E ∈ H)
    {D : α →₀ M} (hD : D ∈ AddSubgroup.closure T) :
    Finsupp.mapDomain s D ∈ H := by
  induction hD using AddSubgroup.closure_induction with
  | mem E hE => exact hT E hE
  | zero => rw [Finsupp.mapDomain_zero]; exact H.zero_mem
  | add E E' _ _ hE hE' => rw [Finsupp.mapDomain_add]; exact H.add_mem hE hE'
  | neg E _ hE =>
    have hneg : Finsupp.mapDomain s (-E) = -(Finsupp.mapDomain s E) :=
      eq_neg_of_add_eq_zero_left (by
        rw [← Finsupp.mapDomain_add, neg_add_cancel, Finsupp.mapDomain_zero])
    rw [hneg]; exact H.neg_mem hE

private theorem mapDomain_reduction_isPrincipal (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    {r₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)}
    (hr₀ : IsPlaceReductionModL A N r₀)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : Divisor.IsPrincipal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) D) :
    Divisor.IsPrincipal (K := ResidueField ↥A)
        (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
      (Finsupp.mapDomain r₀ D) := by
  have hgen : PrincipalGeneratedByIntegral A (IsLocalRing.residue ↥A) N :=
    (ModularCurve.reductionInputsModL_of_not_dvd N hℓN A hA).choose_spec.2
  exact mapDomain_mem_of_closure
    (Divisor.principal (K := ResidueField ↥A)
      (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) N)))
    r₀ (integralPrincipalDivisors A (IsLocalRing.residue ↥A) N)
    (fun E hE => by
      obtain ⟨y, hy, hyk, hy0, hord⟩ := hE
      exact ⟨⟨coeffMap (IsLocalRing.residue ↥A) y, hyk⟩,
        fun h => hy0 (congrArg Subtype.val h),
        fun Q => hr₀.2 y hy hyk hy0 E hord Q⟩)
    (hgen hD)

private theorem mapDomain_sp_isPrincipal_var (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)] :
    ∀ (Y : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
      (hY : modularFunctionFieldFullC (ResidueField ↥A) N = Y)
      (sp : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (ResidueField ↥A) ↥Y)
      (_ : ∀ f : modularFunctionFieldBar N, f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          (∀ v, D v = v.ord f) →
          ∃ g : ↥Y, g ≠ 0 ∧
            ∀ v' : Place (ResidueField ↥A) ↥Y, Finsupp.mapDomain sp D v' = v'.ord g),
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        Divisor.IsPrincipal D →
        Divisor.IsPrincipal (K := ResidueField ↥A)
          (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
          (Finsupp.mapDomain (fun P => (hY ▸ sp P : Place (ResidueField ↥A)
            (modularFunctionFieldFullC (ResidueField ↥A) N))) D) := by
  intro Y hY sp hd5 D hD
  subst hY
  obtain ⟨f, hf, hDf⟩ := hD
  obtain ⟨g, hg, hmap⟩ := hd5 f hf D hDf
  exact ⟨g, hg, hmap⟩

private theorem mapDomain_sp_isPrincipal (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ))
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : Divisor.IsPrincipal (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar N)) D) :
    Divisor.IsPrincipal (K := ResidueField ↥A)
        (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
      (Finsupp.mapDomain (fun P =>
        (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC
          (ResidueField ↥A) ℓ N hℓN).symm ▸ S.sp P) D) :=
  mapDomain_sp_isPrincipal_var N A (modularFunctionFieldC (ResidueField ↥A) N)
    (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC
      (ResidueField ↥A) ℓ N hℓN).symm S.sp S.d5 D hD

private theorem exists_finset_apply_eq_or_mem_var (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [IsAlgClosed (ResidueField ↥A)]
    {r₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)}
    (hcl : (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
      0 < w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) →
      0 < (r₀ w).ord
          (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)
                (IsLocalRing.residue ↥A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A,
        w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0) →
      (r₀ w).ord (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩
        : modularFunctionFieldFullC (ResidueField ↥A) N) < 0) ∧
    (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
      0 < w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) →
      0 < (r₀ w).ord
          (⟨jqNModC (ResidueField ↥A) N,
              modularFunctionFieldC_le_full (ResidueField ↥A) N (jqNModC_mem (ResidueField ↥A) N)⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)
                (IsLocalRing.residue ↥A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A,
        w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0) →
      (r₀ w).ord (⟨jqNModC (ResidueField ↥A) N,
          modularFunctionFieldC_le_full (ResidueField ↥A) N (jqNModC_mem (ResidueField ↥A) N)⟩
        : modularFunctionFieldFullC (ResidueField ↥A) N) < 0)) :
    ∀ (Y : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
      (hY : modularFunctionFieldFullC (ResidueField ↥A) N = Y)
      (hjY : jqModC (ResidueField ↥A) ∈ Y) (hjNY : jqNModC (ResidueField ↥A) N ∈ Y)
      (sp : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (ResidueField ↥A) Y)
      (_ : Function.Surjective sp)
      (_ : ∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
        0 < w.ord
            (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) →
        0 < (sp w).ord (⟨jqModC (ResidueField ↥A), hjY⟩
          - algebraMap (ResidueField ↥A) Y (IsLocalRing.residue ↥A a)))
      (_ : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ a : A,
          w.ord
            (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0) →
        (sp w).ord (⟨jqModC (ResidueField ↥A), hjY⟩ : Y) < 0)
      (_ : ∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
        0 < w.ord
            (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) →
        0 < (sp w).ord (⟨jqNModC (ResidueField ↥A) N, hjNY⟩
          - algebraMap (ResidueField ↥A) Y (IsLocalRing.residue ↥A a)))
      (_ : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ a : A,
          w.ord
            (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0) →
        (sp w).ord (⟨jqNModC (ResidueField ↥A) N, hjNY⟩ : Y) < 0)
      (_ : ∃ B : Finset (Place (ResidueField ↥A) Y),
        (∀ Q : Place (ResidueField ↥A) Y,
          Q.ord (⟨jqModC (ResidueField ↥A), hjY⟩ : Y) < 0 → Q ∈ B) ∧
        (∀ Q : Place (ResidueField ↥A) Y,
          Q.ord (⟨jqNModC (ResidueField ↥A) N, hjNY⟩ : Y) < 0 → Q ∈ B) ∧
        ∀ Q : Place (ResidueField ↥A) Y, Q ∉ B →
          ∀ (Q' : Place (ResidueField ↥A) Y) (s t : ResidueField ↥A),
            0 < Q.ord (⟨jqModC (ResidueField ↥A), hjY⟩ - algebraMap (ResidueField ↥A) Y s) →
            0 < Q.ord (⟨jqNModC (ResidueField ↥A) N, hjNY⟩ - algebraMap (ResidueField ↥A) Y t) →
            0 < Q'.ord (⟨jqModC (ResidueField ↥A), hjY⟩ - algebraMap (ResidueField ↥A) Y s) →
            0 < Q'.ord (⟨jqNModC (ResidueField ↥A) N, hjNY⟩ - algebraMap (ResidueField ↥A) Y t) →
            Q' = Q),
      ∃ X : Finset (Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)),
        (∀ w, (hY ▸ sp w) = r₀ w ∨ ((hY ▸ sp w) ∈ X ∧ r₀ w ∈ X))
        ∧ ∃ w₀, (hY ▸ sp w₀) = r₀ w₀ := by
  intro Y hY hjY hjNY sp hsurj d0_j d0_j_pole d0_jN d0_jN_pole hfin
  subst hY
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hcl
  obtain ⟨B, hBj, hBjN, hB3⟩ := hfin
  have hX : ∀ w, sp w = r₀ w ∨ (sp w ∈ B ∧ r₀ w ∈ B) := by
    intro w
    by_cases hj : ∃ a : A, 0 < w.ord
            (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ))
    · by_cases hjN : ∃ a : A, 0 < w.ord
            (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ))
      · obtain ⟨a, ha⟩ := hj
        obtain ⟨b, hb⟩ := hjN
        have hs1 := d0_j w a ha
        have hs2 := d0_jN w b hb
        have ht1 := hr1 w a ha
        have ht2 := hr3 w b hb
        by_cases hsB : sp w ∈ B
        · by_cases hrB : r₀ w ∈ B
          · exact Or.inr ⟨hsB, hrB⟩
          · exact Or.inl (hB3 (r₀ w) hrB (sp w) _ _ ht1 ht2 hs1 hs2)
        · exact Or.inl (hB3 (sp w) hsB (r₀ w) _ _ hs1 hs2 ht1 ht2).symm
      · simp only [not_exists, not_lt] at hjN
        exact Or.inr ⟨hBjN _ (d0_jN_pole w hjN), hBjN _ (hr4 w hjN)⟩
    · simp only [not_exists, not_lt] at hj
      exact Or.inr ⟨hBj _ (d0_j_pole w hj), hBj _ (hr2 w hj)⟩
  exact ⟨B, hX, exists_apply_eq_of_surjective N sp r₀ hsurj B hX⟩

private theorem exists_finset_apply_eq_or_mem (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ))
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    {r₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)}

    (hfin : ∃ B : Finset (Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)),
      (∀ Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N),
        Q.ord (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩
          : modularFunctionFieldC (ResidueField ↥A) N) < 0 → Q ∈ B) ∧
      (∀ Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N),
        Q.ord (⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩
          : modularFunctionFieldC (ResidueField ↥A) N) < 0 → Q ∈ B) ∧
      ∀ Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N), Q ∉ B →
        ∀ (Q' : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
          (s t : ResidueField ↥A),
          0 < Q.ord (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) s) →
          0 < Q.ord (⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) t) →
          0 < Q'.ord (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) s) →
          0 < Q'.ord (⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) t) →
          Q' = Q)

    (hcl : (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
      0 < w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) →
      0 < (r₀ w).ord
          (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)
                (IsLocalRing.residue ↥A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A,
        w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0) →
      (r₀ w).ord (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩
        : modularFunctionFieldFullC (ResidueField ↥A) N) < 0) ∧
    (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
      0 < w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) →
      0 < (r₀ w).ord
          (⟨jqNModC (ResidueField ↥A) N,
              modularFunctionFieldC_le_full (ResidueField ↥A) N (jqNModC_mem (ResidueField ↥A) N)⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)
                (IsLocalRing.residue ↥A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A,
        w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0) →
      (r₀ w).ord (⟨jqNModC (ResidueField ↥A) N,
          modularFunctionFieldC_le_full (ResidueField ↥A) N (jqNModC_mem (ResidueField ↥A) N)⟩
        : modularFunctionFieldFullC (ResidueField ↥A) N) < 0)) :
    ∃ X : Finset (Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)),
      (∀ w, ((ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC
            (ResidueField ↥A) ℓ N hℓN).symm ▸ S.sp w) = r₀ w ∨
        (((ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC
            (ResidueField ↥A) ℓ N hℓN).symm ▸ S.sp w) ∈ X ∧ r₀ w ∈ X))
      ∧ ∃ w₀, ((ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC
            (ResidueField ↥A) ℓ N hℓN).symm ▸ S.sp w₀) = r₀ w₀ := by
  exact exists_finset_apply_eq_or_mem_var N A hcl (modularFunctionFieldC (ResidueField ↥A) N)
    (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC
      (ResidueField ↥A) ℓ N hℓN).symm
    (jqModC_mem (ResidueField ↥A) N) (jqNModC_mem (ResidueField ↥A) N)
    S.sp S.d4 S.d0_j S.d0_j_pole S.d0_jN S.d0_jN_pole hfin

private theorem false_of_isPrincipal_single_sub_single (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]

    (hEFT : Algebra.EssFiniteType (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))

    (hRR : FunctionFieldRiemannRoch (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hWDA : WeilDualityAdelic (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hCAB : ConstantsAreBase (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))

    (hgen0 : ∀ {K F : Type} [Field K] [Field F] [Algebra K F]
      [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
      [∀ v : Place K F, v.DCoordGenerates]
      (_ : FunctionFieldRiemannRoch K F) (_ : ConstantsAreBase K F)
      {P Q : Place K F}, P ≠ Q → Q.deg = 1 →
      Divisor.IsPrincipal (Finsupp.single P (1 : ℤ) - Finsupp.single Q 1) →
      genus K F = 0)

    (hprin0 : ∀ {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
      [Algebra.EssFiniteType K F] [IsCurveOver K F]
      [HasCanonicalDivisor (K := K) (F := F)]
      (_ : genus K F = 0) {D : Divisor K F},
      Divisor.degree D = 0 → Divisor.IsPrincipal D)
    (hJ : ∃ x : JZero N, x ≠ 0)
    {Q₁ Q₂ : Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)}
    (hQ : Q₁ ≠ Q₂)
    (h : Divisor.IsPrincipal (K := ResidueField ↥A)
        (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
      (Finsupp.single Q₁ (1 : ℤ) - Finsupp.single Q₂ 1)) : False := by

  haveI : IsCurveOver (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N) :=
    ModularCurve.isCurveOver_modularFunctionFieldFullC (ResidueField ↥A) N
  haveI := hEFT
  haveI : HasCanonicalDivisor (K := ResidueField ↥A)
      (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) N)) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  haveI := AlgebraicCurve.dCoordGenerates_of_isCurveOver
    (K := ResidueField ↥A) (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) N))

  have hg0_Full : genus (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N) = 0 :=
    hgen0 (K := ResidueField ↥A) (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
      hRR hCAB hQ (IsCurveOver.forall_deg_eq_one_of_isAlgClosed Q₂) h

  have hgFF_Full : genusFF (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N) = 0 := by
    rw [← AlgebraicCurve.genus_eq_genusFF hRR hWDA hCAB]; exact hg0_Full

  have hNne : (N : ResidueField ↥A) ≠ 0 := by
    have hprime := (Fact.out : ℓ.Prime)
    intro hNzero
    exact hℓN ((CharP.cast_eq_zero_iff (ResidueField ↥A) ℓ N).mp hNzero)
  have hgFF_Bar : genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) = 0 := by
    rw [← ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
      (ResidueField ↥A) N hNne]
    exact hgFF_Full

  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.essFiniteType_modularFunctionFieldBar N
  haveI : HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) :=
    ModularCurve.hasCanonicalDivisor_modularFunctionFieldBar N
  have hg0_Bar : genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) = 0 := by
    rw [ModularCurve.genus_eq_genusFF_modularFunctionFieldBar N]; exact hgFF_Bar
  haveI hSub : Subsingleton (JZero N) :=
    AlgebraicCurve.Pic0.subsingleton_of_forall_isPrincipal (AlgebraicClosure ℚ)
      ↥(modularFunctionFieldBar N) (fun D hD => hprin0 (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) hg0_Bar hD)
  obtain ⟨x, hx⟩ := hJ
  exact hx (hSub.elim x 0)

private theorem sp_eq_r₀_of_hJ_generic
    (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (sp r₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hr₀ : IsPlaceReductionModL A N r₀)
    (X : Finset (Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)))
    (hX : ∀ w, sp w = r₀ w ∨ (sp w ∈ X ∧ r₀ w ∈ X))
    (hw₀ : ∃ w₀, sp w₀ = r₀ w₀)
    (hprinSp : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Divisor.IsPrincipal D →
      Divisor.IsPrincipal (K := ResidueField ↥A)
        (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) N)) (Finsupp.mapDomain sp D))
    (hEFT : Algebra.EssFiniteType (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hRR : FunctionFieldRiemannRoch (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hWDA : WeilDualityAdelic (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hCAB : ConstantsAreBase (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hgen0 : ∀ {K F : Type} [Field K] [Field F] [Algebra K F]
      [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
      [∀ v : Place K F, v.DCoordGenerates]
      (_ : FunctionFieldRiemannRoch K F) (_ : ConstantsAreBase K F)
      {P Q : Place K F}, P ≠ Q → Q.deg = 1 →
      Divisor.IsPrincipal (Finsupp.single P (1 : ℤ) - Finsupp.single Q 1) →
      genus K F = 0)
    (hprin0 : ∀ {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
      [Algebra.EssFiniteType K F] [IsCurveOver K F]
      [HasCanonicalDivisor (K := K) (F := F)]
      (_ : genus K F = 0) {D : Divisor K F},
      Divisor.degree D = 0 → Divisor.IsPrincipal D)
    (hJ : ∃ x : JZero N, x ≠ 0) :
    sp = r₀ := by
  by_contra hne
  obtain ⟨w₁, hw₁⟩ : ∃ w, sp w ≠ r₀ w :=
    not_forall.mp (fun hall => hne (funext hall))
  obtain ⟨w₀, hw₀⟩ := hw₀
  set D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    Finsupp.single w₁ 1 - Finsupp.single w₀ 1
  have hDdeg : D.degree = 0 := by
    simp only [D, map_sub, Divisor.degree_single,
      ModularCurve.deg_eq_one_modularFunctionFieldBar, sub_self]
  have hprin := isPrincipal_mapDomain_sub_mapDomain_jZero N sp r₀ hprinSp
    (mapDomain_reduction_isPrincipal N hℓN A hA hr₀) X hX D hDdeg
  rw [show Finsupp.mapDomain sp D - Finsupp.mapDomain r₀ D
        = Finsupp.single (sp w₁) 1 - Finsupp.single (r₀ w₁) 1 by
      simp only [D, Finsupp.mapDomain_sub, Finsupp.mapDomain_single, hw₀]; abel] at hprin
  exact false_of_isPrincipal_single_sub_single N hℓN A hEFT hRR hWDA hCAB hgen0 hprin0 hJ hw₁ hprin

private theorem isPlaceReductionModL_sp_var
    (N : ℕ) [NeZero N]
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    {r₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)}
    (hr₀ : IsPlaceReductionModL A N r₀)
    (hEFT : Algebra.EssFiniteType (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hRR : FunctionFieldRiemannRoch (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hWDA : WeilDualityAdelic (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hCAB : ConstantsAreBase (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hgen0 : ∀ {K F : Type} [Field K] [Field F] [Algebra K F]
      [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
      [∀ v : Place K F, v.DCoordGenerates]
      (_ : FunctionFieldRiemannRoch K F) (_ : ConstantsAreBase K F)
      {P Q : Place K F}, P ≠ Q → Q.deg = 1 →
      Divisor.IsPrincipal (Finsupp.single P (1 : ℤ) - Finsupp.single Q 1) →
      genus K F = 0)
    (hprin0 : ∀ {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
      [Algebra.EssFiniteType K F] [IsCurveOver K F]
      [HasCanonicalDivisor (K := K) (F := F)]
      (_ : genus K F = 0) {D : Divisor K F},
      Divisor.degree D = 0 → Divisor.IsPrincipal D)
    (hJ : ∃ x : JZero N, x ≠ 0) :
    ∀ (Y : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
      (hY : modularFunctionFieldFullC (ResidueField ↥A) N = Y)
      (sp : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (ResidueField ↥A) ↥Y)
      (X : Finset (Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)))
      (_ : ∀ w, (hY ▸ sp w : Place (ResidueField ↥A)
          (modularFunctionFieldFullC (ResidueField ↥A) N)) = r₀ w ∨
        ((hY ▸ sp w : Place (ResidueField ↥A)
          (modularFunctionFieldFullC (ResidueField ↥A) N)) ∈ X ∧ r₀ w ∈ X))
      (_ : ∃ w₀, (hY ▸ sp w₀ : Place (ResidueField ↥A)
          (modularFunctionFieldFullC (ResidueField ↥A) N)) = r₀ w₀)
      (_ : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        Divisor.IsPrincipal D →
        Divisor.IsPrincipal (K := ResidueField ↥A)
          (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
          (Finsupp.mapDomain (fun P => (hY ▸ sp P : Place (ResidueField ↥A)
            (modularFunctionFieldFullC (ResidueField ↥A) N))) D)),
      IsPlaceReductionModL A N (fun P =>
        (hY ▸ sp P : Place (ResidueField ↥A)
          (modularFunctionFieldFullC (ResidueField ↥A) N))) := by
  intro Y hY sp X hX hw₀ hprinSp
  subst hY
  have heq := sp_eq_r₀_of_hJ_generic N hℓN A hA sp r₀ hr₀ X hX hw₀ hprinSp
    hEFT hRR hWDA hCAB hgen0 hprin0 hJ
  exact heq ▸ hr₀

private theorem isPlaceReductionModL_sp_of_clauses
    (N : ℕ) [NeZero N]
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ)
    {r₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)}
    (hspec₀ : IsPlaceReductionModL A N r₀)

    (hfin : ∃ B : Finset (Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)),
      (∀ Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N),
        Q.ord (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩
          : modularFunctionFieldC (ResidueField ↥A) N) < 0 → Q ∈ B) ∧
      (∀ Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N),
        Q.ord (⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩
          : modularFunctionFieldC (ResidueField ↥A) N) < 0 → Q ∈ B) ∧
      ∀ Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N), Q ∉ B →
        ∀ (Q' : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
          (s t : ResidueField ↥A),
          0 < Q.ord (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) s) →
          0 < Q.ord (⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) t) →
          0 < Q'.ord (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) s) →
          0 < Q'.ord (⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) t) →
          Q' = Q)

    (hcl : (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
      0 < w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) →
      0 < (r₀ w).ord
          (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)
                (IsLocalRing.residue ↥A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A,
        w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0) →
      (r₀ w).ord (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩
        : modularFunctionFieldFullC (ResidueField ↥A) N) < 0) ∧
    (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
      0 < w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) →
      0 < (r₀ w).ord
          (⟨jqNModC (ResidueField ↥A) N,
              modularFunctionFieldC_le_full (ResidueField ↥A) N (jqNModC_mem (ResidueField ↥A) N)⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)
                (IsLocalRing.residue ↥A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A,
        w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0) →
      (r₀ w).ord (⟨jqNModC (ResidueField ↥A) N,
          modularFunctionFieldC_le_full (ResidueField ↥A) N (jqNModC_mem (ResidueField ↥A) N)⟩
        : modularFunctionFieldFullC (ResidueField ↥A) N) < 0))
    (hEFT : Algebra.EssFiniteType (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hRR : FunctionFieldRiemannRoch (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hWDA : WeilDualityAdelic (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hCAB : ConstantsAreBase (ResidueField ↥A)
      ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hgen0 : ∀ {K F : Type} [Field K] [Field F] [Algebra K F]
      [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
      [∀ v : Place K F, v.DCoordGenerates]
      (_ : FunctionFieldRiemannRoch K F) (_ : ConstantsAreBase K F)
      {P Q : Place K F}, P ≠ Q → Q.deg = 1 →
      Divisor.IsPrincipal (Finsupp.single P (1 : ℤ) - Finsupp.single Q 1) →
      genus K F = 0)
    (hprin0 : ∀ {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
      [Algebra.EssFiniteType K F] [IsCurveOver K F]
      [HasCanonicalDivisor (K := K) (F := F)]
      (_ : genus K F = 0) {D : Divisor K F},
      Divisor.degree D = 0 → Divisor.IsPrincipal D)
    (hJ : ∃ x : JZero N, x ≠ 0) :
    IsPlaceReductionModL A N (fun P =>
      (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC
        (ResidueField ↥A) ℓ N hℓN).symm ▸ S.sp P) := by
  obtain ⟨X, hX, hw₀⟩ := exists_finset_apply_eq_or_mem N hℓN A data hKr hα hβ S hfin hcl
  exact isPlaceReductionModL_sp_var N hℓN A hA hspec₀
    hEFT hRR hWDA hCAB hgen0 hprin0 hJ
    (modularFunctionFieldC (ResidueField ↥A) N)
    (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC
      (ResidueField ↥A) ℓ N hℓN).symm
    S.sp X hX hw₀
    (mapDomain_sp_isPrincipal N hℓN A data hKr hα hβ S)

private theorem dedekindPsi_pos' (N : ℕ) [NeZero N] : 0 < dedekindPsi N := by
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
    simp [Nat.mem_divisors, NeZero.ne N]
  calc 0 < N / 1 := by simpa using Nat.pos_of_ne_zero (NeZero.ne N)
    _ ≤ ∑ d ∈ N.divisors with Squarefree d, N / d :=
        Finset.single_le_sum (f := fun d => N / d) (fun d _ => Nat.zero_le _) h1
    _ = dedekindPsi N := rfl

private theorem packFullC (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [CharP k ℓ] [Fact ℓ.Prime]
    (N : ℕ) [NeZero N] (hℓN : ¬ ℓ ∣ N) :
    Algebra.EssFiniteType k ↥(modularFunctionFieldFullC k N) ∧
    FunctionFieldRiemannRoch k ↥(modularFunctionFieldFullC k N) ∧
    WeilDualityAdelic k ↥(modularFunctionFieldFullC k N) ∧
    ConstantsAreBase k ↥(modularFunctionFieldFullC k N) := by
  haveI := ModularCurve.isCurveOver_modularFunctionFieldFullC k N
  have hN : ((N : ℕ) : k) ≠ 0 := fun h0 => hℓN ((CharP.cast_eq_zero_iff k ℓ N).mp h0)
  have htr : Transcendental k
      (⟨jqModC k, jqModC_mem_full k N⟩ : modularFunctionFieldFullC k N) := by
    rw [← transcendental_algebraMap_iff (R := k) (A := LaurentSeries k)
      (S := ↥(modularFunctionFieldFullC k N)) (a := ⟨jqModC k, jqModC_mem_full k N⟩)
      (algebraMap (↥(modularFunctionFieldFullC k N)) (LaurentSeries k)).injective]
    exact ModularCurve.transcendental_jqModC k
  have hfd : FiniteDimensional
      ↥(IntermediateField.adjoin k
        ({⟨jqModC k, jqModC_mem_full k N⟩} : Set (modularFunctionFieldFullC k N)))
      (modularFunctionFieldFullC k N) :=
    Module.finite_of_finrank_pos (by
      rw [ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi k N hN]
      exact dedekindPsi_pos' N)
  have hEFT : Algebra.EssFiniteType k ↥(modularFunctionFieldFullC k N) :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htr hfd
  have hCAB : ConstantsAreBase k ↥(modularFunctionFieldFullC k N) := by
    haveI := hfd
    exact AlgebraicCurve.constantsAreBase_of_isAlgClosed_of_transcendental _ htr
  have hRR : FunctionFieldRiemannRoch k ↥(modularFunctionFieldFullC k N) :=
    AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental htr hfd
  have hSGE : StichtenothGenusExists k ↥(modularFunctionFieldFullC k N) := by
    haveI := hEFT
    exact AlgebraicCurve.stichtenothGenusExists_of_isCurveOver hCAB
  exact ⟨hEFT, hRR,
    AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR hSGE,
    hCAB⟩

private theorem isPlaceReductionModL_sp
    (N : ℕ) [NeZero N]
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ)
    (hJ : ∃ x : JZero N, x ≠ 0) :
    IsPlaceReductionModL A N (fun P =>
      (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) ℓ N hℓN).symm ▸
        S.sp P) := by
  obtain ⟨R₀, -, hspec₀⟩ :=
    ModularCurve.exists_constantReduction_isGood_isPlaceReductionModL N hℓN A hA
  obtain ⟨hEFT, hRR, hWDA, hCAB⟩ := packFullC (ResidueField ↥A) ℓ N hℓN
  exact isPlaceReductionModL_sp_of_clauses N ℓ hℓN A hA data hKr hα hβ S hspec₀
    (ModularCurve.exists_finset_place_eq_of_ord_jqModC_sub_pos (ResidueField ↥A) ℓ N hℓN)
    (ModularCurve.IsPlaceReductionModL.coordinate_clauses N ℓ hℓN A hA R₀.placeMap hspec₀)
    hEFT hRR hWDA hCAB
    AlgebraicCurve.genus_eq_zero_of_isPrincipal_single_sub_single
    AlgebraicCurve.Divisor.isPrincipal_of_genus_eq_zero hJ

private theorem exists_constantReduction_placeMap_eq
    (N : ℕ) [NeZero N]
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ)
    (hJ : ∃ x : JZero N, x ≠ 0) :
    ∃ R : ConstantReduction A (modularFunctionFieldBar N)
        (modularFunctionFieldC (ResidueField ↥A) N), R.placeMap = S.sp :=
  exists_constantReduction_placeMap_eq_var N hℓN A hA (modularFunctionFieldC (ResidueField ↥A) N)
    (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) ℓ N hℓN).symm S.sp
    (isPlaceReductionModL_sp N ℓ hℓN A hA data hKr hα hβ S hJ)

private theorem nonempty_constantReduction (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)] :
    Nonempty (ConstantReduction A (modularFunctionFieldBar N) (modularFunctionFieldC (ResidueField ↥A) N)) := by
  have key : ∀ (Y : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))),
      modularFunctionFieldFullC (ResidueField ↥A) N = Y →
        Nonempty (ConstantReduction A (modularFunctionFieldBar N) ↥Y) := by
    intro Y hY
    subst hY
    obtain ⟨R₀, -, -⟩ := ModularCurve.exists_constantReduction_isGood_isPlaceReductionModL N hℓN A hA
    exact ⟨R₀⟩
  exact key _ (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) ℓ N hℓN).symm

private theorem natCast_level_ne_zero (k : Type) [Field k] (ℓ : ℕ) [CharP k ℓ] [Fact ℓ.Prime]
    (N : ℕ) [NeZero N] (hℓN : ¬ ℓ ∣ N) : ((N : ℕ) : k) ≠ 0 := by
  intro h0
  exact hℓN ((CharP.cast_eq_zero_iff k ℓ N).mp h0)

private theorem genusFF_modularFunctionFieldC_eq (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [CharP k ℓ]
    [Fact ℓ.Prime] (N : ℕ) [NeZero N] (hℓN : ¬ ℓ ∣ N) :
    AlgebraicCurve.genusFF k (ModularCurve.modularFunctionFieldC k N) =
      AlgebraicCurve.genusFF (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) :=
  (AlgebraicCurve.genusFF_eq_of_algEquiv
    (IntermediateField.equivOfEq
      (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k ℓ N hℓN))).trans
    (ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
      k N (natCast_level_ne_zero k ℓ N hℓN))

private theorem pic0Map_eq_spPic0_of_placeMap_eq
    {N : ℕ} [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    [CharP (ResidueField ↥A) ℓ]
    (S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    (R : ConstantReduction A (modularFunctionFieldBar N) (modularFunctionFieldC (ResidueField ↥A) N))
    (h : R.placeMap = S.sp) : R.pic0Map = S.spPic0 := by
  refine AddMonoidHom.ext fun c => ?_
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  obtain ⟨D', hD', hsp⟩ := S.spPic0_compat D
  rw [ConstantReduction.pic0Map_mk, hsp]
  congr 1
  exact Subtype.ext (by rw [ConstantReduction.coe_degZeroMap, hD', h])

end SpecializationComparison

namespace SpecializationComparison

private theorem divisor_congr_refl_mapDomain {k : Type*} [Field k]
    (F : IntermediateField k (LaurentSeries k)) {X : Type*} (sp : X → Place k F) (D : X →₀ ℤ) :
    Divisor.congr (IntermediateField.equivOfEq (rfl : F = F)).toRingEquiv
        (fun a => (IntermediateField.equivOfEq (rfl : F = F)).commutes a) (Finsupp.mapDomain sp D)
      = Finsupp.mapDomain sp D := by
  have hid : Place.congrEquiv (IntermediateField.equivOfEq (rfl : F = F)).toRingEquiv
      (fun a => (IntermediateField.equivOfEq (rfl : F = F)).commutes a) = Equiv.refl _ :=
    Equiv.ext fun v => by
      ext1
      exact SetLike.ext fun x => Iff.rfl
  show Finsupp.domCongr (Place.congrEquiv (IntermediateField.equivOfEq (rfl : F = F)).toRingEquiv
      (fun a => (IntermediateField.equivOfEq (rfl : F = F)).commutes a)) (Finsupp.mapDomain sp D)
    = Finsupp.mapDomain sp D
  rw [hid, Finsupp.domCongr_refl, AddEquiv.refl_apply]

private theorem divisor_congr_mapDomain_var (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ∀ (Y : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
      (hY : modularFunctionFieldFullC (ResidueField ↥A) N = Y)
      (sp : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (ResidueField ↥A) ↥Y)
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      Divisor.congr (IntermediateField.equivOfEq hY.symm).toRingEquiv
          (fun a => (IntermediateField.equivOfEq hY.symm).commutes a) (Finsupp.mapDomain sp D)
        = Finsupp.mapDomain (fun P => (hY ▸ sp P : Place (ResidueField ↥A)
            (modularFunctionFieldFullC (ResidueField ↥A) N))) D := by
  intro Y hY sp D
  subst hY
  exact divisor_congr_refl_mapDomain _ sp D

private theorem pic0_congr_mk {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.congr e he (Pic0.mk D) = Pic0.mk (Pic0.degZeroCongr e he D) :=
  rfl

private theorem pic0_mk_eq_congr_symm_mk {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    (D : Divisor.degZero (K := K) (F := F)) (R : Divisor.degZero (K := K) (F := F'))
    (h : Divisor.congr e he (D : Divisor K F) = (R : Divisor K F')) :
    Pic0.mk D = (Pic0.congr e he).symm (Pic0.mk R) :=
  (AddEquiv.eq_symm_apply (Pic0.congr e he)).mpr
    ((pic0_congr_mk e he D).trans
      (congrArg Pic0.mk (Subtype.ext ((Pic0.coe_degZeroCongr e he D).trans h))))

private theorem map_zero_eq_congr_symm_map_zero {J K F F' : Type*} [AddZeroClass J] [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] (e : F ≃+* F')
    (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a) (f : J →+ Pic0 K F) (g : J →+ Pic0 K F') :
    f 0 = (Pic0.congr e he).symm (g 0) :=
  (map_zero f).trans
    ((map_zero (Pic0.congr e he).symm).symm.trans
      (congrArg (fun t => (Pic0.congr e he).symm t) (map_zero g).symm))

private theorem spPic0_eq_reductionModL_pos
    (N : ℕ) [NeZero N]
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ)
    (hJ : ∃ x : JZero N, x ≠ 0) (x : JZero N) :
    S.spPic0 x = (Pic0.congr
          (IntermediateField.equivOfEq
            (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) ℓ N
              hℓN)).toRingEquiv
          (fun a => (IntermediateField.equivOfEq
            (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) ℓ N
              hℓN)).commutes a)).symm (reductionModL A N x) := by
  have hsp := isPlaceReductionModL_sp N ℓ hℓN A hA data hKr hα hβ S hJ
  have hin : ReductionInputsModL A N := ModularCurve.reductionInputsModL_of_not_dvd N hℓN A hA
  have hr₀ := isPlaceReductionModL_placeReductionModL hin
  have heq := placeMap_eq_of_agree N hℓN A hA (agree_of_two_specs hsp hr₀) (hnc_of_spec N hℓN A hA hsp)
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  obtain ⟨D', hD', hspD⟩ := S.spPic0_compat D
  rw [hspD, reductionModL_mk hin]
  refine pic0_mk_eq_congr_symm_mk _ _ D' _ ?_
  rw [hD', coe_reductionDegZeroAlong, ← heq]
  exact divisor_congr_mapDomain_var N A (modularFunctionFieldC (ResidueField ↥A) N)
    (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) ℓ N hℓN).symm
    S.sp (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))

end SpecializationComparison

theorem solution
    (N : ℕ) [NeZero N]
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ) :
    ∀ x : JZero N,
      S.spPic0 x =
        (Pic0.congr
          (IntermediateField.equivOfEq
            (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) ℓ N
              hℓN)).toRingEquiv
          (fun a => (IntermediateField.equivOfEq
            (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) ℓ N
              hℓN)).commutes a)).symm (reductionModL A N x) := by
  intro x
  by_cases hJ : ∃ x : JZero N, x ≠ 0
  · exact SpecializationComparison.spPic0_eq_reductionModL_pos N ℓ hℓN A hA data hKr hα hβ S hJ x
  ·
    have h0 : x = 0 := by_contra fun hx0 => hJ ⟨x, hx0⟩
    rw [h0]
    exact SpecializationComparison.map_zero_eq_congr_symm_map_zero _ _ S.spPic0 (reductionModL A N)

end S_ModularCurve_PlaceSpecialization_spPic0_eq_reductionModL
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_spPic0_eq_reductionModL (solution)
