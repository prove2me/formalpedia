-- Prove2me | solution 1 for ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e935fea8-0e61-50b6-8267-67b7586f5310

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver
import Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_ModularCurve_card_fibres_jqModC_modularFunctionFieldFullC_eq
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_mul_mem_lSpace_add
import Theorems.Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ModularCurve_exists_mem_integers_transcendental_residue_finrank_eq_of_regularProlongation_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

noncomputable section

section DeuringEngine

open AlgebraicCurve IsLocalRing Polynomial IntermediateField

namespace W9SFiveLe
namespace DeuringLE

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def placeOfValuationSubring (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (V : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ V) (hV : V ≠ ⊤) : Place K F where
  toValuationSubring := V
  algebraMap_mem' := hK
  ne_top' := hV
  isPrincipalIdealRing' :=
    ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin x V hK hV

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ v.toValuationSubring.zero_mem)
  by_contra h
  exact hf ((v.mem_iff_ord_nonneg hf0).mpr (not_lt.mp h))

theorem mem_valuationSubring_of_mem_lSpace (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) (m : ℕ) {f : F}
    (hf : f ∈ LSpace (m • D)) (V : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ V) :
    (x ∈ V → f ∈ V) ∧ (x ∉ V → f * (x ^ m)⁻¹ ∈ V) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp [V.zero_mem]
  by_cases hV : V = ⊤
  · subst hV
    exact ⟨fun _ => ValuationSubring.mem_top _, fun _ => ValuationSubring.mem_top _⟩
  set v : Place K F := placeOfValuationSubring x V hK hV with hv
  have hVv : v.toValuationSubring = V := rfl
  have hford : ∀ w : Place K F, -((m • D) w) ≤ w.ord f :=
    ((mem_lSpace_iff_ord.mp hf).resolve_left hf0)
  have hfv : -((m : ℤ) * D v) ≤ v.ord f := by
    have := hford v
    simpa [Finsupp.smul_apply, smul_eq_mul, nsmul_eq_mul] using this
  rw [hD v] at hfv
  constructor
  · intro hxV
    rcases eq_or_ne x 0 with rfl | hx0
    · have : (0 : ℤ) ≤ v.ord f := by simpa [Place.ord_zero] using hfv
      rw [← hVv]
      exact (v.mem_iff_ord_nonneg hf0).mpr this
    · have hxord : 0 ≤ v.ord x := (v.mem_iff_ord_nonneg hx0).mp (hVv ▸ hxV)
      have hmax : max 0 (-v.ord x) = 0 := max_eq_left (by linarith)
      rw [hmax, mul_zero, neg_zero] at hfv
      rw [← hVv]
      exact (v.mem_iff_ord_nonneg hf0).mpr hfv
  · intro hxV
    have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
    have hxord : v.ord x < 0 := ord_neg_of_not_mem v (hVv ▸ hxV)
    have hmax : max 0 (-v.ord x) = -v.ord x := max_eq_right (by linarith)
    rw [hmax] at hfv
    have hne : f * (x ^ m)⁻¹ ≠ 0 := mul_ne_zero hf0 (inv_ne_zero (pow_ne_zero _ hx0))
    rw [← hVv]
    refine (v.mem_iff_ord_nonneg hne).mpr ?_
    rw [v.ord_mul hf0 (inv_ne_zero (pow_ne_zero _ hx0)), v.ord_inv, ← zpow_natCast,
      v.ord_zpow]
    nlinarith

theorem exists_poleDivisor [HasPrincipalDivisors K F] {x : F} (hx : x ≠ 0) :
    ∃ D : Divisor K F, ∀ v : Place K F, D v = max 0 (-v.ord x) := by
  obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx
  exact ⟨Finsupp.mapRange (fun n => max 0 (-n)) (by simp) P, fun v => by simp [hP v]⟩

theorem nonempty_place_of_transcendental [IsAlgClosed K] {x : F} (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : Nonempty (Place K F) := by
  by_contra h
  have hx' : x ∈ (algebraMap K F).range :=
    Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x hx fun v => (h ⟨v⟩).elim
  obtain ⟨c, rfl⟩ := hx'
  exact hx (isAlgebraic_algebraMap c)

theorem finiteDimensional_lSpace_zero_of_constantsAreBase (hC : ConstantsAreBase K F) :
    FiniteDimensional K (LSpace (0 : Divisor K F)) := by
  have h : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
  rw [h]
  infer_instance

theorem genusFF_eq_of_riemannGenusReachedAt [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] (hC : ConstantsAreBase K F)
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    (genusFF K F : ℤ) = γ := by
  have h1 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [indexOfSpecialty_eq_finrank_H1, ell_zero_eq_one_of_constantsAreBase hC, map_zero] at h1
  rw [genusFF]
  push_cast at h1 ⊢
  linarith

end Generic

section Riemann

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mul_mem_lSpace_sub_of_forall_eq_ord {f : F} {P : Divisor K F}
    (hP : ∀ v : Place K F, P v = v.ord f) {E : Divisor K F} {g : F} (hg : g ∈ LSpace E) :
    g * f ∈ LSpace (E - P) := by
  have hfmem : f ∈ LSpace (-P) :=
    mem_lSpace_iff_ord.mpr (Or.inr fun v => by simp [hP v])
  simpa [sub_eq_add_neg] using mul_mem_lSpace_add hg hfmem

noncomputable def mulRight (f : F) (E E' : Divisor K F)
    (h : ∀ g ∈ LSpace E, g * f ∈ LSpace E') : LSpace E →ₗ[K] LSpace E' where
  toFun g := ⟨(g : F) * f, h g g.2⟩
  map_add' a b := Subtype.ext (by simp [add_mul])
  map_smul' c a := Subtype.ext (by simp)

theorem ell_sub_eq_of_forall_eq_ord {f : F} (hf0 : f ≠ 0) {P : Divisor K F}
    (hP : ∀ v : Place K F, P v = v.ord f) (E : Divisor K F) : ell (E - P) = ell E := by
  have h1 : ∀ g ∈ LSpace E, g * f ∈ LSpace (E - P) := fun g hg =>
    mul_mem_lSpace_sub_of_forall_eq_ord hP hg
  have hP' : ∀ v : Place K F, (-P) v = v.ord f⁻¹ := fun v => by simp [hP v, Place.ord_inv]
  have h2 : ∀ g ∈ LSpace (E - P), g * f⁻¹ ∈ LSpace E := fun g hg => by
    simpa using mul_mem_lSpace_sub_of_forall_eq_ord hP' hg
  let e : LSpace E ≃ₗ[K] LSpace (E - P) :=
    { mulRight f E (E - P) h1 with
      invFun := mulRight f⁻¹ (E - P) E h2
      left_inv := fun g => Subtype.ext (by simp [mulRight, mul_inv_cancel_right₀ hf0])
      right_inv := fun g => Subtype.ext (by simp [mulRight, inv_mul_cancel_right₀ hf0]) }
  exact (LinearEquiv.finrank_eq e).symm

theorem exists_forall_degree_nsmul_sub_ell_eq [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {γ : ℤ} {D₀ : Divisor K F}
    (h : RiemannGenusReachedAt γ D₀) {D : Divisor K F} (hD : 0 < Divisor.degree D) :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
      Divisor.degree (m • D) - (ell (m • D) : ℤ) = γ - 1 := by
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : ℕ, Divisor.degree D₀ + γ ≤ (m₁ : ℤ) * Divisor.degree D := by
    refine ⟨(Divisor.degree D₀ + γ).toNat, ?_⟩
    calc Divisor.degree D₀ + γ ≤ ((Divisor.degree D₀ + γ).toNat : ℤ) := Int.self_le_toNat _
      _ = ((Divisor.degree D₀ + γ).toNat : ℤ) * 1 := (mul_one _).symm
      _ ≤ ((Divisor.degree D₀ + γ).toNat : ℤ) * Divisor.degree D :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
  refine ⟨m₁, fun m hm => ?_⟩
  have hdegm : Divisor.degree (m • D) = (m : ℤ) * Divisor.degree D := by
    rw [map_nsmul, nsmul_eq_mul]
  have hineq := h.isMax (m • D - D₀)
  have hmm : (m₁ : ℤ) * Divisor.degree D ≤ (m : ℤ) * Divisor.degree D :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hD.le
  have hell_pos : 0 < ell (m • D - D₀) := by
    have : (1 : ℤ) ≤ ell (m • D - D₀) := by
      rw [map_sub, hdegm] at hineq
      linarith
    exact_mod_cast this
  haveI : FiniteDimensional K (LSpace (m • D - D₀)) := finiteDimensional_lSpace _
  obtain ⟨⟨f, hfmem⟩, hf0⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := LSpace (m • D - D₀))).mp hell_pos
  have hf0 : f ≠ 0 := fun h0 => hf0 (Subtype.ext h0)
  obtain ⟨P, hP, hP0⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hle : D₀ - P ≤ m • D := fun v => by
    have := (mem_lSpace_iff_ord.mp hfmem).resolve_left hf0 v
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_smul, Pi.smul_apply] at this ⊢
    rw [hP v]
    linarith
  have h' : RiemannGenusReachedAt γ (D₀ - P) :=
    { finite := finiteDimensional_lSpace _
      eq := by
        rw [ell_sub_eq_of_forall_eq_ord hf0 hP, map_sub, hP0, sub_zero]
        exact h.eq
      isMax := h.isMax }
  exact h'.eq_of_ge hle

end Riemann

section Prolongation

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constHom (R : RegularProlongation A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

theorem transcendental_coe [IsAlgClosed L] (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x)) : Transcendental L (x : F) := by
  intro halg
  have hint : IsIntegral L (x : F) := halg.isIntegral
  have h1 : (minpoly L (x : F)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one L (x : F) h1
  have hcA : c ∈ A := (R.algebraMap_mem_iff c).mp (hc ▸ x.2)
  apply hx
  have hxeq : x = constHom R ⟨c, hcA⟩ := Subtype.ext hc.symm
  rw [hxeq, residue_constHom]
  exact isAlgebraic_algebraMap _

theorem residue_mem_lSpace_nsmul (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    {D : Divisor L F} (hD : ∀ v : Place L F, D v = max 0 (-v.ord (x : F)))
    {Dbar : Divisor (ResidueField A) Fbar}
    (hDbar : ∀ w : Place (ResidueField A) Fbar, Dbar w = max 0 (-w.ord (R.residue x)))
    (m : ℕ) {f : R.integers} (hf : (f : F) ∈ LSpace (m • D)) :
    R.residue f ∈ LSpace (m • Dbar) := by
  obtain ⟨p, hp, hpdeg, hroot⟩ :=
    AlgebraicCurve.RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring
      A R x hx (f : F) m
      (fun V hV hxV => (mem_valuationSubring_of_mem_lSpace (x : F) D hD m hf V hV).1 hxV)
      (fun V hV hxV => (mem_valuationSubring_of_mem_lSpace (x : F) D hD m hf V hV).2 hxV)
      (fun V hV => by
        rw [AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff
          A R x hx hfin hdeg V hV]
        exact f.2)
  have hM := AlgebraicCurve.RegularProlongation.mul_min_ord_residue_le_of_monic
    A R x f m p hp hpdeg hroot
  refine mem_lSpace_iff_ord.mpr (Or.inr fun w => ?_)
  have h1 := hM w
  have h2 : -((m : ℤ) * Dbar w) = (m : ℤ) * min 0 (w.ord (R.residue x)) := by
    rw [hDbar w, ← mul_neg]
    congr 1
    rcases le_total 0 (w.ord (R.residue x)) with h0 | h0
    · rw [max_eq_left (by linarith), min_eq_left h0, neg_zero]
    · rw [max_eq_right (by linarith), min_eq_right h0, neg_neg]
  have h3 : (m • Dbar) w = (m : ℤ) * Dbar w := by simp
  rw [h3, h2]
  exact h1

end Prolongation

section GenusLE

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
  [IsCurveOver (ResidueField A) Fbar]

theorem genusFF_le (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar) :
    genusFF (ResidueField A) Fbar ≤ genusFF L F := by
  classical

  haveI hk : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : PerfectField (ResidueField A) := IsAlgClosed.perfectField _
  haveI : PerfectField L := IsAlgClosed.perfectField _
  have hxL : Transcendental L (x : F) := transcendental_coe R x hx
  haveI hfdb : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  haveI hfd : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  haveI : Nonempty (Place L F) := nonempty_place_of_transcendental hxL
  haveI : Nonempty (Place (ResidueField A) Fbar) := nonempty_place_of_transcendental hx
  have hC : ConstantsAreBase L F :=
    constantsAreBase_of_deg_eq_one (Classical.arbitrary (Place L F))
      (IsCurveOver.deg_eq_one_of_isAlgClosed _)
  have hCb : ConstantsAreBase (ResidueField A) Fbar :=
    constantsAreBase_of_deg_eq_one (Classical.arbitrary (Place (ResidueField A) Fbar))
      (IsCurveOver.deg_eq_one_of_isAlgClosed _)
  haveI : FiniteDimensional L (LSpace (0 : Divisor L F)) :=
    finiteDimensional_lSpace_zero_of_constantsAreBase hC
  haveI : FiniteDimensional (ResidueField A) (LSpace (0 : Divisor (ResidueField A) Fbar)) :=
    finiteDimensional_lSpace_zero_of_constantsAreBase hCb
  haveI : Algebra.EssFiniteType L F :=
    essFiniteType_of_transcendental_of_finiteDimensional hxL hfd
  haveI : Algebra.EssFiniteType (ResidueField A) Fbar :=
    essFiniteType_of_transcendental_of_finiteDimensional hx hfdb

  obtain ⟨-, -, γ, D₀, hR⟩ := stichtenothGenusExists_of_isCurveOver hC
  obtain ⟨-, -, γb, Db₀, hRb⟩ := stichtenothGenusExists_of_isCurveOver hCb
  have hγ : (genusFF L F : ℤ) = γ := genusFF_eq_of_riemannGenusReachedAt hC hR
  have hγb : (genusFF (ResidueField A) Fbar : ℤ) = γb :=
    genusFF_eq_of_riemannGenusReachedAt hCb hRb

  have hx0 : (x : F) ≠ 0 := fun h0 => hxL (h0 ▸ isAlgebraic_zero)
  have hxb0 : R.residue x ≠ 0 := fun h0 => hx (h0 ▸ isAlgebraic_zero)
  obtain ⟨D, hD⟩ := exists_poleDivisor (K := L) hx0
  obtain ⟨Db, hDb⟩ := exists_poleDivisor (K := ResidueField A) hxb0
  have hdegD := Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord (x : F) hxL D hD
  have hdegDb := Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord (R.residue x) hx Db hDb
  have hDD : Divisor.degree D = Divisor.degree Db := by rw [hdegD, hdegDb, hdeg]
  have hDbpos : 0 < Divisor.degree Db := by rw [hdegDb]; exact_mod_cast hfin

  obtain ⟨m, hm⟩ := exists_forall_degree_nsmul_sub_ell_eq hRb hDbpos
  have hexact : Divisor.degree (m • Db) - (ell (m • Db) : ℤ) = γb - 1 := hm m le_rfl

  have hRi : Divisor.degree (m • D) - (ell (m • D) : ℤ) ≤ γ - 1 := hR.isMax (m • D)
  have hdegm : Divisor.degree (m • D) = Divisor.degree (m • Db) := by
    rw [map_nsmul, map_nsmul, hDD]

  haveI : FiniteDimensional L (LSpace (m • D)) := finiteDimensional_lSpace _
  haveI : FiniteDimensional (ResidueField A) (LSpace (m • Db)) := finiteDimensional_lSpace _
  set S : Submodule (ResidueField A) Fbar := Submodule.span (ResidueField A)
    {h : Fbar | ∃ f : R.integers, (f : F) ∈ LSpace (m • D) ∧ R.residue f = h} with hS
  have hSle : S ≤ LSpace (m • Db) := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact residue_mem_lSpace_nsmul R x hx hfin hdeg hD hDb m hf
  have hfinS : Module.finrank (ResidueField A) S = Module.finrank L (LSpace (m • D)) :=
    AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank A R x hx hfin hdeg
      (LSpace (m • D))
  have hmono : Module.finrank (ResidueField A) S ≤
      Module.finrank (ResidueField A) (LSpace (m • Db)) := Submodule.finrank_mono hSle
  have hell : (ell (m • D) : ℤ) ≤ ell (m • Db) := by
    have : ell (m • D) ≤ ell (m • Db) := by
      change Module.finrank L (LSpace (m • D)) ≤ Module.finrank (ResidueField A) (LSpace (m • Db))
      rw [← hfinS]
      exact hmono
    exact_mod_cast this

  have hγle : γb ≤ γ := by linarith
  have : (genusFF (ResidueField A) Fbar : ℤ) ≤ genusFF L F := by rw [hγ, hγb]; exact hγle
  exact_mod_cast this

end GenusLE

end W9SFiveLe.DeuringLE
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe.DeuringLE"
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe"

end DeuringEngine
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe.DeuringLE"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve IsDedekindDomain WithZero

namespace W9SFiveLe

section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_ord_nonneg (w : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ w.ord f) :
    f ∈ w.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

theorem mem_of_ord_sub_pos (w : Place K F) {f : F} {c : K}
    (h : 0 < w.ord (f - algebraMap K F c)) : f ∈ w.toValuationSubring := by
  have hne : f - algebraMap K F c ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  have := add_mem (mem_of_ord_nonneg w hne h.le) (w.algebraMap_mem' c)
  rwa [sub_add_cancel] at this

theorem ord_eq_one_of_valuation_eq (w : Place K F) {v' : Valuation F ℤᵐ⁰}
    (hv' : v'.valuationSubring = w.toValuationSubring) {x : F} (hx : v' x = exp (-1 : ℤ)) :
    w.ord x = 1 := by
  have hE := w.isEquiv_adicValuation_of_valuationSubring_eq hv'
  have hx0 : v' x ≠ 0 := by rw [hx]; exact exp_ne_zero
  have hu0 : w.adicValuation x ≠ 0 := (hE.eq_zero).ne.mp hx0
  have hlt : w.adicValuation x < 1 := by
    refine hE.lt_one_iff_lt_one.mp ?_
    rw [hx, ← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)
  obtain ⟨ϖ, hϖ⟩ := w.heightOneSpectrum.valuation_exists_uniformizer F
  change w.adicValuation ϖ = exp (-1 : ℤ) at hϖ
  have hϖ0 : w.adicValuation ϖ ≠ 0 := by rw [hϖ]; exact exp_ne_zero
  have hϖlt : v' ϖ < 1 := by
    refine hE.lt_one_iff_lt_one.mpr ?_
    rw [hϖ, ← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)
  have hϖ0' : v' ϖ ≠ 0 := (hE.eq_zero).ne.mpr hϖ0
  have hϖle : v' ϖ ≤ v' x := by
    rw [hx, ← log_le_iff_le_exp hϖ0']
    have hlog : log (v' ϖ) < 0 := (log_lt_iff_lt_exp hϖ0').mpr (by rw [exp_zero]; exact hϖlt)
    omega
  have hge : exp (-1 : ℤ) ≤ w.adicValuation x := by
    rw [← hϖ]
    exact (hE ϖ x).mp hϖle
  have hle' : log (w.adicValuation x) ≤ -1 := by
    have hlog : log (w.adicValuation x) < 0 :=
      (log_lt_iff_lt_exp hu0).mpr (by rw [exp_zero]; exact hlt)
    omega
  have hge' : -1 ≤ log (w.adicValuation x) := (le_log_iff_exp_le hu0).mpr hge
  simp only [Place.ord]
  omega

theorem adicValuation_lt_one_of_ord_pos (w : Place K F) {g : F} (h : 0 < w.ord g) :
    w.adicValuation g < 1 := by
  have hg : g ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at h
    exact lt_irrefl _ h
  have h0 : w.adicValuation g ≠ 0 := w.adicValuation_ne_zero hg
  rw [← exp_zero, ← log_lt_iff_lt_exp h0]
  simp only [Place.ord] at h
  omega

theorem eq_zero_of_ord_pos_of_ord_sub_pos (w : Place K F) {f : F} {c : K}
    (h1 : 0 < w.ord f) (h2 : 0 < w.ord (f - algebraMap K F c)) : c = 0 := by
  by_contra hc
  have hv1 := adicValuation_lt_one_of_ord_pos w h1
  have hv2 := adicValuation_lt_one_of_ord_pos w h2
  have hone : w.adicValuation (algebraMap K F c) = 1 :=
    Valuation.IsTrivialOn.eq_one (v := w.adicValuation) c hc
  have hle := Valuation.map_sub w.adicValuation f (f - algebraMap K F c)
  rw [sub_sub_cancel, hone] at hle
  exact absurd (lt_of_le_of_lt hle (max_lt hv1 hv2)) (lt_irrefl _)

scoped instance instIsPrincipalIdealRingAdjoinSingleton (t : F) :
    IsPrincipalIdealRing (Algebra.adjoin K ({t} : Set F)) := by
  have hmem : ∀ p : Polynomial K, Polynomial.aeval t p ∈ Algebra.adjoin K ({t} : Set F) := by
    intro p
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  refine IsPrincipalIdealRing.of_surjective
    ((Polynomial.aeval t).codRestrict (Algebra.adjoin K ({t} : Set F)) hmem) ?_
  rintro ⟨a, ha⟩
  obtain ⟨p, hp⟩ : ∃ p : Polynomial K, Polynomial.aeval t p = a := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    exact (AlgHom.mem_range _).mp ha
  exact ⟨p, Subtype.ext hp⟩

def linGen (t : F) (c : K) : Algebra.adjoin K ({t} : Set F) :=
  ⟨t, Algebra.self_mem_adjoin_singleton K t⟩ - algebraMap K _ c

@[scoped simp] theorem coe_linGen (t : F) (c : K) :
    ((linGen t c : Algebra.adjoin K ({t} : Set F)) : F) = t - algebraMap K F c := by
  simp [linGen]

section Transcendental

variable (t : F) (htr : Transcendental K t)

include htr in
theorem linGen_ne_zero (c : K) : linGen t c ≠ 0 := by
  intro h
  have h' := congrArg (fun a : Algebra.adjoin K ({t} : Set F) => (a : F)) h
  simp only [coe_linGen, ZeroMemClass.coe_zero, sub_eq_zero] at h'
  exact htr (by rw [h']; exact isAlgebraic_algebraMap c)

def polyEquiv : Polynomial K ≃ₐ[K] Algebra.adjoin K ({t} : Set F) :=
  (AlgEquiv.ofInjective (Polynomial.aeval t) (transcendental_iff_injective.mp htr)).trans
    (Subalgebra.equivOfEq _ _ (by rw [Algebra.adjoin_singleton_eq_range_aeval]))

theorem polyEquiv_X_sub_C (c : K) :
    polyEquiv t htr (Polynomial.X - Polynomial.C c) = linGen t c := by
  apply Subtype.ext
  rw [coe_linGen]
  simp [polyEquiv, Subalgebra.equivOfEq_apply, AlgEquiv.ofInjective_apply]

include htr in

theorem prime_linGen (c : K) : Prime (linGen t c) := by
  rw [← polyEquiv_X_sub_C t htr c, MulEquiv.prime_iff]
  exact Polynomial.prime_X_sub_C c

def linPrime (c : K) : HeightOneSpectrum (Algebra.adjoin K ({t} : Set F)) :=
  ⟨Ideal.span {linGen t c}, (Ideal.span_singleton_prime (linGen_ne_zero t htr c)).mpr
    (prime_linGen t htr c), by
      rw [ne_eq, Ideal.span_singleton_eq_bot]
      exact linGen_ne_zero t htr c⟩

open scoped IntermediateField.algebraAdjoinAdjoin

def basePlace (c : K) : Place K (IntermediateField.adjoin K ({t} : Set F)) :=
  Place.ofHeightOneSpectrum (K := K) (linPrime t htr c)

theorem algebraMap_linGen (c : K) :
    algebraMap (Algebra.adjoin K ({t} : Set F)) (IntermediateField.adjoin K ({t} : Set F))
        (linGen t c) =
      IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c := by
  apply Subtype.ext
  rw [IntermediateField.algebraAdjoinAdjoin.coe_algebraMap, coe_linGen]
  simp

theorem ord_basePlace (c : K) :
    (basePlace t htr c).ord (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) = 1 := by
  rw [← algebraMap_linGen]
  refine ord_eq_one_of_valuation_eq (basePlace t htr c)
    (v' := (linPrime t htr c).valuation (IntermediateField.adjoin K ({t} : Set F))) rfl ?_
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (linPrime t htr c).intValuation_singleton (linGen_ne_zero t htr c) rfl

theorem forall_algebraMap_mem (v : Place K (IntermediateField.adjoin K ({t} : Set F)))
    (ht : IntermediateField.AdjoinSimple.gen K t ∈ v.toValuationSubring)
    (r : Algebra.adjoin K ({t} : Set F)) :
    algebraMap (Algebra.adjoin K ({t} : Set F)) (IntermediateField.adjoin K ({t} : Set F)) r ∈
      v.toValuationSubring := by
  obtain ⟨x, hx⟩ := r
  show (⟨x, IntermediateField.algebra_adjoin_le_adjoin K _ hx⟩ :
      IntermediateField.adjoin K ({t} : Set F)) ∈ v.toValuationSubring
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    have hy' : y = t := Set.mem_singleton_iff.mp hy
    subst hy'
    exact ht
  | algebraMap a => exact v.algebraMap_mem' a
  | add y z hy hz ihy ihz => exact add_mem ihy ihz
  | mul y z hy hz ihy ihz => exact mul_mem ihy ihz

include htr in

theorem eq_basePlace_of_ord_pos (v : Place K (IntermediateField.adjoin K ({t} : Set F))) (c : K)
    (hv : 0 < v.ord (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c)) :
    v = basePlace t htr c := by
  have ht : IntermediateField.AdjoinSimple.gen K t ∈ v.toValuationSubring := mem_of_ord_sub_pos v hv
  have hw := forall_algebraMap_mem t v ht
  have hmem : linGen t c ∈ Place.center (Algebra.adjoin K ({t} : Set F)) v hw := by
    rw [Place.mem_center_iff_ord_pos v hw (linGen_ne_zero t htr c), algebraMap_linGen]
    exact hv
  have hcenter : Place.center (Algebra.adjoin K ({t} : Set F)) v hw = Ideal.span {linGen t c} := by
    haveI : (Ideal.span {linGen t c}).IsPrime := (linPrime t htr c).isPrime
    have hmax : (Ideal.span {linGen t c}).IsMaximal :=
      IsPrime.to_maximal_ideal (linPrime t htr c).ne_bot
    exact (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm
  have hc : Place.centerHeightOneSpectrum (Algebra.adjoin K ({t} : Set F)) v hw =
      linPrime t htr c := HeightOneSpectrum.ext hcenter
  apply Place.ext
  rw [v.toValuationSubring_eq_of_forall_mem hw, hc,
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rfl

theorem algebraMap_gen_sub (c : K) :
    algebraMap (IntermediateField.adjoin K ({t} : Set F)) F
        (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) =
      t - algebraMap K F c := by
  rw [map_sub, IntermediateField.AdjoinSimple.algebraMap_gen,
    ← IsScalarTower.algebraMap_apply]

variable [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]

theorem ord_sub_eq_mul (w : Place K F) (c : K) :
    w.ord (t - algebraMap K F c) =
      w.ramificationIndex (IntermediateField.adjoin K ({t} : Set F)) *
        (w.restrict (IntermediateField.adjoin K ({t} : Set F))).ord
          (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) := by
  rw [← algebraMap_gen_sub t c, Place.ord_restrict]

include htr in

theorem restrict_eq_basePlace_iff (w : Place K F) (c : K) :
    w.restrict (IntermediateField.adjoin K ({t} : Set F)) = basePlace t htr c ↔
      0 < w.ord (t - algebraMap K F c) := by
  constructor
  · intro h
    rw [ord_sub_eq_mul t w c, h, ord_basePlace, mul_one]
    exact_mod_cast w.ramificationIndex_pos (F := IntermediateField.adjoin K ({t} : Set F))
  · intro h
    refine eq_basePlace_of_ord_pos t htr _ c ?_
    rw [ord_sub_eq_mul t w c] at h
    exact (pos_iff_pos_of_mul_pos h).mp
      (by exact_mod_cast w.ramificationIndex_pos (F := IntermediateField.adjoin K ({t} : Set F)))

include htr in

theorem ramificationIndex_eq_ord (w : Place K F) (c : K) (h : 0 < w.ord (t - algebraMap K F c)) :
    (w.ramificationIndex (IntermediateField.adjoin K ({t} : Set F)) : ℤ) =
      w.ord (t - algebraMap K F c) := by
  rw [ord_sub_eq_mul t w c, (restrict_eq_basePlace_iff t htr w c).mpr h, ord_basePlace, mul_one]

theorem inertiaDeg_eq_one (w : Place K F) (hw : w.deg = 1) :
    w.inertiaDeg (IntermediateField.adjoin K ({t} : Set F)) = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := IntermediateField.adjoin K ({t} : Set F))
  rw [hw] at h
  exact Nat.eq_one_of_mul_eq_one_left h

variable [Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F]

include htr in

theorem sum_ord_sub_eq_finrank (hdeg : ∀ w : Place K F, w.deg = 1) (c : K)
    (S : Finset (Place K F)) (hS : ∀ w, w ∈ S ↔ 0 < w.ord (t - algebraMap K F c)) :
    ∑ w ∈ S, w.ord (t - algebraMap K F c) =
      Module.finrank (IntermediateField.adjoin K ({t} : Set F)) F := by
  have hSfib : S = (basePlace t htr c).fiberOver F := by
    ext w
    rw [hS, Place.mem_fiberOver, restrict_eq_basePlace_iff t htr]
  have hsum := Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := F) (basePlace t htr c)
  rw [← hSfib] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [inertiaDeg_eq_one t w (hdeg w), Nat.cast_one, mul_one,
    ramificationIndex_eq_ord t htr w c ((hS w).mp hw)]

include htr in

theorem exists_finset_ord_sub_pos (c : K) :
    ∃ S : Finset (Place K F), ∀ w, w ∈ S ↔ 0 < w.ord (t - algebraMap K F c) :=
  ⟨(basePlace t htr c).fiberOver F, fun w => by
    rw [Place.mem_fiberOver, restrict_eq_basePlace_iff t htr]⟩

end Transcendental
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe.DeuringLE"

end Engine
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe.DeuringLE"

theorem genusFormula_le_of_hurwitz (N : ℕ) {g s₀ s₁ t : ℕ}
    (h₀ : 3 * s₀ = dedekindPsi N + 2 * nuThree N) (h₁ : 2 * s₁ = dedekindPsi N + nuTwo N)
    (ht : t = cuspCount N)
    (hRH : ((dedekindPsi N : ℤ) - s₀) + ((dedekindPsi N : ℤ) - s₁) + ((dedekindPsi N : ℤ) - t) ≤
      2 * (g : ℤ) - 2 + 2 * (dedekindPsi N : ℤ)) :
    genusFormula N ≤ (g : ℚ) := by
  have h₀' : (3 : ℚ) * s₀ = dedekindPsi N + 2 * nuThree N := by exact_mod_cast h₀
  have h₁' : (2 : ℚ) * s₁ = dedekindPsi N + nuTwo N := by exact_mod_cast h₁
  have hRH' : ((dedekindPsi N : ℚ) - s₀) + ((dedekindPsi N : ℚ) - s₁) + ((dedekindPsi N : ℚ) - t) ≤
      2 * (g : ℚ) - 2 + 2 * (dedekindPsi N : ℚ) := by exact_mod_cast hRH
  subst ht
  unfold genusFormula
  linarith

section LowerBound

variable (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N]

abbrev JJ : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

omit [IsAlgClosed K] [NeZero N] in
theorem transcendental_JJ : Transcendental K (JJ K N) := by
  have h : Transcendental K
      (algebraMap (modularFunctionFieldFullC K N) (LaurentSeries K) (JJ K N)) :=
    ModularCurve.transcendental_jqModC K
  exact (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective _ _)).mp h

omit [IsAlgClosed K] in
theorem finrank_adjoin_JJ (hN : (N : K) ≠ 0) :
    Module.finrank (IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) = dedekindPsi N :=
  ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN

omit [IsAlgClosed K] in
theorem finiteDimensional_adjoin_JJ (hN : (N : K) ≠ 0) :
    FiniteDimensional
      (IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) :=
  Module.finite_of_finrank_pos
    (by rw [finrank_adjoin_JJ K N hN]; exact ModularCurve.dedekindPsi_pos N (NeZero.ne N))

omit [IsAlgClosed K] [NeZero N] in
theorem adjoin_inv_JJ_eq :
    IntermediateField.adjoin K ({(JJ K N)⁻¹} : Set (modularFunctionFieldFullC K N)) =
      IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K _)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h := inv_mem (IntermediateField.mem_adjoin_simple_self K (JJ K N)⁻¹)
    rwa [inv_inv] at h

omit [IsAlgClosed K] [NeZero N] in

theorem ord_inftyPlace_inv_JJ :
    (qInftyPlaceMod K (jqModC_mem_full K N)).ord (JJ K N)⁻¹ = 1 := by
  rw [ord_qInftyPlaceMod]
  exact order_jModInvElt K (jqModC_mem_full K N)

theorem isSeparable_adjoin_JJ (hN : (N : K) ≠ 0) :
    Algebra.IsSeparable
      (IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) := by
  haveI := finiteDimensional_adjoin_JJ K N hN
  haveI : Algebra.IsAlgebraic
      (IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) := Algebra.IsAlgebraic.of_finite _ _
  have h := Place.isSeparable_adjoin_of_ord_eq_one (K := K) (JJ K N)
    (qInftyPlaceMod K (jqModC_mem_full K N)) (ord_inftyPlace_inv_JJ K N)
  rwa [adjoin_inv_JJ_eq] at h

variable {K} in
omit [IsAlgClosed K] in
theorem natCast_ne_zero_of_not_dvd {ℓ : ℕ} [CharP K ℓ] {m : ℕ} (h : ¬ ℓ ∣ m) : (m : K) ≠ 0 :=
  fun h0 => h ((CharP.cast_eq_zero_iff K ℓ m).mp h0)

omit [IsAlgClosed K] in
theorem two_ne_zero_of_five_le {ℓ : ℕ} [CharP K ℓ] (hℓ : 5 ≤ ℓ) : (2 : K) ≠ 0 := by
  have h : ¬ ℓ ∣ 2 := fun h => by have := Nat.le_of_dvd two_pos h; omega
  exact_mod_cast natCast_ne_zero_of_not_dvd (K := K) h

omit [IsAlgClosed K] in
theorem three_ne_zero_of_five_le {ℓ : ℕ} [CharP K ℓ] (hℓ : 5 ≤ ℓ) : (3 : K) ≠ 0 := by
  have h : ¬ ℓ ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  exact_mod_cast natCast_ne_zero_of_not_dvd (K := K) h

theorem genusFormula_le_genusFF {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hℓ : 5 ≤ ℓ)
    (hN : (N : K) ≠ 0) :
    genusFormula N ≤ (genusFF K (modularFunctionFieldFullC K N) : ℚ) := by
  classical
  haveI hfin := finiteDimensional_adjoin_JJ K N hN
  haveI hsep := isSeparable_adjoin_JJ K N hN
  have htr := transcendental_JJ K N
  have hψ := finrank_adjoin_JJ K N hN
  haveI := ModularCurve.isCurveOver_modularFunctionFieldFullC K N
  have hdeg : ∀ w : Place K (modularFunctionFieldFullC K N), w.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  have h2 := two_ne_zero_of_five_le K hℓ
  have h3 := three_ne_zero_of_five_le K hℓ
  have h6N : ((6 * N : ℕ) : K) ≠ 0 := by
    have h6 : (6 : K) = 2 * 3 := by norm_num
    push_cast
    rw [h6]
    exact mul_ne_zero (mul_ne_zero h2 h3) hN
  have h1728 : (1728 : K) ≠ 0 := by
    have : (1728 : K) = 2 ^ 6 * 3 ^ 3 := by norm_num
    rw [this]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

  obtain ⟨S0, hS0⟩ := exists_finset_ord_sub_pos (JJ K N) htr (0 : K)
  obtain ⟨S1, hS1⟩ := exists_finset_ord_sub_pos (JJ K N) htr (1728 : K)
  have hS0' : ∀ P, P ∈ S0 ↔ 0 < P.ord (JJ K N) := fun P => by
    rw [hS0, map_zero, sub_zero]

  have heq := adjoin_inv_JJ_eq K N
  haveI hfin' : FiniteDimensional
      (IntermediateField.adjoin K ({(JJ K N)⁻¹} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) := by rw [heq]; exact hfin
  haveI hsep' : Algebra.IsSeparable
      (IntermediateField.adjoin K ({(JJ K N)⁻¹} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) := by rw [heq]; exact hsep
  have htr' : Transcendental K (JJ K N)⁻¹ := fun h => htr (IsAlgebraic.inv_iff.mp h)
  have hψ' : Module.finrank
      (IntermediateField.adjoin K ({(JJ K N)⁻¹} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) = dedekindPsi N := by rw [heq]; exact hψ
  obtain ⟨T, hT⟩ := exists_finset_ord_sub_pos (JJ K N)⁻¹ htr' (0 : K)
  have hT' : ∀ P, P ∈ T ↔ P.ord (JJ K N) < 0 := fun P => by
    rw [hT, map_zero, sub_zero, Place.ord_inv, neg_pos]

  obtain ⟨hc0, hc1, hcT⟩ :=
    ModularCurve.card_fibres_jqModC_modularFunctionFieldFullC_eq K N h6N S0 S1 T hS0' hS1 hT'

  have hsum0 : ∑ P ∈ S0, P.ord (JJ K N) = dedekindPsi N := by
    have h := sum_ord_sub_eq_finrank (JJ K N) htr hdeg 0 S0 hS0
    simp only [map_zero, sub_zero] at h
    rw [hψ] at h
    exact h
  have hsum1 : ∑ P ∈ S1, P.ord (JJ K N - algebraMap K _ 1728) = dedekindPsi N := by
    have h := sum_ord_sub_eq_finrank (JJ K N) htr hdeg 1728 S1 hS1
    rw [hψ] at h
    exact h
  have hsumT : ∑ P ∈ T, (-P.ord (JJ K N)) = dedekindPsi N := by
    have h := sum_ord_sub_eq_finrank (JJ K N)⁻¹ htr' hdeg 0 T hT
    simp only [map_zero, sub_zero, Place.ord_inv] at h
    rw [hψ'] at h
    exact h

  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro P h0 h1
    exact h1728 (eq_zero_of_ord_pos_of_ord_sub_pos P ((hS0' P).mp h0) ((hS1 P).mp h1))

  have hRH : ∑ P ∈ S0 ∪ S1, (P.ord (JJ K N - algebraMap K _ (if P ∈ S0 then (0 : K) else 1728)) - 1)
      + ∑ P ∈ T, (-P.ord (JJ K N) - 1) ≤
      2 * (genusFF K (modularFunctionFieldFullC K N) : ℤ) - 2 +
        2 * (Module.finrank
          (IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)))
          (modularFunctionFieldFullC K N) : ℤ) :=
    AlgebraicCurve.sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable K (JJ K N) htr
      hfin hsep (S0 ∪ S1) (fun P => if P ∈ S0 then 0 else 1728)
      (by
        intro P hP
        rcases Finset.mem_union.mp hP with h | h
        · rw [if_pos h, map_zero, sub_zero]
          exact (hS0' P).mp h
        · rw [if_neg (Finset.disjoint_right.mp hdisj h)]
          exact (hS1 P).mp h)
      T (fun P hP => (hT' P).mp hP)
  rw [Finset.sum_union hdisj, hψ] at hRH
  have e0 : ∑ P ∈ S0, (P.ord (JJ K N - algebraMap K _ (if P ∈ S0 then (0 : K) else 1728)) - 1) =
      (dedekindPsi N : ℤ) - S0.card := by
    rw [Finset.sum_congr rfl (g := fun P => P.ord (JJ K N) - 1)
      (fun P hP => by rw [if_pos hP, map_zero, sub_zero]), Finset.sum_sub_distrib, hsum0]
    simp
  have e1 : ∑ P ∈ S1, (P.ord (JJ K N - algebraMap K _ (if P ∈ S0 then (0 : K) else 1728)) - 1) =
      (dedekindPsi N : ℤ) - S1.card := by
    rw [Finset.sum_congr rfl (g := fun P => P.ord (JJ K N - algebraMap K _ 1728) - 1)
      (fun P hP => by rw [if_neg (Finset.disjoint_right.mp hdisj hP)]), Finset.sum_sub_distrib,
      hsum1]
    simp
  have eT : ∑ P ∈ T, (-P.ord (JJ K N) - 1) = (dedekindPsi N : ℤ) - T.card := by
    rw [Finset.sum_sub_distrib, hsumT]
    simp
  rw [e0, e1, eT] at hRH
  exact genusFormula_le_of_hurwitz N hc0 hc1 hcT hRH

end LowerBound
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe.DeuringLE"

section Core

theorem genusFF_fullC_residueField_le (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    genusFF (IsLocalRing.ResidueField A)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) ≤
      genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by
  haveI hk : IsAlgClosed (IsLocalRing.ResidueField A) :=
    ValuationSubring.isAlgClosed_residueField A
  haveI : PerfectField (IsLocalRing.ResidueField A) := IsAlgClosed.perfectField _
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI : IsCurveOver (IsLocalRing.ResidueField A)
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :=
    ModularCurve.isCurveOver_modularFunctionFieldFullC (IsLocalRing.ResidueField A) N

  obtain ⟨R, hspec⟩ := ModularCurve.exists_regularProlongation_modularFunctionFieldBar N hℓN A hA

  obtain ⟨x, hx, hfin, hdeg⟩ :=
    ModularCurve.exists_mem_integers_transcendental_residue_finrank_eq_of_regularProlongation_modularFunctionFieldBar
      N ℓ hℓN A hA R hspec
  exact DeuringLE.genusFF_le R x hx hfin hdeg

theorem genusFF_bar_eq_genusFormula (N : ℕ) [NeZero N] :
    (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℚ) = genusFormula N := by
  haveI := ModularCurve.hasCanonicalDivisor_modularFunctionFieldBar N
  rw [← ModularCurve.genus_eq_genusFF_modularFunctionFieldBar N]
  exact ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula N

theorem charP_residueField {L : Type*} [Field L] (A : ValuationSubring L) {ℓ : ℕ} [Fact ℓ.Prime]
    (hA : A.LiesOverPrime ℓ) : CharP (IsLocalRing.ResidueField A) ℓ := by
  have hℓ : ((ℓ : A) : L) ∈ A.nonunits := by simpa [ValuationSubring.LiesOverPrime] using hA
  rw [ValuationSubring.coe_mem_nonunits_iff] at hℓ
  have h0 : (ℓ : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hℓ
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0

theorem genusFF_fullC_residueField_eq (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    genusFF (IsLocalRing.ResidueField A)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) =
      genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by
  haveI := ValuationSubring.isAlgClosed_residueField A
  haveI := charP_residueField A hA
  have hN : (N : IsLocalRing.ResidueField A) ≠ 0 := natCast_ne_zero_of_not_dvd hℓN
  have hle := genusFF_fullC_residueField_le N hℓN A hA
  have hge := genusFormula_le_genusFF (IsLocalRing.ResidueField A) N hℓ hN
  rw [← genusFF_bar_eq_genusFormula N] at hge
  have hge' : genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ≤
      genusFF (IsLocalRing.ResidueField A)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) := by exact_mod_cast hge
  omega

end Core
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe.DeuringLE"

section Glue

variable {k K : Type*} [Field k] [Field K] (φ : k →+* K) (N : ℕ) [NeZero N]

theorem coeffMap_algebraMap_const (c : k) :
    coeffMap φ (algebraMap k (LaurentSeries k) c) = algebraMap K (LaurentSeries K) (φ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

omit [NeZero N] in

theorem coeffMap_mem_fullC {x : LaurentSeries k} (hx : x ∈ modularFunctionFieldFullC k N) :
    coeffMap φ x ∈ modularFunctionFieldFullC K N := by
  change x ∈ IntermediateField.adjoin k (divisorExpansionsC k N) at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨d, hd, hdN, rfl⟩ := hx
    rw [ModularCurve.coeffMap_qExpand, coeffMap_jqModC]
    exact jqModCd_mem_full K N hdN
  | algebraMap c =>
    rw [coeffMap_algebraMap_const]
    exact IntermediateField.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | inv x _ hx =>
    rw [map_inv₀]
    exact inv_mem hx
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

def fullCMap : modularFunctionFieldFullC k N →+* modularFunctionFieldFullC K N :=
  ((coeffMap φ).comp (modularFunctionFieldFullC k N).val.toRingHom).codRestrict
    (modularFunctionFieldFullC K N) (fun x => coeffMap_mem_fullC φ N x.2)

omit [NeZero N] in
@[scoped simp] theorem coe_fullCMap (x : modularFunctionFieldFullC k N) :
    ((fullCMap φ N x : modularFunctionFieldFullC K N) : LaurentSeries K) = coeffMap φ x := rfl

include φ in

theorem genusFF_fullC_eq_of_ringHom [IsAlgClosed k] [IsAlgClosed K] (hN : (N : K) ≠ 0) :
    genusFF K (modularFunctionFieldFullC K N) = genusFF k (modularFunctionFieldFullC k N) := by
  have hNk : (N : k) ≠ 0 := by
    intro h
    apply hN
    have := congrArg φ h
    rwa [map_natCast, map_zero] at this
  letI : Algebra k K := φ.toAlgebra
  letI : Algebra (modularFunctionFieldFullC k N) (modularFunctionFieldFullC K N) :=
    (fullCMap φ N).toAlgebra
  letI : Algebra k (modularFunctionFieldFullC K N) :=
    ((algebraMap K (modularFunctionFieldFullC K N)).comp φ).toAlgebra
  haveI : IsScalarTower k K (modularFunctionFieldFullC K N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k (modularFunctionFieldFullC k N) (modularFunctionFieldFullC K N) := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    apply Subtype.ext
    show algebraMap K (LaurentSeries K) (φ c) = coeffMap φ (algebraMap k (LaurentSeries k) c)
    rw [coeffMap_algebraMap_const]
  haveI := ModularCurve.isCurveOver_modularFunctionFieldFullC k N
  haveI := ModularCurve.isCurveOver_modularFunctionFieldFullC K N
  refine AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed
    k (modularFunctionFieldFullC k N) K (modularFunctionFieldFullC K N)
    ⟨JJ k N, transcendental_JJ k N, finiteDimensional_adjoin_JJ k N hNk⟩
    ⟨JJ K N, transcendental_JJ K N, finiteDimensional_adjoin_JJ K N hN⟩ ?_

  rw [eq_top_iff]
  intro x _
  have hle : modularFunctionFieldFullC K N ≤
      (IntermediateField.adjoin K (Set.range (algebraMap (modularFunctionFieldFullC k N)
        (modularFunctionFieldFullC K N)))).map (modularFunctionFieldFullC K N).val := by
    change IntermediateField.adjoin K (divisorExpansionsC K N) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨d, hd, hdN, rfl⟩
    haveI := hd
    refine (IntermediateField.mem_map _).mpr
      ⟨⟨qExpand K d (jqModC K), jqModCd_mem_full K N hdN⟩, ?_, rfl⟩
    apply IntermediateField.subset_adjoin
    refine ⟨⟨qExpand k d (jqModC k), jqModCd_mem_full k N hdN⟩, ?_⟩
    apply Subtype.ext
    show coeffMap φ (qExpand k d (jqModC k)) = qExpand K d (jqModC K)
    rw [ModularCurve.coeffMap_qExpand, coeffMap_jqModC]
  obtain ⟨y, hy, hyx⟩ := (IntermediateField.mem_map _).mp (hle x.2)
  rwa [← Subtype.ext hyx]

end Glue
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe.DeuringLE"

theorem natCast_ne_zero_of_charP {K R : Type*} [Field K] [Field R] {ℓ : ℕ} [CharP K ℓ] [CharP R ℓ]
    {N : ℕ} (hN : (N : K) ≠ 0) : (N : R) ≠ 0 := fun h =>
  hN ((CharP.cast_eq_zero_iff K ℓ N).mpr ((CharP.cast_eq_zero_iff R ℓ N).mp h))

end W9SFiveLe
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.W9SFiveLe.DeuringLE"

open W9SFiveLe in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hℓ : 5 ≤ ℓ) :
    genusFF K (modularFunctionFieldFullC K N) =
      genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by
  have hℓN : ¬ ℓ ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K ℓ N).mpr h)

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨ℓ, Fact.out⟩
  haveI := ValuationSubring.isAlgClosed_residueField A
  haveI := charP_residueField A hA

  haveI : CharP (AlgebraicClosure (ZMod ℓ)) ℓ :=
    (Algebra.charP_iff (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)) ℓ).mp inferInstance
  letI : Algebra (ZMod ℓ) K := ZMod.algebra K ℓ
  letI : Algebra (ZMod ℓ) (IsLocalRing.ResidueField A) := ZMod.algebra _ ℓ
  let φ₂ : AlgebraicClosure (ZMod ℓ) →+* K :=
    (IsAlgClosed.lift (R := ZMod ℓ) (S := AlgebraicClosure (ZMod ℓ)) (M := K)).toRingHom
  let φ₁ : AlgebraicClosure (ZMod ℓ) →+* IsLocalRing.ResidueField A :=
    (IsAlgClosed.lift (R := ZMod ℓ) (S := AlgebraicClosure (ZMod ℓ))
      (M := IsLocalRing.ResidueField A)).toRingHom
  have hNA : (N : IsLocalRing.ResidueField A) ≠ 0 := natCast_ne_zero_of_charP (K := K) hN
  rw [genusFF_fullC_eq_of_ringHom φ₂ N hN, ← genusFF_fullC_eq_of_ringHom φ₁ N hNA]
  exact genusFF_fullC_residueField_eq N hℓ hℓN A hA

end
end S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le
end P2MW
export P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le (solution)
