-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9f763315-9c79-5164-ac2c-d1795ffc8074

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_SpecializationMap
import Theorems.Thm_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem
import Theorems.Thm_ModularCurve_algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure
import Theorems.Thm_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piFin_eq_coeffRed
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_piFin_range_localizes_of_jqModC_mem
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_ord_sub_pos_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_exists_numberField_presentation_of_neZero
import Definitions.Def_ModularCurve_FibreModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm"
p2m_attr_erase "simp" "Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.AlgebraicCurve IsLocalRing ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve"
p2m_open "ModularCurve.NodeLocalized P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.NodeLocalized ModularCurve.CharPModel"
p2m_open "ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"

noncomputable section

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.AlgebraicCurve.Place.ord_nonneg_of_mem_pn" "AlgebraicCurve.Place.ord_nonneg_of_mem_pn"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.AlgebraicCurve.Place.mem_of_ord_nonneg_pn" "AlgebraicCurve.Place.mem_of_ord_nonneg_pn"

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.AlgebraicCurve.Place.ord_algebraMap_pn" "AlgebraicCurve.Place.ord_algebraMap_pn"

private theorem _root_.AlgebraicCurve.Place.ne_zero_of_ord_pos_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  simp at h

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.AlgebraicCurve.Place.ne_zero_of_ord_pos_pn" "AlgebraicCurve.Place.ne_zero_of_ord_pos_pn"

private theorem _root_.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn {K F : Type*} [Field K]
    [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn" "AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn {K F : Type*} [Field K]
    [Field F] [Algebra K F] (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring) (c : K) :
    v.HasValue g c ↔ g = algebraMap K F c ∨ 0 < v.ord (g - algebraMap K F c) := by
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hg hcm
  have key : v.HasValue g c ↔
      IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hsub⟩ = 0 := by
    have hx : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring c := Subtype.ext (by simp)
    rw [hx, map_sub, sub_eq_zero, v.residue_algebraMap c]
    constructor
    · intro h; exact h.residue_eq
    · intro h; exact ⟨hg, h⟩
  rw [key, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne (g - algebraMap K F c) 0 with h0 | h0
  · have hg' : g = algebraMap K F c := sub_eq_zero.mp h0
    have hz : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) = 0 := Subtype.ext h0
    rw [hz]
    exact ⟨fun _ => Or.inl hg', fun _ => not_isUnit_zero⟩
  · rw [v.isUnit_iff_ord_eq_zero_pn hsub h0]
    have hnn := v.ord_nonneg_of_mem_pn hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn" "AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn"

private theorem _root_.AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {g : F} {c : K} (h : 0 < v.ord (g - algebraMap K F c)) :
    v.HasValue g c := by
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring :=
    v.mem_of_ord_nonneg_pn (v.ne_zero_of_ord_pos_pn h) h.le
  have hg : g ∈ v.toValuationSubring := by
    have h' := add_mem hsub (v.algebraMap_mem' c)
    rwa [sub_add_cancel] at h'
  exact (v.hasValue_iff_eq_or_ord_sub_pos_pn hg c).mpr (Or.inr h)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn" "AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn"
namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1 ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

omit [Fact (Nat.Prime q)] [CharP k q] in

theorem penA_hasValue_add {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {x y : F} {a b : K} (hx : w.HasValue x a) (hy : w.HasValue y b) : w.HasValue (x + y) (a + b) := by
  obtain ⟨hxm, hxr⟩ := hx
  obtain ⟨hym, hyr⟩ := hy
  refine ⟨add_mem hxm hym, ?_⟩
  have e : (⟨x + y, add_mem hxm hym⟩ : w.toValuationSubring) = ⟨x, hxm⟩ + ⟨y, hym⟩ := rfl
  rw [e, map_add, hxr, hyr, map_add]

theorem pnN_coe_algebraMap {L : Type*} [Field L] (E : IntermediateField L (LaurentSeries L))
    (x : L) : ((algebraMap L E x : E) : LaurentSeries L) = algebraMap L (LaurentSeries L) x := by
  rw [IsScalarTower.algebraMap_apply L E (LaurentSeries L) x]
  rfl

theorem penC_residue_surjective [IsAlgClosed k] (v : Place k (modularFunctionFieldC k N)) :
    Function.Surjective (algebraMap k v.ResidueField) := by
  have h1 : Module.finrank k v.ResidueField = 1 := place_deg_eq_one_of_isAlgClosed k N v
  intro x
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp h1 x
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

theorem penC_exists_j_value (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w = v) :
    ∃ a₀ : A, 0 < w.ord (CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a₀ : AlgebraicClosure ℚ)) := by
  by_contra hcon
  have hle : ∀ a : A, w.ord (CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ)) ≤ 0 :=
    fun a => not_lt.mp (fun h => hcon ⟨a, h⟩)
  have hpole := P.d0_j_pole w hle
  rw [hw] at hpole
  have hnn : (0 : ℤ) ≤ v.ord (jGeomGen k N) := v.ord_nonneg_of_mem_pn hv1
  exact absurd hnn (not_le.mpr hpole)

theorem penC_sub_mem_nonunits_of_hasValue {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : Place K F) {g : F} {c : K} (h : u.HasValue g c) :
    g - algebraMap K F c ∈ u.toValuationSubring.nonunits := by
  have hmem : g - algebraMap K F c ∈ u.toValuationSubring := sub_mem h.mem (u.algebraMap_mem' c)
  have hres : IsLocalRing.residue u.toValuationSubring ⟨g - algebraMap K F c, hmem⟩ = 0 := by
    have e : (⟨g - algebraMap K F c, hmem⟩ : u.toValuationSubring)
        = ⟨g, h.mem⟩ - algebraMap K u.toValuationSubring c := rfl
    rw [e, map_sub, h.residue_eq, u.residue_algebraMap, sub_self]
  exact ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.residue_eq_zero_iff _).mp hres)

theorem penC_hasValue_of_sub_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : Place K F) {g : F} {c : K} (h : g - algebraMap K F c ∈ u.toValuationSubring.nonunits) :
    u.HasValue g c := by
  by_cases hgc : g = algebraMap K F c
  · rw [hgc]
    exact u.hasValue_algebraMap c
  · have hne : g - algebraMap K F c ≠ 0 := sub_ne_zero.mpr hgc
    obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
    exact u.hasValue_of_ord_sub_pos_pn ((u.mem_maximalIdeal_iff_ord_pos hne hmem).mp hmax)

theorem penC_red_eq_zero_of_mem_maximalIdeal (hred : Function.Surjective red) {a : A}
    (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)
  rw [← RingHom.mem_ker, hker]
  exact ha

theorem penC_frob_mem_nonunits (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N}
    (hx : x ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring.nonunits) :
    frobeniusGeomLevel k N data hKr x ∈ u.toValuationSubring.nonunits := by
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨zero_mem _, Ideal.zero_mem _⟩
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
  have hord : 0 < (frobOnPlacesGeomLevel k N data hKr u).ord x :=
    ((frobOnPlacesGeomLevel k N data hKr u).mem_maximalIdeal_iff_ord_pos hx0 hmem).mp hmax

  have hinv : x⁻¹ ∉ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := by
    intro hmem'
    have h1 := (frobOnPlacesGeomLevel k N data hKr u).ord_nonneg_of_mem_pn hmem'
    rw [Place.ord_inv] at h1
    omega
  rw [mem_frobOnPlacesGeomLevel_iff, map_inv₀] at hinv

  have hFx0 : frobeniusGeomLevel k N data hKr x ≠ 0 := by
    intro h0
    apply hinv
    rw [h0, inv_zero]
    exact zero_mem _
  have hFmem : frobeniusGeomLevel k N data hKr x ∈ u.toValuationSubring :=
    (u.toValuationSubring.mem_or_inv_mem _).resolve_right hinv
  have hFord : 0 < u.ord (frobeniusGeomLevel k N data hKr x) := by
    by_contra hle
    apply hinv
    apply u.mem_of_ord_nonneg_pn (inv_ne_zero hFx0)
    rw [Place.ord_inv]
    omega
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    ⟨hFmem, (u.mem_maximalIdeal_iff_ord_pos hFx0 hFmem).mpr hFord⟩

theorem penC_isAffine_of_isAffine_frob (u : Place k (modularFunctionFieldC k N))
    (h : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr u)) : IsAffineGeomPlace k N u := by
  obtain ⟨hj, hjN⟩ := h
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  refine ⟨?_, ?_⟩
  · have h1 : jGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := hj
    rw [mem_frobOnPlacesGeomLevel_iff] at h1
    have h2 : frobeniusGeomLevel k N data hKr (jGeomGen k N) = jGeomGen k N ^ q := frobeniusGeomLevel_jq k N data hKr
    rw [h2] at h1
    exact u.toValuationSubring.mem_of_pow_mem' hq h1
  · have h1 : jNGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := hjN
    rw [mem_frobOnPlacesGeomLevel_iff] at h1
    have h2 : frobeniusGeomLevel k N data hKr (jNGeomGen k N) = jNGeomGen k N ^ q := frobeniusGeomLevel_jqN k N data hKr
    rw [h2] at h1
    exact u.toValuationSubring.mem_of_pow_mem' hq h1

theorem penC_isAffine_frob_of_isAffine (u : Place k (modularFunctionFieldC k N))
    (h : IsAffineGeomPlace k N u) : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr u) := by
  obtain ⟨hj, hjN⟩ := h
  refine ⟨?_, ?_⟩
  · show jGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring
    rw [mem_frobOnPlacesGeomLevel_iff]
    have h2 : frobeniusGeomLevel k N data hKr (jGeomGen k N) = jGeomGen k N ^ q := frobeniusGeomLevel_jq k N data hKr
    rw [h2]
    exact pow_mem hj q
  · show jNGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring
    rw [mem_frobOnPlacesGeomLevel_iff]
    have h2 : frobeniusGeomLevel k N data hKr (jNGeomGen k N) = jNGeomGen k N ^ q := frobeniusGeomLevel_jqN k N data hKr
    rw [h2]
    exact pow_mem hjN q

theorem penC_reduceSnd_affine (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    IsAffineGeomPlace k N (P.reduceSnd W) := by
  rcases P.d1 W with h | h
  · have h₁ : P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) := h
    rw [hW] at h₁
    refine penC_isAffine_of_isAffine_frob (data := data) (hKr := hKr) _ ?_
    rw [← h₁]
    exact hvaff
  · have h₁ : frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W := h
    rw [hW] at h₁
    rw [← h₁]
    exact penC_isAffine_frob_of_isAffine v hvaff

omit [Fact q.Prime] [NeZero N] in

theorem penC_ramificationIndexAlong_pos' (φ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      →ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))
    (hφ : φ.toRingHom.IsIntegral) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    0 < Place.ramificationIndexAlong φ W := by
  unfold Place.ramificationIndexAlong
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact W.ramificationIndex_pos (F := laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))

omit [Fact q.Prime] [NeZero N] in

theorem penC_hasValue_of_restrictAlong
    (φ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      →ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))
    (hφ : φ.toRingHom.IsIntegral) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {x : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)} {c : AlgebraicClosure ℚ}
    (h : (W.restrictAlong φ hφ).HasValue x c) : W.HasValue (φ x) c := by
  by_cases hxc : x = algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c
  · rw [hxc, φ.commutes]
    exact W.hasValue_algebraMap c
  · have hne : x - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c ≠ 0 :=
      sub_ne_zero.mpr hxc
    have hmem : x - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c
        ∈ (W.restrictAlong φ hφ).toValuationSubring :=
      sub_mem h.mem ((W.restrictAlong φ hφ).algebraMap_mem' c)
    have hmax : (⟨_, hmem⟩ : (W.restrictAlong φ hφ).toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      ValuationSubring.coe_mem_nonunits_iff.mp (penC_sub_mem_nonunits_of_hasValue _ h)
    have hord := ((W.restrictAlong φ hφ).mem_maximalIdeal_iff_ord_pos hne hmem).mp hmax
    apply W.hasValue_of_ord_sub_pos_pn
    rw [← φ.commutes, ← map_sub, W.ord_restrictAlong φ hφ]
    exact mul_pos (by exact_mod_cast penC_ramificationIndexAlong_pos' φ hφ W) hord

theorem penC_hasValue_frob_apply (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N} {t : k}
    (h : (frobOnPlacesGeomLevel k N data hKr u).HasValue x t) : u.HasValue (frobeniusGeomLevel k N data hKr x) t := by
  have h1 := penC_frob_mem_nonunits u (penC_sub_mem_nonunits_of_hasValue _ h)
  rw [map_sub, AlgHom.commutes] at h1
  exact penC_hasValue_of_sub_mem_nonunits u h1

noncomputable def packA_g (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : CharPReduction.integralCoeffs A.toSubring) : LaurentSeries A where
  coeff n := ⟨(x : LaurentSeries (AlgebraicClosure ℚ)).coeff n, x.2 n⟩
  isPWO_support' := (x : LaurentSeries (AlgebraicClosure ℚ)).isPWO_support.mono
    (fun _ hn h => hn (Subtype.ext h))

theorem coeffMap_subtype_packA_g (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : CharPReduction.integralCoeffs A.toSubring) :
    coeffMap A.subtype (packA_g A x) = (x : LaurentSeries (AlgebraicClosure ℚ)) := by
  ext n
  rfl

theorem coeffMap_residue_packA_g (A : ValuationSubring (AlgebraicClosure ℚ)) (red : A →+* k)
    (x : CharPReduction.integralCoeffs A.toSubring) :
    coeffMap red (packA_g A x) = CharPReduction.coeffRed A.toSubring red x := by
  ext n
  rw [coeffMap_coeff, CharPReduction.coeffRed_coeff]
  rfl

theorem penC_redBar_comp_residue : R.redBar.comp (IsLocalRing.residue A) = red :=
  RingHom.ext fun a => R.redBar_residue a

theorem penC_good_residue_of_coe_eq (g : modularFunctionFieldBar (N * q)) (y : LaurentSeries A)
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y) :
    ∃ h : g ∈ R.R₁.integers, ((R.residue₁ ⟨g, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) = coeffMap red y := by
  have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := hg ▸ g.2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap y hy
  have hgeq : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) = g := Subtype.ext hg.symm
  have key : ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers,
      ((R.residue₁ ⟨_, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) = coeffMap red y := by
    refine ⟨h, ?_⟩
    rw [R.residue₁_apply, R.ι_coe, hres, coeffMap_coeffMap, penC_redBar_comp_residue]
  exact hgeq ▸ key

theorem penC_bfin_coe_mem_integralCoeffs (fm : FibreModel N A q k red) (b : fm.BFin) :
    ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.integralCoeffs A.toSubring :=
  mem_integralCoeffs_of_integral_affineBaseFin A N _ (fm.integralFin b)

theorem penC_residue_alpha (fm : FibreModel N A q k red) (b : fm.BFin) :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = fm.piFin b := by
  have hint := penC_bfin_coe_mem_integralCoeffs fm b
  have hcoe : ((heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (packA_g A ⟨_, hint⟩) := by
    rw [coe_heckeAlphaBar, coeffMap_subtype_packA_g]
  obtain ⟨h, hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext (hres.trans ?_)⟩
  rw [coeffMap_residue_packA_g, FibreModel.coe_piFin_eq_coeffRed N A q k red fm b hint]

theorem penC_residue_beta (fm : FibreModel N A q k red) (b : fm.BFin) :
    ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = frobeniusGeomLevel k N data hKr (fm.piFin b) := by
  have hint := penC_bfin_coe_mem_integralCoeffs fm b
  have hcoe : ((heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
        = coeffMap A.subtype (qExpand A q (packA_g A ⟨_, hint⟩)) := by
    rw [coe_heckeBetaBar, coeffMap_qExpand, coeffMap_subtype_packA_g]
  obtain ⟨h, hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext (hres.trans ?_)⟩
  rw [coeffMap_qExpand, coeffMap_residue_packA_g, frobeniusGeomLevel_apply_coe,
    FibreModel.coe_piFin_eq_coeffRed N A q k red fm b hint]

theorem penC_residue_const (a : A) :
    ∃ h : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = algebraMap k (modularFunctionFieldC k N) (red a) := by
  have hcoe : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (HahnSeries.single 0 a) := by
    rw [pnN_coe_algebraMap, algebraMap_laurentSeries_eq_single, coeffMap_single]
    rfl
  obtain ⟨h, hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext ?_⟩
  rw [hres, coeffMap_single, pnN_coe_algebraMap, algebraMap_laurentSeries_eq_single]

theorem penC_bfin_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring) (b : fm.BFin)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w = v) :
    ∃ a : A, w.HasValue (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ) ∧
      v.HasValue (fm.piFin b) (red a) := by
  obtain ⟨a₀, ha₀⟩ := penC_exists_j_value v hv1 _ hw

  have hreg : fm.piFin b ∈ v.toValuationSubring := (FibreModel.piFin_range_localizes_of_jqModC_mem N A q hqN k red fm v hv1).1 b
  obtain ⟨c, hc, -⟩ := v.exists_hasValue_of_surjective (penC_residue_surjective v) hreg
  obtain ⟨a₁, rfl⟩ := hred c

  set b₁ : fm.BFin := b - ⟨CharPModel.constantsHom N A a₁, fm.constFin_mem a₁⟩ with hb₁
  have hpi : (fm.piFin b₁ : modularFunctionFieldC k N)
      = fm.piFin b - algebraMap k (modularFunctionFieldC k N) (red a₁) := by
    rw [hb₁, map_sub, fm.piFin_const]
  have hnu : (fm.piFin b₁ : modularFunctionFieldC k N) ∈ v.toValuationSubring.nonunits := by
    rw [hpi]
    exact penC_sub_mem_nonunits_of_hasValue v hc
  have hsp : fm.spPlace hred dataAll hsep w = v := by
    rw [← hP]
    exact hw
  rw [← hsp] at hnu
  obtain ⟨a₂, ha₂m, ha₂⟩ := (fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep _ a₀ ha₀ b₁).mp hnu

  have hdiff : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
      = (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
            (a₂ : AlgebraicClosure ℚ) := by
    have hcoe : ((a₁ + a₂ : A) : AlgebraicClosure ℚ) = (a₁ : AlgebraicClosure ℚ) + a₂ := rfl
    have hb₁' : (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        = (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
              (a₁ : AlgebraicClosure ℚ) := by
      rw [hb₁]
      push_cast
      rfl
    rw [hcoe, hb₁', map_add, sub_sub]
  have ha₂' : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
        ∈ w.toValuationSubring.nonunits := by
    rw [hdiff]
    exact ha₂
  have hval_w : w.HasValue
      (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ((a₁ + a₂ : A) : AlgebraicClosure ℚ) :=
    penC_hasValue_of_sub_mem_nonunits _ ha₂'
  refine ⟨a₁ + a₂, hval_w, ?_⟩

  rw [map_add, penC_red_eq_zero_of_mem_maximalIdeal hred ha₂m, add_zero]
  exact hc

theorem penC_alpha_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v) (b : fm.BFin)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    ∃ a : A, W.HasValue (heckeAlphaBar (AlgebraicClosure ℚ) N q
        (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) (a : AlgebraicClosure ℚ) ∧
      v.HasValue (fm.piFin b) (red a) := by
  obtain ⟨a, haw, hav⟩ := penC_bfin_values fm hred dataAll hsep hP hqN v hvaff.1 b
    (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) hW
  exact ⟨a, penC_hasValue_of_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W haw, hav⟩

theorem penC_beta_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v) (b : fm.BFin)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    ∃ a : A, W.HasValue (heckeBetaBar (AlgebraicClosure ℚ) N q
        (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) (a : AlgebraicClosure ℚ) ∧
      (P.reduceSnd W).HasValue (fm.piFin b) (red a) := by
  obtain ⟨a, haw, hau⟩ := penC_bfin_values fm hred dataAll hsep hP hqN (P.reduceSnd W) (penC_reduceSnd_affine v hvaff W hW).1 b
    (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) rfl
  exact ⟨a, penC_hasValue_of_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ W haw, hau⟩

theorem atkinLehnerBar_heckeBetaBar_g (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar N) :
    ProlongationTuple.atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q t) =
      heckeAlphaBar (AlgebraicClosure ℚ) N q t := by
  have hex := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hσ := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q hex
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ hσ).2
  exact AlgHom.congr_fun hlegs t

theorem penC_beta_mem_snd (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (b : fm.BFin) :
    heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ R.R₂.integers := by
  obtain ⟨hαI, -⟩ := penC_residue_alpha R fm b
  rw [R.mem_integersSnd_iff, atkinLehnerBar_heckeBetaBar_g hqN]
  exact (R.mem_integersFst_iff _).mp hαI

theorem penC_residue₂_beta (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (b : fm.BFin)
    (h : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h⟩ = fm.piFin b := by
  obtain ⟨hαI, hαres⟩ := penC_residue_alpha R fm b
  have hAL := atkinLehnerBar_heckeBetaBar_g hqN (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
  have h2 : R.residue₂ ⟨_, h⟩ = R.residue₁ ⟨_, hαI⟩ := by
    show R.ι (R.R₂.residue ⟨_, h⟩) = R.ι (R.R₁.residue ⟨_, hαI⟩)
    rw [R.residue₂_eq]
    exact congrArg R.ι (congrArg R.R₁.residue (Subtype.ext hAL))
  rw [h2, hαres]

section FrobeniusOnPlaces

end FrobeniusOnPlaces

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring redRestrict fieldOver jRing jIntegralClosure exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict"
p2m_open "ModularCurve.NodeLocalized ModularCurve~jBar"

section Basics

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem c4_mem_coeffSubring_iff {x : AlgebraicClosure ℚ} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := by
  simp only [coeffSubring, Subring.mem_inf]
  exact Iff.rfl

theorem c4_algebraMap_mem_fieldOver (M : ℕ) [NeZero M] {x : AlgebraicClosure ℚ} (hx : x ∈ K) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) x ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

theorem c4_jqModC_mem_fieldOver (M : ℕ) [NeZero M] : jqModC (AlgebraicClosure ℚ) ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

theorem c4_jqNModC_mem_fieldOver (M : ℕ) [NeZero M] : jqNModC (AlgebraicClosure ℚ) M ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))

theorem c4_jqModC_mem_jRing : jqModC (AlgebraicClosure ℚ) ∈ jRing A K :=
  Subring.subset_closure (Or.inr rfl)

theorem c4_constSeries_mem_jRing (a : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) a ∈ jRing A K :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem c4_jRing_le_fieldOver (M : ℕ) [NeZero M] : jRing A K ≤ (fieldOver M K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact c4_algebraMap_mem_fieldOver K M ((c4_mem_coeffSubring_iff A K).mp a.2).2
  · exact c4_jqModC_mem_fieldOver K M

variable {A K} in
theorem c4_coeffSubring_mono {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') :
    coeffSubring A K ≤ coeffSubring A K' :=
  inf_le_inf_left _ (fun _ hx => h hx)

variable {A K} in
theorem c4_jRing_mono {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') : jRing A K ≤ jRing A K' := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact c4_constSeries_mem_jRing A K' ⟨a, c4_coeffSubring_mono h a.2⟩
  · exact c4_jqModC_mem_jRing A K'

variable {K} in
theorem c4_fieldOver_mono (M : ℕ) [NeZero M] {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') :
    fieldOver M K ≤ fieldOver M K' := by
  rw [fieldOver, Subfield.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · exact Subfield.subset_closure (Or.inl ⟨⟨a, h a.2⟩, rfl⟩)
  · exact Subfield.subset_closure (Or.inr hx)

end Basics

end ModularCurve.NodeLocalized

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1 ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section LevelM

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (M : ℕ) [NeZero M]

theorem c4_coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ n x)
      = qExpand (AlgebraicClosure ℚ) n (coeffEmb (AlgebraicClosure ℚ) x) := by
  ext m
  by_cases hm : (n : ℤ) ∣ m
  · obtain ⟨m, rfl⟩ := hm
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hm, qExpand_coeff_of_not_dvd n _ hm, map_zero]

theorem c4_coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  show (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)
  exact map_jqModC _

theorem c4_coe_jBar : ((CharPModel.jBar M : modularFunctionFieldBar M) : LaurentSeries (AlgebraicClosure ℚ))
    = jqModC (AlgebraicClosure ℚ) := c4_coeffEmb_jq

theorem c4_coe_jNBar : ((CharPModel.jNBar M : modularFunctionFieldBar M) : LaurentSeries (AlgebraicClosure ℚ))
    = jqNModC (AlgebraicClosure ℚ) M := by
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq) = qExpand (AlgebraicClosure ℚ) M (jqModC (AlgebraicClosure ℚ))
  rw [c4_coeffEmb_qExpand, c4_coeffEmb_jq]

theorem c4_jqModC_mem_bar : jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar M := by
  rw [← c4_coe_jBar M]; exact SetLike.coe_mem _

theorem c4_jqNModC_mem_bar : jqNModC (AlgebraicClosure ℚ) M ∈ modularFunctionFieldBar M := by
  rw [← c4_coe_jNBar M]; exact SetLike.coe_mem _

theorem c4_fieldOver_le_bar : (fieldOver M K : Set (LaurentSeries (AlgebraicClosure ℚ))) ⊆ modularFunctionFieldBar M := by
  intro x hx
  change x ∈ (modularFunctionFieldBar M).toSubfield
  refine (Subfield.closure_le.mpr ?_) hx
  rintro y (⟨a, rfl⟩ | rfl | rfl)
  · exact (modularFunctionFieldBar M).algebraMap_mem (a : AlgebraicClosure ℚ)
  · exact c4_jqModC_mem_bar M
  · exact c4_jqNModC_mem_bar M

variable {A K M} in
theorem c4_bar_mem_of_mem_C {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ jIntegralClosure M A K) :
    x ∈ modularFunctionFieldBar M := c4_fieldOver_le_bar K M hx.1

theorem c4_jRing_le_map_affineBaseFin :
    jRing A K ≤ (CharPModel.affineBaseFin M A).map (modularFunctionFieldBar M).val.toRingHom := by
  rw [jRing, Subring.closure_le]
  rintro y (⟨a, rfl⟩ | rfl)
  · exact ⟨CharPModel.constantsHom M A ⟨(a : AlgebraicClosure ℚ), ((c4_mem_coeffSubring_iff A K).mp a.2).1⟩,
      Subring.subset_closure (Or.inl ⟨_, rfl⟩), rfl⟩
  · exact ⟨CharPModel.jBar M, Subring.subset_closure (Or.inr rfl), c4_coe_jBar M⟩

variable {A K M} in
theorem c4_jRing_to_affineBaseFin {y : LaurentSeries (AlgebraicClosure ℚ)} (hy : y ∈ jRing A K)
    (hy' : y ∈ modularFunctionFieldBar M) :
    (⟨y, hy'⟩ : modularFunctionFieldBar M) ∈ CharPModel.affineBaseFin M A := by
  obtain ⟨z, hz, hzy⟩ := c4_jRing_le_map_affineBaseFin A K M hy
  have : (⟨y, hy'⟩ : modularFunctionFieldBar M) = z := Subtype.ext hzy.symm
  rw [this]
  exact hz

end LevelM

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1 ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section Normalisation

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

def c4_jRingToABF (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (M : ℕ) [NeZero M] : ↥(jRing A K) →+* ↥(CharPModel.affineBaseFin M A) where
  toFun y := ⟨⟨(y : LaurentSeries (AlgebraicClosure ℚ)),
      c4_fieldOver_le_bar K M (c4_jRing_le_fieldOver A K M y.2)⟩, c4_jRing_to_affineBaseFin y.2 _⟩
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)
  map_zero' := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)

theorem c4_exists_monic_affineBaseFin (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    ∃ p : Polynomial (CharPModel.affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (CharPModel.affineBaseFin (N * q) A).subtype t p = 0 := by
  obtain ⟨p, hp, hpt⟩ := ht.2
  refine ⟨p.map (c4_jRingToABF A K (N * q)), hp.map _, ?_⟩
  apply Subtype.val_injective
  rw [Polynomial.eval₂_map]
  have h := Polynomial.hom_eval₂ p (((CharPModel.affineBaseFin (N * q) A).subtype).comp (c4_jRingToABF A K (N * q)))
    (modularFunctionFieldBar (N * q)).val.toRingHom t
  refine h.trans ?_
  convert hpt using 1 <;> try rfl

theorem c4_coe_mem_integralCoeffs (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.integralCoeffs A.toSubring :=
  mem_integralCoeffs_of_integral_affineBaseFin A (N * q) t (c4_exists_monic_affineBaseFin K t ht)

theorem c4_mem_integersFst_and_coe_residue₁ (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    ∃ h : t ∈ R.R₁.integers, ((R.residue₁ ⟨t, h⟩ : modularFunctionFieldC k N) : LaurentSeries k)
      = coeffMap red (packA_g A ⟨_, c4_coe_mem_integralCoeffs K t ht⟩) :=
  penC_good_residue_of_coe_eq R t (packA_g A ⟨_, c4_coe_mem_integralCoeffs K t ht⟩)
    (coeffMap_subtype_packA_g A ⟨_, c4_coe_mem_integralCoeffs K t ht⟩).symm

theorem c4_mem_integersFst (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) : t ∈ R.R₁.integers :=
  (c4_mem_integersFst_and_coe_residue₁ R K t ht).1

end Normalisation

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1 ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section SecondSide

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem c4_jBar_eq_alpha_jBar :
    CharPModel.jBar (N * q) = heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) :=
  Subtype.ext (by rw [coe_heckeAlphaBar]; rfl)

theorem c4_atkinLehnerBar_jBar (hqN : ¬ q ∣ N) :
    ProlongationTuple.atkinLehnerBar N q (CharPModel.jBar (N * q))
      = heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) := by
  have hex := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hσ := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q hex
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ hσ).1
  rw [c4_jBar_eq_alpha_jBar]
  exact AlgHom.congr_fun hlegs (CharPModel.jBar N)

theorem c4_mem_integersSnd (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) : t ∈ R.R₂.integers :=
  (ModularCurve.PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure R hqN K t ht).2.1.fst

theorem c4_isIntegral_adjoin_residue₁_of_mem_C (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) (h₁ : t ∈ R.R₁.integers) :
    IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N))) (R.residue₁ ⟨t, h₁⟩ : modularFunctionFieldC k N) := by
  obtain ⟨h, hi⟩ := (ModularCurve.PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure R hqN K t ht).1
  exact hi

theorem c4_isIntegral_adjoin_residue₂_of_mem_C (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) (h₂ : t ∈ R.R₂.integers) :
    IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N))) (R.residue₂ ⟨t, h₂⟩ : modularFunctionFieldC k N) := by
  obtain ⟨h, hi⟩ := (ModularCurve.PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure R hqN K t ht).2.1
  exact hi

end SecondSide

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1 ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section ResidueRegular

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem c4_exists_monic_of_mem_affineBaseFin {s : modularFunctionFieldBar (N * q)}
    (hs : s ∈ CharPModel.affineBaseFin (N * q) A) :
    ∃ p : Polynomial (CharPModel.affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (CharPModel.affineBaseFin (N * q) A).subtype s p = 0 :=
  ⟨Polynomial.X - Polynomial.C ⟨s, hs⟩, Polynomial.monic_X_sub_C _,
    by rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, Subring.coe_subtype, sub_self]⟩

theorem c4_mem_integersFst_of_exists_monic {t : modularFunctionFieldBar (N * q)}
    (ht : ∃ p : Polynomial (CharPModel.affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (CharPModel.affineBaseFin (N * q) A).subtype t p = 0) : t ∈ R.R₁.integers := by
  have hco := mem_integralCoeffs_of_integral_affineBaseFin A (N * q) t ht
  exact (penC_good_residue_of_coe_eq R t (packA_g A ⟨_, hco⟩) (coeffMap_subtype_packA_g A ⟨_, hco⟩).symm).1

theorem c4_mem_integersFst_of_mem_affineBaseFin {s : modularFunctionFieldBar (N * q)}
    (hs : s ∈ CharPModel.affineBaseFin (N * q) A) : s ∈ R.R₁.integers :=
  c4_mem_integersFst_of_exists_monic R (c4_exists_monic_of_mem_affineBaseFin hs)

theorem c4_residue₁_jBar (h : (CharPModel.jBar (N * q) : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers) :
    R.residue₁ ⟨CharPModel.jBar (N * q), h⟩ = jGeomGen k N := by
  have hcoe : ((CharPModel.jBar (N * q) : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap A.subtype (jqModC A) := by
    rw [c4_coe_jBar]
    exact (map_jqModC _).symm
  obtain ⟨h', hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  apply Subtype.ext
  rw [show (⟨CharPModel.jBar (N * q), h⟩ : ↥R.R₁.integers) = ⟨_, h'⟩ from rfl, hres]
  exact map_jqModC _

theorem c4_residue₁_const (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h⟩ = algebraMap k (modularFunctionFieldC k N) (red a) := by
  obtain ⟨h', hres⟩ := penC_residue_const R a
  exact hres

theorem c4_residue₁_constantsHom (a : A) (h : CharPModel.constantsHom (N * q) A a ∈ R.R₁.integers) :
    R.residue₁ ⟨CharPModel.constantsHom (N * q) A a, h⟩ = algebraMap k (modularFunctionFieldC k N) (red a) :=
  c4_residue₁_const R a h

end ResidueRegular

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1 ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section Values

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

variable (P) in

theorem c4_exists_ord_jBar_sub_pos (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = v) :
    ∃ a₀ : A, 0 < V.ord (CharPModel.jBar (N * q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a₀ : AlgebraicClosure ℚ)) := by
  obtain ⟨a₀, ha₀⟩ := penC_exists_j_value (P := P) v hv (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) hV
  refine ⟨a₀, ?_⟩
  rw [c4_jBar_eq_alpha_jBar, ← (heckeAlphaBar (AlgebraicClosure ℚ) N q).commutes (a₀ : AlgebraicClosure ℚ), ← map_sub,
    V.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα]
  exact mul_pos (by exact_mod_cast penC_ramificationIndexAlong_pos' (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V) ha₀

variable (P) in

theorem c4_exists_hasValue_of_exists_monic {t : modularFunctionFieldBar (N * q)}
    (ht : ∃ p : Polynomial (CharPModel.affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (CharPModel.affineBaseFin (N * q) A).subtype t p = 0)
    (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = v) :
    ∃ a : A, V.HasValue t (a : AlgebraicClosure ℚ) := by
  obtain ⟨a₀, ha₀⟩ := c4_exists_ord_jBar_sub_pos P v hv V hV
  obtain ⟨a, ha⟩ := ModularCurve.exists_ord_sub_pos_of_integral_affineBaseFin A (N * q) V t ht a₀ ha₀
  exact ⟨a, penC_hasValue_of_sub_mem_nonunits V ha⟩

theorem c4_mem_nodeIntegersOver (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (hw : jGeomGen k N ∈ w.toValuationSubring)
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    t ∈ R.nodeIntegersOver K w := by
  refine ⟨⟨c4_mem_integersFst R K t ht, c4_mem_integersSnd R hqN K t ht, fun V hV => ?_⟩, ht.1⟩
  obtain ⟨a, ha⟩ := c4_exists_hasValue_of_exists_monic P (c4_exists_monic_affineBaseFin K t ht) w hw V hV
  exact ha.mem

end Values

end ModularCurve.PlaceSpecialization

end

section

open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField Polynomial

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv algebraAlong isScalarTower_along isIntegral_along Place.ramificationIndexAlong Place.ord_nonneg_of_mem_pn Place.mem_of_ord_nonneg_pn Place.ord_algebraMap_pn Place.ne_zero_of_ord_pos_pn Place.isUnit_iff_ord_eq_zero_pn Place.hasValue_iff_eq_or_ord_sub_pos_pn Place.hasValue_of_ord_sub_pos_pn"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {j : F}

theorem integralClosure_adjoin_le_valuationSubring (O : ValuationSubring F)
    (hK : ∀ c : K, algebraMap K F c ∈ O) (hjO : j ∈ O)
    (r : integralClosure (Algebra.adjoin K ({j} : Set F)) F) : (r : F) ∈ O := by
  let O' : Subalgebra K F :=
    { O.toSubring with
      algebraMap_mem' := hK }
  have hle : Algebra.adjoin K ({j} : Set F) ≤ O' :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjO)
  let φ : Algebra.adjoin K ({j} : Set F) →+* O :=
    (Subalgebra.val _).toRingHom.codRestrict O.toSubring (fun y => hle y.2)
  obtain ⟨p, hp, hpr⟩ : IsIntegral (Algebra.adjoin K ({j} : Set F)) (r : F) := r.2
  have hint : IsIntegral O (r : F) := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [eval₂_map]
    exact hpr
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

theorem algebraMap_mem_integralClosure_adjoin (c : K) :
    algebraMap K F c ∈ integralClosure (Algebra.adjoin K ({j} : Set F)) F := by
  rw [mem_integralClosure_iff, IsScalarTower.algebraMap_apply K (Algebra.adjoin K ({j} : Set F)) F]
  exact isIntegral_algebraMap

end AlgebraicCurve

end

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1 ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

theorem c4_eq_comap_of_span {C D : Type*} [CommRing C] [CommRing D] [Algebra C D] [Algebra.IsIntegral C D]
    (𝔫 : Ideal C) [𝔫.IsPrime] (hker : RingHom.ker (algebraMap C D) ≤ 𝔫)
    (M : Ideal D) [hM : M.IsMaximal] (S : Set D) (hS : M = Ideal.span S)
    (hgen : ∀ s ∈ S, ∃ c ∈ 𝔫, algebraMap C D c = s) : 𝔫 = M.comap (algebraMap C D) := by
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔫 (⊥ : Ideal D)
    (by rw [← RingHom.ker_eq_comap_bot]; exact hker)
  have hMQ : M ≤ Q := by
    rw [hS, Ideal.span_le]
    intro s hs
    obtain ⟨c, hc, rfl⟩ := hgen s hs
    have : c ∈ Q.comap (algebraMap C D) := hQc.symm ▸ hc
    exact this
  have hQM : M = Q := hM.eq_of_le hQ.ne_top hMQ
  rw [hQM, hQc]

section ChartRing

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q]

def c4D (k : Type*) [Field k] (N : ℕ) [NeZero N] : Subring (modularFunctionFieldC k N) :=
  (integralClosure (Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N))) (modularFunctionFieldC k N)).toSubring

omit [Fact q.Prime] [CharP k q] in
theorem c4_mem_c4D_iff {x : modularFunctionFieldC k N} :
    x ∈ c4D k N ↔ IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N))) x :=
  mem_integralClosure_iff _ _

theorem c4_isDedekindDomain_c4D (dataN : ModularPolynomialData N)
    (hsep : ((dataN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) : IsDedekindDomain ↥(c4D k N) := by
  exact (ModularCurve.isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable k N dataN hsep).2.2.1

theorem c4_isNoetherianRing_c4D (dataN : ModularPolynomialData N)
    (hsep : ((dataN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) : IsNoetherianRing ↥(c4D k N) := by
  haveI hD := c4_isDedekindDomain_c4D dataN hsep
  exact hD.toIsDedekindRing.toIsNoetherian

omit [Fact q.Prime] [CharP k q] in

theorem c4_c4D_le_place (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring)
    (r : ↥(c4D k N)) : (r : modularFunctionFieldC k N) ∈ v.toValuationSubring :=
  integralClosure_adjoin_le_valuationSubring v.toValuationSubring v.algebraMap_mem' hv ⟨r, r.2⟩

omit [Fact q.Prime] [CharP k q] in
theorem c4_algebraMap_mem_c4D (c : k) : algebraMap k (modularFunctionFieldC k N) c ∈ c4D k N :=
  algebraMap_mem_integralClosure_adjoin c

def c4_DtoPlace (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring) :
    ↥(c4D k N) →+* ↥v.toValuationSubring where
  toFun r := ⟨r, c4_c4D_le_place v hv r⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

def c4_evalD (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring) :
    ↥(c4D k N) →+* v.ResidueField :=
  (IsLocalRing.residue ↥v.toValuationSubring).comp (c4_DtoPlace v hv)

def c4_M (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring) : Ideal ↥(c4D k N) :=
  RingHom.ker (c4_evalD v hv)

omit [Fact q.Prime] [CharP k q] in
theorem c4_mem_M_iff (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring) (r : ↥(c4D k N)) :
    r ∈ c4_M v hv ↔ v.HasValue (r : modularFunctionFieldC k N) (0 : k) := by
  rw [c4_M, RingHom.mem_ker]
  constructor
  · intro h
    exact ⟨c4_c4D_le_place v hv r, by rw [map_zero]; exact h⟩
  · rintro ⟨h1, h2⟩
    rw [map_zero] at h2
    exact h2

omit [Fact q.Prime] [CharP k q] in
theorem c4_evalD_surjective (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring)
    (hrat : v.IsRational) : Function.Surjective (c4_evalD v hv) := by
  intro x
  obtain ⟨c, rfl⟩ := hrat x
  refine ⟨(⟨algebraMap k (modularFunctionFieldC k N) c, c4_algebraMap_mem_c4D c⟩ : ↥(c4D k N)), ?_⟩
  exact v.residue_algebraMap c

omit [Fact q.Prime] [CharP k q] in
theorem c4_isMaximal_M (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring)
    (hrat : v.IsRational) : (c4_M v hv).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (c4_evalD_surjective v hv hrat)

theorem c4_exists_finset_span_eq_M (dataN : ModularPolynomialData N)
    (hsep : ((dataN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring) :
    ∃ S : Finset ↥(c4D k N), Ideal.span (S : Set ↥(c4D k N)) = c4_M v hv := by
  haveI := c4_isNoetherianRing_c4D (k := k) dataN hsep
  exact IsNoetherian.noetherian (c4_M v hv)

end ChartRing

end ModularCurve.PlaceSpecialization

end

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1 ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section ModelElements

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem c4_exists_fd_forall_degeneracies_mem (fm : FibreModel N A q k red) (b : fm.BFin) :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K₀),
      ∀ K'' : IntermediateField ℚ (AlgebraicClosure ℚ), K₀ ≤ K'' →
        ((heckeAlphaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N) : modularFunctionFieldBar (N * q)) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' ∧
        ((heckeBetaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N) : modularFunctionFieldBar (N * q)) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' := by
  exact ModularCurve.CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem fm b

theorem c4_exists_piFin_eq (fm : FibreModel N A q k red) (hred : Function.Surjective red) (r : ↥(c4D k N)) :
    ∃ b : fm.BFin, fm.piFin b = (r : modularFunctionFieldC k N) := by

  let Rg : Subalgebra k (modularFunctionFieldC k N) :=
    { fm.piFin.range with
      algebraMap_mem' := fun c => by
        obtain ⟨a, rfl⟩ := hred c
        exact ⟨⟨constantsHom N A a, fm.constFin_mem a⟩, fm.piFin_const a⟩ }
  have hle : Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N)) ≤ Rg := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨⟨jBar N, fm.jBar_mem⟩, fm.piFin_j⟩
  let ψ : ↥(Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N))) →+* ↥fm.piFin.range :=
    (Subalgebra.val _).toRingHom.codRestrict fm.piFin.range (fun y => hle y.2)
  obtain ⟨p, hp, hpr⟩ : IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N))) (r : modularFunctionFieldC k N) := r.2
  obtain ⟨b, hb⟩ := fm.intClosed_piFin r ⟨p.map ψ, hp.map ψ, by rw [Polynomial.eval₂_map]; exact hpr⟩
  exact ⟨b, hb⟩

end ModelElements

section SecondReduction

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

variable (P) in

theorem c4_reduceSnd_eq_arithFrobC_smul [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    P.reduceSnd V = arithFrobC q k N • w := by
  have hfix := ModularCurve.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
    k N hqN data hKr w hw
  rw [arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr]
  rcases P.d1 V with h | h
  · have h' : P.reduceFst V = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V) := h
    rw [hV] at h'
    apply frobOnPlacesGeomLevel_injective k N data hKr
    rw [hfix]
    exact h'.symm
  · have h' : frobOnPlacesGeomLevel k N data hKr (P.reduceFst V) = P.reduceSnd V := h
    rw [hV] at h'
    exact h'.symm

end SecondReduction

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1 ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section Evaluation

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N))
  (hw : jGeomGen k N ∈ w.toValuationSubring)
  (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w)

def c4_toBar (t : ↥(jIntegralClosure (N * q) A K)) : modularFunctionFieldBar (N * q) :=
  ⟨(t : LaurentSeries (AlgebraicClosure ℚ)), c4_bar_mem_of_mem_C t.2⟩

@[scoped simp] theorem c4_coe_toBar (t : ↥(jIntegralClosure (N * q) A K)) :
    ((c4_toBar K t : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) = t := rfl

theorem c4_toBar_mem (t : ↥(jIntegralClosure (N * q) A K)) :
    ((c4_toBar K t : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K := t.2

include hw hV in
variable (P) in
theorem c4_exists_value (t : ↥(jIntegralClosure (N * q) A K)) : ∃ a : A, V.HasValue (c4_toBar K t) (a : AlgebraicClosure ℚ) :=
  c4_exists_hasValue_of_exists_monic P (c4_exists_monic_affineBaseFin K (c4_toBar K t) t.2) w hw V hV

variable (P) in

def c4_value (t : ↥(jIntegralClosure (N * q) A K)) : A := Classical.choose (c4_exists_value P K w hw V hV t)

variable (P) in
theorem c4_hasValue_value (t : ↥(jIntegralClosure (N * q) A K)) :
    V.HasValue (c4_toBar K t) ((c4_value P K w hw V hV t : A) : AlgebraicClosure ℚ) :=
  Classical.choose_spec (c4_exists_value P K w hw V hV t)

variable (P) in
theorem c4_value_eq_of_hasValue (t : ↥(jIntegralClosure (N * q) A K)) (a : A)
    (ha : V.HasValue (c4_toBar K t) (a : AlgebraicClosure ℚ)) : c4_value P K w hw V hV t = a :=
  Subtype.ext ((c4_hasValue_value P K w hw V hV t).unique ha)

variable (P) in

def c4_evalV : ↥(jIntegralClosure (N * q) A K) →+* k where
  toFun t := red (c4_value P K w hw V hV t)
  map_one' := by
    rw [c4_value_eq_of_hasValue P K w hw V hV 1 1 (by
      rw [OneMemClass.coe_one, show (c4_toBar K (1 : ↥(jIntegralClosure (N * q) A K)) : modularFunctionFieldBar (N * q)) = 1
        from Subtype.ext rfl, ← map_one (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))]
      exact V.hasValue_algebraMap 1), map_one]
  map_mul' s t := by
    rw [← map_mul]
    congr 1
    apply c4_value_eq_of_hasValue
    rw [MulMemClass.coe_mul, show (c4_toBar K (s * t) : modularFunctionFieldBar (N * q)) = c4_toBar K s * c4_toBar K t
      from Subtype.ext rfl]
    exact (c4_hasValue_value P K w hw V hV s).mul (c4_hasValue_value P K w hw V hV t)
  map_zero' := by
    rw [c4_value_eq_of_hasValue P K w hw V hV 0 0 (by
      rw [ZeroMemClass.coe_zero, show (c4_toBar K (0 : ↥(jIntegralClosure (N * q) A K)) : modularFunctionFieldBar (N * q)) = 0
        from Subtype.ext rfl, ← map_zero (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))]
      exact V.hasValue_algebraMap 0), map_zero]
  map_add' s t := by
    rw [← map_add]
    congr 1
    apply c4_value_eq_of_hasValue
    rw [AddMemClass.coe_add, show (c4_toBar K (s + t) : modularFunctionFieldBar (N * q)) = c4_toBar K s + c4_toBar K t
      from Subtype.ext rfl]
    exact penA_hasValue_add V (c4_hasValue_value P K w hw V hV s) (c4_hasValue_value P K w hw V hV t)

variable (P) in
theorem c4_evalV_apply (t : ↥(jIntegralClosure (N * q) A K)) : c4_evalV P K w hw V hV t = red (c4_value P K w hw V hV t) := rfl

variable (P) in

def c4_nV : Ideal ↥(jIntegralClosure (N * q) A K) := RingHom.ker (c4_evalV P K w hw V hV)

variable (P) in
theorem c4_isPrime_nV : (c4_nV P K w hw V hV).IsPrime := RingHom.ker_isPrime _

variable (P) in

theorem c4_mem_nV_iff (hred : Function.Surjective red) (t : ↥(jIntegralClosure (N * q) A K)) (a : A)
    (ha : V.HasValue (c4_toBar K t) (a : AlgebraicClosure ℚ)) :
    t ∈ c4_nV P K w hw V hV ↔ a ∈ IsLocalRing.maximalIdeal A := by
  rw [c4_nV, RingHom.mem_ker, c4_evalV_apply, c4_value_eq_of_hasValue P K w hw V hV t a ha]
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)
  rw [← RingHom.mem_ker, hker]

end Evaluation

end ModularCurve.PlaceSpecialization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1 ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section ResidueHoms

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem c4_jRing_le_C {y : LaurentSeries (AlgebraicClosure ℚ)} (hy : y ∈ jRing A K) : y ∈ jIntegralClosure (N * q) A K :=
  ⟨c4_jRing_le_fieldOver A K (N * q) hy, isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨y, hy⟩)⟩

def c4_cst (a : ↥(coeffSubring A K)) : ↥(jIntegralClosure (N * q) A K) :=
  ⟨CharPReduction.constSeries (coeffSubring A K) a, c4_jRing_le_C K (c4_constSeries_mem_jRing A K a)⟩

theorem c4_toBar_cst (a : ↥(coeffSubring A K)) :
    c4_toBar K (c4_cst K a) = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) :=
  Subtype.ext rfl

def c4_jC : ↥(jIntegralClosure (N * q) A K) :=
  ⟨jqModC (AlgebraicClosure ℚ), c4_jRing_le_C K (c4_jqModC_mem_jRing A K)⟩

theorem c4_toBar_jC : c4_toBar K (c4_jC K : ↥(jIntegralClosure (N * q) A K)) = CharPModel.jBar (N * q) :=
  Subtype.ext (c4_coe_jBar (N * q)).symm

def c4_res₁C : ↥(jIntegralClosure (N * q) A K) →+* modularFunctionFieldC k N where
  toFun t := R.residue₁ ⟨c4_toBar K t, c4_mem_integersFst R K _ t.2⟩
  map_one' := by
    rw [show (⟨c4_toBar K (1 : ↥(jIntegralClosure (N * q) A K)), c4_mem_integersFst R K _
      (1 : ↥(jIntegralClosure (N * q) A K)).2⟩ : ↥R.R₁.integers) = 1 from Subtype.ext rfl, map_one]
  map_mul' s t := by
    rw [show (⟨c4_toBar K (s * t), c4_mem_integersFst R K _ (s * t).2⟩ : ↥R.R₁.integers)
      = ⟨c4_toBar K s, c4_mem_integersFst R K _ s.2⟩ * ⟨c4_toBar K t, c4_mem_integersFst R K _ t.2⟩ from Subtype.ext rfl, map_mul]
  map_zero' := by
    rw [show (⟨c4_toBar K (0 : ↥(jIntegralClosure (N * q) A K)), c4_mem_integersFst R K _
      (0 : ↥(jIntegralClosure (N * q) A K)).2⟩ : ↥R.R₁.integers) = 0 from Subtype.ext rfl, map_zero]
  map_add' s t := by
    rw [show (⟨c4_toBar K (s + t), c4_mem_integersFst R K _ (s + t).2⟩ : ↥R.R₁.integers)
      = ⟨c4_toBar K s, c4_mem_integersFst R K _ s.2⟩ + ⟨c4_toBar K t, c4_mem_integersFst R K _ t.2⟩ from Subtype.ext rfl, map_add]

theorem c4_res₁C_apply (t : ↥(jIntegralClosure (N * q) A K)) :
    c4_res₁C R K t = R.residue₁ ⟨c4_toBar K t, c4_mem_integersFst R K _ t.2⟩ := rfl

theorem c4_res₁C_mem_c4D (hqN : ¬ q ∣ N) (t : ↥(jIntegralClosure (N * q) A K)) : c4_res₁C R K t ∈ c4D k N :=
  (c4_mem_c4D_iff).mpr (c4_isIntegral_adjoin_residue₁_of_mem_C R hqN K _ t.2 _)

def c4_g₁ (hqN : ¬ q ∣ N) : ↥(jIntegralClosure (N * q) A K) →+* ↥(c4D k N) := (c4_res₁C R K).codRestrict (c4D k N) (c4_res₁C_mem_c4D R K hqN)

theorem c4_coe_g₁ (hqN : ¬ q ∣ N) (t : ↥(jIntegralClosure (N * q) A K)) :
    ((c4_g₁ R K hqN t : ↥(c4D k N)) : modularFunctionFieldC k N) = R.residue₁ ⟨c4_toBar K t, c4_mem_integersFst R K _ t.2⟩ := rfl

theorem c4_coe_g₁_cst (hqN : ¬ q ∣ N) (a : ↥(coeffSubring A K)) :
    ((c4_g₁ R K hqN (c4_cst K a) : ↥(c4D k N)) : modularFunctionFieldC k N)
      = algebraMap k (modularFunctionFieldC k N) (redRestrict red K a) := by
  rw [c4_coe_g₁ R K hqN]
  exact c4_residue₁_const R ⟨(a : AlgebraicClosure ℚ), a.2.1⟩ _

theorem c4_coe_g₁_jC (hqN : ¬ q ∣ N) : ((c4_g₁ R K hqN (c4_jC K) : ↥(c4D k N)) : modularFunctionFieldC k N) = jGeomGen k N := by
  rw [c4_coe_g₁ R K hqN]
  have h := c4_toBar_jC (A := A) (q := q) (N := N) K
  rw [show (⟨c4_toBar K (c4_jC K : ↥(jIntegralClosure (N * q) A K)), c4_mem_integersFst R K _ (c4_jC K).2⟩ : ↥R.R₁.integers)
    = ⟨CharPModel.jBar (N * q), c4_mem_integersFst_of_mem_affineBaseFin R (Subring.subset_closure (Or.inr rfl))⟩
    from Subtype.ext h]
  exact c4_residue₁_jBar R _

theorem c4_residue₂_eq_residue₁_atkinLehnerBar (t : modularFunctionFieldBar (N * q)) (h₂ : t ∈ R.R₂.integers)
    (h₁ : ProlongationTuple.atkinLehnerBar N q t ∈ R.R₁.integers) :
    R.residue₂ ⟨t, h₂⟩ = R.residue₁ ⟨ProlongationTuple.atkinLehnerBar N q t, h₁⟩ := by
  show R.ι (R.R₂.residue ⟨t, h₂⟩) = R.ι (R.R₁.residue ⟨_, h₁⟩)
  rw [R.residue₂_eq]

theorem c4_atkinLehnerBar_mem_integersFst (hqN : ¬ q ∣ N) (t : ↥(jIntegralClosure (N * q) A K)) :
    ProlongationTuple.atkinLehnerBar N q (c4_toBar K t) ∈ R.R₁.integers :=
  (R.mem_integers₂_iff _).mp (c4_mem_integersSnd R hqN K _ t.2)

def c4_res₂C (hqN : ¬ q ∣ N) : ↥(jIntegralClosure (N * q) A K) →+* modularFunctionFieldC k N where
  toFun t := R.residue₂ ⟨c4_toBar K t, c4_mem_integersSnd R hqN K _ t.2⟩
  map_one' := by
    rw [show (⟨c4_toBar K (1 : ↥(jIntegralClosure (N * q) A K)), c4_mem_integersSnd R hqN K _
      (1 : ↥(jIntegralClosure (N * q) A K)).2⟩ : ↥R.R₂.integers) = 1 from Subtype.ext rfl, map_one]
  map_mul' s t := by
    rw [show (⟨c4_toBar K (s * t), c4_mem_integersSnd R hqN K _ (s * t).2⟩ : ↥R.R₂.integers)
      = ⟨c4_toBar K s, c4_mem_integersSnd R hqN K _ s.2⟩ * ⟨c4_toBar K t, c4_mem_integersSnd R hqN K _ t.2⟩ from Subtype.ext rfl, map_mul]
  map_zero' := by
    rw [show (⟨c4_toBar K (0 : ↥(jIntegralClosure (N * q) A K)), c4_mem_integersSnd R hqN K _
      (0 : ↥(jIntegralClosure (N * q) A K)).2⟩ : ↥R.R₂.integers) = 0 from Subtype.ext rfl, map_zero]
  map_add' s t := by
    rw [show (⟨c4_toBar K (s + t), c4_mem_integersSnd R hqN K _ (s + t).2⟩ : ↥R.R₂.integers)
      = ⟨c4_toBar K s, c4_mem_integersSnd R hqN K _ s.2⟩ + ⟨c4_toBar K t, c4_mem_integersSnd R hqN K _ t.2⟩ from Subtype.ext rfl, map_add]

theorem c4_res₂C_apply (hqN : ¬ q ∣ N) (t : ↥(jIntegralClosure (N * q) A K)) :
    c4_res₂C R K hqN t = R.residue₂ ⟨c4_toBar K t, c4_mem_integersSnd R hqN K _ t.2⟩ := rfl

theorem c4_res₂C_eq (hqN : ¬ q ∣ N) (t : ↥(jIntegralClosure (N * q) A K)) :
    c4_res₂C R K hqN t = R.residue₁ ⟨_, c4_atkinLehnerBar_mem_integersFst R K hqN t⟩ :=
  c4_residue₂_eq_residue₁_atkinLehnerBar R (c4_toBar K t) (c4_mem_integersSnd R hqN K _ t.2)
    (c4_atkinLehnerBar_mem_integersFst R K hqN t)

theorem c4_res₂C_mem_c4D (hqN : ¬ q ∣ N) (t : ↥(jIntegralClosure (N * q) A K)) : c4_res₂C R K hqN t ∈ c4D k N :=
  (c4_mem_c4D_iff).mpr (c4_isIntegral_adjoin_residue₂_of_mem_C R hqN K _ t.2 _)

def c4_g₂ (hqN : ¬ q ∣ N) : ↥(jIntegralClosure (N * q) A K) →+* ↥(c4D k N) :=
  (c4_res₂C R K hqN).codRestrict (c4D k N) (c4_res₂C_mem_c4D R K hqN)

theorem c4_coe_g₂ (hqN : ¬ q ∣ N) (t : ↥(jIntegralClosure (N * q) A K)) :
    ((c4_g₂ R K hqN t : ↥(c4D k N)) : modularFunctionFieldC k N) = R.residue₂ ⟨c4_toBar K t, c4_mem_integersSnd R hqN K _ t.2⟩ := rfl

theorem c4_coe_g₂_cst (hqN : ¬ q ∣ N) (a : ↥(coeffSubring A K)) :
    ((c4_g₂ R K hqN (c4_cst K a) : ↥(c4D k N)) : modularFunctionFieldC k N)
      = algebraMap k (modularFunctionFieldC k N) (redRestrict red K a) := by
  rw [c4_coe_g₂, ← c4_res₂C_apply R K hqN, c4_res₂C_eq R K hqN]
  have hW : ProlongationTuple.atkinLehnerBar N q (c4_toBar K (c4_cst K a))
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
    rw [c4_toBar_cst]
    exact (ProlongationTuple.atkinLehnerBar N q).commutes (a : AlgebraicClosure ℚ)
  obtain ⟨h', hres⟩ := penC_residue_const R ⟨(a : AlgebraicClosure ℚ), a.2.1⟩
  rw [show (⟨ProlongationTuple.atkinLehnerBar N q (c4_toBar K (c4_cst K a)), c4_atkinLehnerBar_mem_integersFst R K hqN (c4_cst K a)⟩
      : ↥R.R₁.integers) = ⟨_, h'⟩ from Subtype.ext hW]
  exact hres

omit [Fact q.Prime] [NeZero N] [CharP k q] in
theorem c4_coeffMap_jqModC {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) : coeffMap f (jqModC S) = jqModC T :=
  map_jqModC f

theorem c4_residue₁_beta_jBar (h : heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) ∈ R.R₁.integers) :
    R.residue₁ ⟨heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N), h⟩ = jGeomGen k N ^ q := by
  have hcoe : ((heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (jqNModC A q) := by
    rw [coe_heckeBetaBar, jqNModC, coeffMap_qExpand, c4_coeffMap_jqModC]
    exact congrArg _ (c4_coe_jBar N)
  obtain ⟨h', hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  apply Subtype.ext
  rw [show (⟨_, h⟩ : ↥R.R₁.integers) = ⟨_, h'⟩ from rfl, hres, jqNModC, coeffMap_qExpand, c4_coeffMap_jqModC,
    qExpand_jqModC_eq_pow k data hKr, SubmonoidClass.coe_pow]
  rfl

theorem c4_coe_g₂_jC (hqN : ¬ q ∣ N) :
    ((c4_g₂ R K hqN (c4_jC K) : ↥(c4D k N)) : modularFunctionFieldC k N) = jGeomGen k N ^ q := by
  rw [c4_coe_g₂, ← c4_res₂C_apply R K hqN, c4_res₂C_eq R K hqN]
  have hW : ProlongationTuple.atkinLehnerBar N q (c4_toBar K (c4_jC K : ↥(jIntegralClosure (N * q) A K)))
      = heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) := by
    rw [c4_toBar_jC, c4_atkinLehnerBar_jBar hqN]
  have h' : heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) ∈ R.R₁.integers := hW ▸ c4_atkinLehnerBar_mem_integersFst R K hqN _
  rw [show (⟨ProlongationTuple.atkinLehnerBar N q (c4_toBar K (c4_jC K)), c4_atkinLehnerBar_mem_integersFst R K hqN (c4_jC K)⟩
      : ↥R.R₁.integers) = ⟨_, h'⟩ from Subtype.ext hW]
  exact c4_residue₁_beta_jBar R h'

end ResidueHoms
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization"

end ModularCurve.PlaceSpecialization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1 ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section IntegralOverC

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] (red : A →+* k)

theorem c4_algebra_isIntegral_c4D (hred : Function.Surjective red)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g : ↥(jIntegralClosure (N * q) A K) →+* ↥(c4D k N))
    (hconst : ∀ a : ↥(coeffSubring A K), ∃ c, ((g c : ↥(c4D k N)) : modularFunctionFieldC k N)
      = algebraMap k (modularFunctionFieldC k N) (redRestrict red K a))
    (hj : ∃ c, ∃ n : ℕ, 0 < n ∧ ((g c : ↥(c4D k N)) : modularFunctionFieldC k N) = jGeomGen k N ^ n) :
    @Algebra.IsIntegral ↥(jIntegralClosure (N * q) A K) ↥(c4D k N) _ _ g.toAlgebra :=
  ModularCurve.algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq red hred K g hconst hj

end IntegralOverC
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization"

end ModularCurve.PlaceSpecialization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.constSeries NodeLocalized.redRestrict CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.FibreModel isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed exists_ord_sub_pos_of_integral_affineBaseFin PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1 ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section C4aAssembly

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem c4_finiteDimensional_finset_sup {ι : Type*} (s : Finset ι) (f : ι → IntermediateField ℚ (AlgebraicClosure ℚ))
    (hf : ∀ i ∈ s, FiniteDimensional ℚ ↥(f i)) : FiniteDimensional ℚ ↥(s.sup f) := by
  classical
  refine Finset.sup_induction (p := fun K : IntermediateField ℚ (AlgebraicClosure ℚ) => FiniteDimensional ℚ K)
    (inferInstance : FiniteDimensional ℚ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ))) ?_ hf
  intro K₁ hK₁ K₂ hK₂
  haveI := hK₁; haveI := hK₂
  exact IntermediateField.finiteDimensional_sup K₁ K₂

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem c4a_toBar_mk (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    c4_toBar K (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K)) = t :=
  Subtype.ext rfl

variable (w : Place k (modularFunctionFieldC k N)) (hw : jGeomGen k N ∈ w.toValuationSubring)

theorem c4a_mem_comap_g₁_iff (hqN : ¬ q ∣ N) (s : ↥(jIntegralClosure (N * q) A K)) :
    s ∈ (c4_M w hw).comap (c4_g₁ R K hqN) ↔
      w.HasValue (R.residue₁ ⟨c4_toBar K s, c4_mem_integersFst R K _ s.2⟩ : modularFunctionFieldC k N) (0 : k) := by
  rw [Ideal.mem_comap, c4_mem_M_iff]
  rfl

theorem c4a_mem_comap_g₂_iff (hqN : ¬ q ∣ N) (u : Place k (modularFunctionFieldC k N)) (hu : jGeomGen k N ∈ u.toValuationSubring)
    (s : ↥(jIntegralClosure (N * q) A K)) :
    s ∈ (c4_M u hu).comap (c4_g₂ R K hqN) ↔
      u.HasValue (R.residue₂ ⟨c4_toBar K s, c4_mem_integersSnd R hqN K _ s.2⟩ : modularFunctionFieldC k N) (0 : k) := by
  rw [Ideal.mem_comap, c4_mem_M_iff]
  rfl

theorem c4a_g₂_beta (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (b : fm.BFin)
    (hβC : ((heckeBetaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N) : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    ((c4_g₂ R K hqN ⟨_, hβC⟩ : ↥(c4D k N)) : modularFunctionFieldC k N) = fm.piFin b := by
  rw [c4_coe_g₂]
  have hβ₂ : heckeBetaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N) ∈ R.R₂.integers :=
    penC_beta_mem_snd R hqN fm b
  rw [← penC_residue₂_beta R hqN fm b hβ₂]
  congr 1

theorem c4a_g₁_beta (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (b : fm.BFin)
    (hβC : ((heckeBetaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N) : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    ((c4_g₁ R K hqN ⟨_, hβC⟩ : ↥(c4D k N)) : modularFunctionFieldC k N) = frobeniusGeomLevel k N data hKr (fm.piFin b) := by
  rw [c4_coe_g₁]
  obtain ⟨hβI, hres⟩ := penC_residue_beta R fm b
  rw [← hres]
  congr 1

theorem c4a_ker_g₂_le_n₁ [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) [FiniteDimensional ℚ K]
    (hwss : w ∈ ssPlaces q N k) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = w.evalAt (jGeomGen k N)) :
    RingHom.ker (c4_g₂ R K hqN) ≤ (c4_M w hw).comap (c4_g₁ R K hqN) := by
  intro s hs
  rw [c4a_mem_comap_g₁_iff R K w hw hqN]
  have hs' : R.residue₂ ⟨c4_toBar K s, c4_mem_integersSnd R hqN K _ s.2⟩ = 0 := congrArg Subtype.val (RingHom.mem_ker.mp hs)
  obtain ⟨h₁, hval⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure
      R hqN K w hwss (w.evalAt (jGeomGen k N)) rfl x hx (c4_toBar K s) s.2 (c4_mem_integersSnd R hqN K _ s.2) hs'
  exact hval

theorem c4a_n₁_eq_n₂ [IsAlgClosed k] [DecidableEq k] (hred : Function.Surjective red) (hqN : ¬ q ∣ N) [FiniteDimensional ℚ K]
    (fm : FibreModel N A q k red) (hwss : w ∈ ssPlaces q N k)
    (hφ : jGeomGen k N ∈ (arithFrobC q k N • w).toValuationSubring)
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = w.evalAt (jGeomGen k N))
    (S : Finset ↥(c4D k N)) (hS : Ideal.span (S : Set ↥(c4D k N)) = c4_M (arithFrobC q k N • w) hφ)
    (hSb : ∀ s ∈ S, ∃ b : fm.BFin, fm.piFin b = (s : modularFunctionFieldC k N) ∧
      ((heckeBetaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N) : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    (c4_M w hw).comap (c4_g₁ R K hqN) = (c4_M (arithFrobC q k N • w) hφ).comap (c4_g₂ R K hqN) := by
  letI := (c4_g₂ R K hqN).toAlgebra
  haveI := c4_algebra_isIntegral_c4D red hred K (c4_g₂ R K hqN)
    (fun a' => ⟨c4_cst K a', c4_coe_g₂_cst R K hqN a'⟩) ⟨c4_jC K, q, (Fact.out : q.Prime).pos, c4_coe_g₂_jC R K hqN⟩
  haveI hMw : (c4_M w hw).IsMaximal := c4_isMaximal_M w hw hwss.1
  haveI : ((c4_M w hw).comap (c4_g₁ R K hqN)).IsPrime := Ideal.comap_isPrime _ _
  haveI := c4_isMaximal_M (arithFrobC q k N • w) hφ (ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k w hwss).1
  refine c4_eq_comap_of_span ((c4_M w hw).comap (c4_g₁ R K hqN)) (c4a_ker_g₂_le_n₁ R K w hw hqN hwss x hx)
    (c4_M (arithFrobC q k N • w) hφ) (S : Set ↥(c4D k N)) hS.symm (fun s hs => ?_)
  obtain ⟨b, hb, hβC⟩ := hSb s hs
  refine ⟨⟨_, hβC⟩, ?_, Subtype.ext ((c4a_g₂_beta R K hqN fm b hβC).trans hb)⟩

  rw [c4a_mem_comap_g₁_iff R K w hw hqN]
  have hs0 : (arithFrobC q k N • w).HasValue (s : modularFunctionFieldC k N) (0 : k) :=
    (c4_mem_M_iff _ hφ s).mp (hS ▸ Ideal.subset_span hs)
  rw [arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr] at hs0
  have hF := penC_hasValue_frob_apply (data := data) (hKr := hKr) w hs0
  rw [← hb] at hF
  have e : (R.residue₁ ⟨c4_toBar K ⟨_, hβC⟩, c4_mem_integersFst R K _ hβC⟩ : modularFunctionFieldC k N)
      = frobeniusGeomLevel k N data hKr (fm.piFin b) := c4a_g₁_beta R K hqN fm b hβC
  rw [e]
  exact hF

theorem c4a_exists_hasValue_redRestrict [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) [FiniteDimensional ℚ K]
    (hwss : w ∈ ssPlaces q N k)
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (t : modularFunctionFieldBar (N * q)) (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    ∃ (c : ↥(coeffSubring A K)) (h₁ : t ∈ R.R₁.integers),
      w.HasValue (R.residue₁ ⟨t, h₁⟩ : modularFunctionFieldC k N) (NodeLocalized.redRestrict red K c) := by
  have h₁ : t ∈ R.R₁.integers := c4_mem_integersFst R K t ht
  have hreg : (R.residue₁ ⟨t, h₁⟩ : modularFunctionFieldC k N) ∈ w.toValuationSubring :=
    w.mem_toValuationSubring_of_isIntegral_adjoin hwss.2.1.1 (c4_isIntegral_adjoin_residue₁_of_mem_C R hqN K t ht h₁)
  obtain ⟨a, ha, -⟩ := w.exists_hasValue_of_surjective (penC_residue_surjective w) hreg
  have hg : t ∈ R.nodeIntegersOver K w := c4_mem_nodeIntegersOver R hqN K w hwss.2.1.1 t ht
  have ha' : w.HasValue (R.nodeResidue₁ w ⟨t, hg.1⟩ : modularFunctionFieldC k N) a := by
    rw [ProlongationTuple.nodeResidue₁_apply]
    exact ha
  obtain ⟨c, hc⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst
      R hqN K w hwss hk₀ ⟨t, hg⟩ a ha'
  exact ⟨c, h₁, hc ▸ ha⟩

end C4aAssembly
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization"

end ModularCurve.PlaceSpecialization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization"

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (fm : CharPModel.FibreModel N A q k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hP : P.sp = fm.spPlace hred dataAll hsep)
    (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    ∀ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K →
      ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
        ∀ (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ K'' → K' ≤ K'' →
          (∀ (t : ↥(modularFunctionFieldBar (N * q))),
              (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' →
              ((∃ h₁ : t ∈ R.R₁.integers,
                  w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
                (∃ h₂ : t ∈ R.R₂.integers,
                  (arithFrobC q k N • w).HasValue (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) (0 : k)))) ∧
          (∀ (t : ↥(modularFunctionFieldBar (N * q))),
              (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' →
              ∃ (c : ↥(coeffSubring A K'')) (h₁ : t ∈ R.R₁.integers),
                w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (redRestrict red K'' c)) := by
  classical
  intro K hK
  haveI := hK
  have hwaff : jGeomGen k N ∈ w.toValuationSubring := hw.2.1.1
  have hw' : arithFrobC q k N • w ∈ ssPlaces q N k := ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k w hw
  have hφaff : jGeomGen k N ∈ (arithFrobC q k N • w).toValuationSubring := hw'.2.1.1

  obtain ⟨a₀, ha₀⟩ := hred (w.evalAt (jGeomGen k N))
  have halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  haveI hKa : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ {(a₀ : AlgebraicClosure ℚ)}) :=
    IntermediateField.adjoin.finiteDimensional (halg.isAlgebraic _).isIntegral

  have hq2 : (q ^ 2) ≠ 1 := (Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt).ne'
  have hpne : (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : Polynomial k => p.coeff (q ^ 2)) h
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, Polynomial.coeff_X_of_ne_one hq2, sub_zero,
      Polynomial.coeff_zero] at hc
    exact one_ne_zero hc
  obtain ⟨Kθ, hKθ, -, hθ⟩ :=
    ModularCurve.NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict q A k red
      ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset) (fun a ha => by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hpne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, sub_eq_zero] at ha
        exact ha)
  haveI := hKθ

  obtain ⟨Sφ, hSφ⟩ := c4_exists_finset_span_eq_M (k := k) (dataAll N (dvd_refl N)) hsep (arithFrobC q k N • w) hφaff
  choose bOf hbOf using fun r : ↥(c4D k N) => c4_exists_piFin_eq fm hred r
  choose KOf hKOf hKmem using fun b : fm.BFin => c4_exists_fd_forall_degeneracies_mem (A := A) (k := k) (red := red) fm b
  let K₂ : IntermediateField ℚ (AlgebraicClosure ℚ) := Sφ.sup (fun r => KOf (bOf r))
  haveI hK₂ : FiniteDimensional ℚ K₂ := c4_finiteDimensional_finset_sup _ _ (fun r _ => hKOf (bOf r))

  refine ⟨K ⊔ IntermediateField.adjoin ℚ {(a₀ : AlgebraicClosure ℚ)} ⊔ Kθ ⊔ K₂, inferInstance,
    le_sup_left.trans (le_sup_left.trans le_sup_left), ?_⟩
  intro K'' hK'' hle
  haveI := hK''
  have hKa₀ : IntermediateField.adjoin ℚ {(a₀ : AlgebraicClosure ℚ)} ≤ K'' := le_sup_right.trans (le_sup_left.trans (le_sup_left.trans hle))
  have hKθle : Kθ ≤ K'' := le_sup_right.trans (le_sup_left.trans hle)
  have hK₂le : ∀ r ∈ Sφ, KOf (bOf r) ≤ K'' := fun r hr => (Finset.le_sup (f := fun r => KOf (bOf r)) hr).trans (le_sup_right.trans hle)

  let x : ↥(coeffSubring A K'') := ⟨(a₀ : AlgebraicClosure ℚ), a₀.2, hKa₀ (IntermediateField.mem_adjoin_simple_self ℚ _)⟩
  have hx : redRestrict red K'' x = w.evalAt (jGeomGen k N) := ha₀

  have hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K'') := by
    intro a ha
    have hmem : a ∈ ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset) := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hpne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, sub_eq_zero]
      exact ha
    obtain ⟨y, hy⟩ := hθ a hmem
    exact ⟨⟨(y : AlgebraicClosure ℚ), y.2.1, hKθle y.2.2⟩, hy⟩

  have hn : (c4_M w hwaff).comap (c4_g₁ R K'' hqN) = (c4_M (arithFrobC q k N • w) hφaff).comap (c4_g₂ R K'' hqN) :=
    c4a_n₁_eq_n₂ R K'' w hwaff hred hqN fm hw hφaff x hx Sφ hSφ
      (fun s hs => ⟨bOf s, hbOf s, (hKmem (bOf s) K'' (hK₂le s hs)).2⟩)
  refine ⟨fun t ht => ?_, fun t ht => c4a_exists_hasValue_redRestrict R K'' w hqN hw hk₀ t ht⟩
  have h := congrArg (fun I : Ideal ↥(jIntegralClosure (N * q) A K'') =>
    (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K'')) ∈ I) hn
  simp only [eq_iff_iff] at h
  rw [c4a_mem_comap_g₁_iff R K'' w hwaff hqN, c4a_mem_comap_g₂_iff] at h
  constructor
  · rintro ⟨h₁, h1⟩
    exact ⟨c4_mem_integersSnd R hqN K'' t ht, h.mp h1⟩
  · rintro ⟨h₂, h2⟩
    exact ⟨c4_mem_integersFst R K'' t ht, h.mpr h2⟩

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace.ModularCurve.PlaceSpecialization"

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_iff_residueSnd_jIntegralClosure_of_sp_eq_spPlace (solution)
