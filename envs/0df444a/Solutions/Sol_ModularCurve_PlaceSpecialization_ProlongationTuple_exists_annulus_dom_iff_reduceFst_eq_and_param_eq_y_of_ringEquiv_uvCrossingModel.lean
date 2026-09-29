-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/0d3767b9-506f-5bcb-9ada-bec4faee0e77

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_evalAt_lt_one_iff_mem_maximalIdeal
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_y_sub_algebraMap_evalAt_eq_one_of_ringEquiv_uvCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_zpow_unit_principle_evalAt_y_of_ringEquiv_uvCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_eq_of_evalAt_y_eq_of_reduceFst_eq_of_ringEquiv_uvCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ValuationSubring.instIsAlgClosedResidueField AdicCompletion.instIsLocalRingMaximalIdeal GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero"
p2m_attr_erase "simp" "TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst"
set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.hasValue_algebraMap Place Place.deg Annulus GaussReduction.ord_nonneg_of_mem_gen GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero Place.isRational_of_deg_eq_one' Place.evalAt_eq_of_hasValue' Place.hasValue_evalAt'"
p2m_open "AlgebraicCurve"

open IsLocalRing

namespace Place
p2m_export "AlgebraicCurve.Place" "HasValue hasValue_algebraMap ext ResidueField deg ord ord_zero ord_mul ord_inv algebraMap_mem' toValuationSubring IsRational evalAt algebraMap_evalAt evalAt_one isRational_of_deg_eq_one' evalAt_eq_of_hasValue' hasValue_evalAt'"
p2m_open "AlgebraicCurve.Place~evalAt_mul_of_mem"

private theorem evalAt_zero_of_isRational {L F : Type*} [Field L] [Field F] [Algebra L F]
    (v : Place L F) (hv : v.IsRational) : v.evalAt (0 : F) = 0 := by
  have h0 : (0 : F) ∈ v.toValuationSubring := zero_mem _
  have h := v.algebraMap_evalAt hv h0
  rw [show (⟨0, h0⟩ : v.toValuationSubring) = 0 from rfl, map_zero] at h
  exact (algebraMap L v.ResidueField).injective (h.trans (map_zero _).symm)

end Place

namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus modulus_mem dom mem_dom param ord_param_sub"
p2m_open "AlgebraicCurve.Annulus"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]

private theorem _root_.AlgebraicCurve.Annulus.param_ne_zero_of_mem_dom (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    An.param ≠ 0 := by
  obtain ⟨hrat, -, -, hne, -⟩ := An.mem_dom P hP
  intro h0
  rw [h0] at hne
  exact hne (Place.evalAt_zero_of_isRational P hrat)

p2m_export "AlgebraicCurve.Annulus" "param_ne_zero_of_mem_dom"

private theorem _root_.AlgebraicCurve.Annulus.ord_param_eq_zero_of_mem_dom (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    P.ord An.param = 0 := by
  obtain ⟨-, hreg, -, hne, -⟩ := An.mem_dom P hP
  have h0 : An.param ≠ 0 := An.param_ne_zero_of_mem_dom hP
  have hnn : 0 ≤ P.ord An.param := GaussReduction.ord_nonneg_of_mem_gen P hreg h0
  rcases hnn.lt_or_eq with hlt | heq
  · exact absurd (StandardAnnulus.evalAt_eq_zero_of_ord_pos P h0 hlt) hne
  · exact heq.symm

p2m_export "AlgebraicCurve.Annulus" "ord_param_eq_zero_of_mem_dom"

private theorem _root_.AlgebraicCurve.Annulus.inv_param_mem_of_mem_dom (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    An.param⁻¹ ∈ P.toValuationSubring := by
  have h0 : An.param ≠ 0 := An.param_ne_zero_of_mem_dom hP
  refine GaussReduction.mem_of_ord_nonneg_gen P (inv_ne_zero h0) ?_
  rw [P.ord_inv, An.ord_param_eq_zero_of_mem_dom hP]
  omega

p2m_export "AlgebraicCurve.Annulus" "inv_param_mem_of_mem_dom"

private theorem _root_.AlgebraicCurve.Annulus.evalAt_modulus_mul_param_inv (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    P.evalAt (algebraMap L F ((An.modulus : L)) * An.param⁻¹)
      = (An.modulus : L) * (P.evalAt An.param)⁻¹ := by
  obtain ⟨hrat, -, -, -, -⟩ := An.mem_dom P hP
  have h0 : An.param ≠ 0 := An.param_ne_zero_of_mem_dom hP
  have hord := An.ord_param_eq_zero_of_mem_dom hP
  rw [GaussReduction.evalAt_mul_of_mem P hrat (P.algebraMap_mem' _)
      (An.inv_param_mem_of_mem_dom hP),
    GaussReduction.evalAt_algebraMap_const P hrat,
    StandardAnnulus.evalAt_inv_of_ord_eq_zero P hrat h0 hord]

p2m_export "AlgebraicCurve.Annulus" "evalAt_modulus_mul_param_inv"

private def _root_.AlgebraicCurve.Annulus.opposite (An : Annulus A F) (hπ : ((An.modulus : L)) ≠ 0) : Annulus A F where
  dom := An.dom
  param := algebraMap L F ((An.modulus : L)) * An.param⁻¹
  modulus := An.modulus
  modulus_mem := An.modulus_mem
  mem_dom := by
    intro P hP
    obtain ⟨hrat, -, ⟨hmemA, hm𝔪⟩, hne, m, hm, hprod⟩ := An.mem_dom P hP
    have hev : P.evalAt (algebraMap L F ((An.modulus : L)) * An.param⁻¹)
        = (An.modulus : L) * (P.evalAt An.param)⁻¹ := An.evalAt_modulus_mul_param_inv hP
    have hm0 : (m : L) ≠ 0 := by
      intro h0
      exact hπ (by rw [hprod, h0, mul_zero])
    have hevm : P.evalAt (algebraMap L F ((An.modulus : L)) * An.param⁻¹) = (m : L) := by
      rw [hev, hprod]
      field_simp
    refine ⟨hrat, mul_mem (P.algebraMap_mem' _) (An.inv_param_mem_of_mem_dom hP), ?_, ?_, ?_⟩
    · rw [hevm]
      exact ⟨m.2, by simpa using hm⟩
    · rw [hevm]
      exact hm0
    · refine ⟨⟨P.evalAt An.param, hmemA⟩, hm𝔪, ?_⟩
      rw [hevm, hprod]
      ring
  existsUnique_evalAt_eq := by
    intro c hc hc0 hadm
    obtain ⟨d, hd, hcd⟩ := hadm
    have hd0 : (d : L) ≠ 0 := by
      intro h0
      exact hπ (by rw [hcd, h0, mul_zero])
    obtain ⟨P, ⟨hPdom, hPeval⟩, huniq⟩ :=
      An.existsUnique_evalAt_eq d hd hd0 ⟨c, hc, by rw [hcd]; ring⟩
    refine ⟨P, ⟨hPdom, ?_⟩, ?_⟩
    · rw [An.evalAt_modulus_mul_param_inv hPdom, hPeval, hcd]
      field_simp
    · rintro Q ⟨hQdom, hQeval⟩
      apply huniq
      refine ⟨hQdom, ?_⟩
      obtain ⟨-, -, -, htQ, -⟩ := An.mem_dom Q hQdom
      rw [An.evalAt_modulus_mul_param_inv hQdom, ← div_eq_mul_inv, div_eq_iff htQ] at hQeval
      rw [hcd] at hQeval
      exact mul_left_cancel₀ hc0 hQeval.symm
  ord_param_sub := by
    intro P hP
    obtain ⟨-, -, -, hne, -⟩ := An.mem_dom P hP
    have h0 : An.param ≠ 0 := An.param_ne_zero_of_mem_dom hP
    have hord := An.ord_param_eq_zero_of_mem_dom hP
    have hev := An.evalAt_modulus_mul_param_inv hP
    rw [hev]
    have hbF : algebraMap L F (P.evalAt An.param) ≠ 0 := (map_ne_zero _).mpr hne
    have hsub : An.param - algebraMap L F (P.evalAt An.param) ≠ 0 := by
      intro hz0
      have h1 := An.ord_param_sub P hP
      rw [hz0, P.ord_zero] at h1
      exact one_ne_zero h1.symm
    have hfact : algebraMap L F ((An.modulus : L)) * An.param⁻¹
          - algebraMap L F ((An.modulus : L) * (P.evalAt An.param)⁻¹)
        = algebraMap L F (-((An.modulus : L) * (P.evalAt An.param)⁻¹))
            * (An.param - algebraMap L F (P.evalAt An.param)) * An.param⁻¹ := by
      simp only [map_neg, map_mul, map_inv₀]
      field_simp
      ring
    rw [hfact]
    have hA1 : algebraMap L F (-((An.modulus : L) * (P.evalAt An.param)⁻¹)) ≠ 0 :=
      (map_ne_zero _).mpr (neg_ne_zero.mpr (mul_ne_zero hπ (inv_ne_zero (fun h =>
        hne h))))
    rw [P.ord_mul (mul_ne_zero hA1 hsub) (inv_ne_zero h0), P.ord_mul hA1 hsub,
      StandardAnnulus.ord_algebraMap_eq_zero P
        (neg_ne_zero.mpr (mul_ne_zero hπ (inv_ne_zero (fun h => hne h)))),
      An.ord_param_sub P hP, P.ord_inv, hord]
    omega
  unit_principle := by
    intro f hf0 hords
    obtain ⟨m, c, hc0, hP⟩ := An.unit_principle f hf0 hords
    refine ⟨-m, c * (An.modulus : L) ^ m, mul_ne_zero hc0 (zpow_ne_zero m hπ), ?_⟩
    intro P hP'
    obtain ⟨-, -, -, hne, -⟩ := An.mem_dom P hP'
    obtain ⟨hwit, hunit⟩ := hP P hP'
    have hev := An.evalAt_modulus_mul_param_inv hP'
    have e1 : ((An.modulus : L) * (P.evalAt An.param)⁻¹) ^ m
        = (An.modulus : L) ^ m * (P.evalAt An.param) ^ (-m) := by
      rw [mul_zpow, inv_zpow, ← zpow_neg]
    have hkey : P.evalAt f * (c * (An.modulus : L) ^ m)⁻¹
          * (P.evalAt (algebraMap L F ((An.modulus : L)) * An.param⁻¹)) ^ (-(-m))
        = P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m) := by
      rw [hev, neg_neg, e1, mul_inv,
        show P.evalAt f * (c⁻¹ * ((An.modulus : L) ^ m)⁻¹)
            * ((An.modulus : L) ^ m * (P.evalAt An.param) ^ (-m))
          = P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m)
              * (((An.modulus : L) ^ m)⁻¹ * (An.modulus : L) ^ m) from by ring,
        inv_mul_cancel₀ (zpow_ne_zero m hπ), mul_one]
    rw [hkey]
    exact ⟨hwit, hunit⟩

p2m_export "AlgebraicCurve.Annulus" "opposite"

private theorem opposite_dom (An : Annulus A F) (hπ : ((An.modulus : L)) ≠ 0) :
    (An.opposite hπ).dom = An.dom := rfl

private theorem opposite_modulus (An : Annulus A F) (hπ : ((An.modulus : L)) ≠ 0) :
    (An.opposite hπ).modulus = An.modulus := rfl

private theorem opposite_param (An : Annulus A F) (hπ : ((An.modulus : L)) ≠ 0) :
    (An.opposite hπ).param = algebraMap L F ((An.modulus : L)) * An.param⁻¹ := rfl

private theorem opposite_param_mul (An : Annulus A F) (hπ : ((An.modulus : L)) ≠ 0)
    (hz : An.param ≠ 0) :
    (An.opposite hπ).param * An.param = algebraMap L F ((An.modulus : L)) := by
  rw [opposite_param, mul_assoc, inv_mul_cancel₀ hz, mul_one]

private theorem opposite_pair_spec (An : Annulus A F) (hπ : ((An.modulus : L)) ≠ 0)
    (hz : An.param ≠ 0) :
    (An.opposite hπ).dom = An.dom ∧ (An.opposite hπ).modulus = An.modulus ∧
      (((An.modulus : L)) ≠ 0) ∧
      (An.opposite hπ).param * An.param = algebraMap L F ((An.modulus : L)) :=
  ⟨rfl, rfl, hπ, opposite_param_mul An hπ hz⟩

end Annulus

end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence ssPlaces arithFrobC NodeLocalized.coeffSubring NodeLocalized.redRestrict UVCrossingModel arithFrobC_smul_eq_frobOnPlacesGeomLevel deg_eq_one_modularFunctionFieldBar"
namespace NodeAnnulusSkel
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel.AlgebraicCurve IsLocalRing"

private theorem _root_.AlgebraicCurve.Place.isRational_of_deg_eq_one' {L F : Type*} [Field L] [Field F]
    [Algebra L F] (v : Place L F) (h : v.deg = 1) : v.IsRational := by
  intro z
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra L v.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra L v.ResidueField) := by
    rw [hbt]
    exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel.AlgebraicCurve.Place.isRational_of_deg_eq_one'" "AlgebraicCurve.Place.isRational_of_deg_eq_one'"
private theorem isRational_place (M : ℕ) [NeZero M] (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) :
    V.IsRational :=
  V.isRational_of_deg_eq_one' (deg_eq_one_modularFunctionFieldBar M V)

private theorem _root_.AlgebraicCurve.Place.evalAt_eq_of_hasValue' {L F : Type*} [Field L] [Field F]
    [Algebra L F] {v : Place L F} (hv : v.IsRational) {g : F} {a : L} (h : v.HasValue g a) :
    v.evalAt g = a := by
  obtain ⟨hm, hres⟩ := h
  have h1 := v.algebraMap_evalAt hv hm
  exact (algebraMap L v.ResidueField).injective (h1.trans hres)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel.AlgebraicCurve.Place.evalAt_eq_of_hasValue'" "AlgebraicCurve.Place.evalAt_eq_of_hasValue'"
private theorem _root_.AlgebraicCurve.Place.hasValue_evalAt' {L F : Type*} [Field L] [Field F]
    [Algebra L F] {v : Place L F} (hv : v.IsRational) {g : F}
    (hm : g ∈ v.toValuationSubring) : v.HasValue g (v.evalAt g) :=
  ⟨hm, (v.algebraMap_evalAt hv hm).symm⟩

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel.AlgebraicCurve.Place.hasValue_evalAt'" "AlgebraicCurve.Place.hasValue_evalAt'"
variable {A : ValuationSubring (AlgebraicClosure ℚ)} (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem coeffSubring_le : NodeLocalized.coeffSubring A K ≤ A.toSubring := inf_le_left

private def inclA : ↥(NodeLocalized.coeffSubring A K) →+* ↥A := Subring.inclusion (coeffSubring_le (A := A) K)

private theorem coe_inclA (d : ↥(NodeLocalized.coeffSubring A K)) : ((inclA K d : ↥A) : AlgebraicClosure ℚ) = (d : AlgebraicClosure ℚ) := rfl

end ModularCurve.NodeAnnulusSkel

end

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel.ModularCurve ModularCurve.UVCrossingModel"
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open ModularCurve.NodeAnnulusSkel

set_option maxHeartbeats 3200000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (hord : R.OrderLawFixed)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hvalA : R.ValueIntegralityLaw w)
    (hres : ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
    (hσπ : σ π = algebraMap _ _ (R.nodeConst K w ϖ))
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
          w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
          (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (c : R.NodeCoordinates K w) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u) :
    ∃ An An' : Annulus A ↥(modularFunctionFieldBar (N * q)),
      (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        V' ∈ An.dom ↔ (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V')) ∧
      An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      (An.modulus : AlgebraicClosure ℚ) = (ϖ : AlgebraicClosure ℚ) ^ E₀ ∧
      An.param = (↑c.y : ↥(modularFunctionFieldBar (N * q))) ∧
      An'.param * An.param
        = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (An.modulus : AlgebraicClosure ℚ) := by
  classical

  have hexu : ∀ c₀ : A, c₀ ∈ maximalIdeal A → (c₀ : AlgebraicClosure ℚ) ≠ 0 →
      (∃ m ∈ maximalIdeal A, ((inclA K ϖ ^ E₀ : A) : AlgebraicClosure ℚ) = c₀ * m) →
      ∃! V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w ∧ V'.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))) = c₀ := by
    intro c₀ hc₀ hne hwin
    obtain ⟨m, hm, hm'⟩ := hwin
    have hwin' : (ϖ : AlgebraicClosure ℚ) ^ E₀ = (c₀ : AlgebraicClosure ℚ) * (m : AlgebraicClosure ℚ) :=
      (SubmonoidClass.coe_pow (inclA K ϖ) E₀).symm.trans hm'
    have hwin₂ : ∃ m ∈ maximalIdeal A,
        (ϖ : AlgebraicClosure ℚ) ^ E₀ = (c₀ : AlgebraicClosure ℚ) * (m : AlgebraicClosure ℚ) := ⟨m, hm, hwin'⟩
    have hex₁ :=
      exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel
        R hqN hmodel hord K w hw hvalA hres ϖ hϖ π hπ σ hσπ E hE ι hconst hres₁ hres₂ c E₀ u hu hxy
        c₀ hc₀ hne hwin₂
    obtain ⟨V₀, hV₀, hy₀⟩ := hex₁
    have hE4 : ∀ V V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        P.reduceFst V' = w →
        V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))) = V'.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))) →
        V = V' := by
      exact
        eq_of_evalAt_y_eq_of_reduceFst_eq_of_ringEquiv_uvCrossingModel
          R hqN hmodel hord K w hw hvalA hres ϖ hϖ π hπ σ hσπ E hE ι hconst hres₁ hres₂ c E₀ u hu hxy
    exact ⟨V₀, ⟨hV₀, hy₀⟩, fun V₁ hV₁ => hE4 V₁ V₀ hV₁.1 hV₀ (hV₁.2.trans hy₀.symm)⟩
  have hunif :=
    ord_y_sub_algebraMap_evalAt_eq_one_of_ringEquiv_uvCrossingModel
      R hqN hmodel hord K w hw hvalA hres ϖ hϖ π hπ σ hσπ E hE ι hconst hres₁ hres₂ c E₀ u hu hxy
  have hunit :=
    exists_zpow_unit_principle_evalAt_y_of_ringEquiv_uvCrossingModel
      R hqN hmodel hord K w hw hvalA hres ϖ hϖ π hπ σ hσπ E hE ι hconst hres₁ hres₂ c E₀ u hu hxy

  have hrat : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V'.IsRational := fun V' => isRational_place (N * q) V'
  have hreg : ∀ (g : ↥(R.nodeIntegersOver K w)) (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), P.reduceFst V' = w →
      (g : ↥(modularFunctionFieldBar (N * q))) ∈ V'.toValuationSubring := fun g V' hV' => g.2.1.2.2 V' hV'
  have hval : ∀ (g : ↥(R.nodeIntegersOver K w)) (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), P.reduceFst V' = w →
      V'.evalAt (g : ↥(modularFunctionFieldBar (N * q))) ∈ A := fun g V' hV' => hvalA (g : ↥(modularFunctionFieldBar (N * q))) g.2.1 V' hV'
  have hev_mul : ∀ (g h : ↥(R.nodeIntegersOver K w)) (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), P.reduceFst V' = w →
      V'.evalAt ((g * h : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = V'.evalAt (g : ↥(modularFunctionFieldBar (N * q))) * V'.evalAt (h : ↥(modularFunctionFieldBar (N * q))) := by
    intro g h V' hV'
    have hg := Place.hasValue_evalAt' (v := V') (hrat V') (hreg g V' hV')
    have hh := Place.hasValue_evalAt' (v := V') (hrat V') (hreg h V' hV')
    exact Place.evalAt_eq_of_hasValue' (hrat V') (hg.mul hh)
  have hev_const : ∀ (d : ↥(NodeLocalized.coeffSubring A K)) (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      V'.evalAt ((R.nodeConst K w d : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = (d : AlgebraicClosure ℚ) := by
    intro d V'
    rw [coe_nodeConst]
    exact Place.evalAt_eq_of_hasValue' (hrat V') (Place.hasValue_algebraMap (v := V') _)

  have hle : R.nodeIntegersOver K w ≤ R.nodeIntegers w := fun f hf => hf.1
  have hx_nonunit : ¬ IsUnit c.x := by
    intro hxu
    have h1 : IsUnit (R.nodeResidue₁ w (Subring.inclusion hle c.x)) :=
      (hxu.map (Subring.inclusion hle)).map (R.nodeResidue₁ w)
    exact h1.ne_zero c.x_fst
  have hy_nonunit : ¬ IsUnit c.y := by
    intro hyu
    have h1 : IsUnit (R.nodeResidue₂ w (Subring.inclusion hle c.y)) :=
      (hyu.map (Subring.inclusion hle)).map (R.nodeResidue₂ w)
    exact h1.ne_zero c.y_snd
  have hxmem : c.x ∈ maximalIdeal ↥(R.nodeIntegersOver K w) := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hymem : c.y ∈ maximalIdeal ↥(R.nodeIntegersOver K w) := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hϖ0 : (ϖ : AlgebraicClosure ℚ) ≠ 0 := by
    have hq : NodeLocalized.redRestrict red K ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = 0 := by
      rw [map_natCast]
      exact CharP.cast_eq_zero k q
    obtain ⟨d', hd'⟩ := (hϖ _).1 hq
    intro h0
    have hϖz : ϖ = 0 := Subtype.ext h0
    have h1 := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K) => (z : AlgebraicClosure ℚ)) hd'
    simp only [hϖz, zero_mul, SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h1
    exact (Fact.out : q.Prime).ne_zero h1
  have hu_val : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
      ∃ hA : V'.evalAt (u : ↥(modularFunctionFieldBar (N * q))) ∈ A, IsUnit (⟨V'.evalAt (u : ↥(modularFunctionFieldBar (N * q))), hA⟩ : A) := by
    intro V' hV'
    obtain ⟨uu, rfl⟩ := hu
    refine ⟨hval _ V' hV', ?_⟩
    refine IsUnit.of_mul_eq_one ⟨_, hval ((uu⁻¹ : (↥(R.nodeIntegersOver K w))ˣ) : ↥(R.nodeIntegersOver K w)) V' hV'⟩ ?_
    apply Subtype.ext
    show V'.evalAt ((uu : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
        * V'.evalAt (((uu⁻¹ : (↥(R.nodeIntegersOver K w))ˣ) : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = 1
    rw [← hev_mul _ _ V' hV', Units.mul_inv]
    exact V'.evalAt_one

  have hprod : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
      V'.evalAt (c.x : ↥(modularFunctionFieldBar (N * q))) * V'.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))) = (ϖ : AlgebraicClosure ℚ) ^ E₀ * V'.evalAt (u : ↥(modularFunctionFieldBar (N * q))) := by
    intro V' hV'
    rw [← hev_mul _ _ V' hV', hxy, hev_mul _ _ V' hV', ← map_pow, hev_const]
    rw [SubmonoidClass.coe_pow]
  have hy0 : (c.y : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
    intro hy
    have hxyF := congrArg (fun z : ↥(R.nodeIntegersOver K w) => (z : ↥(modularFunctionFieldBar (N * q)))) hxy
    simp only [Subring.coe_mul, Subring.coe_pow, coe_nodeConst, hy, mul_zero] at hxyF
    rcases mul_eq_zero.1 hxyF.symm with h | h
    · exact hϖ0 ((map_eq_zero _).1 (eq_zero_of_pow_eq_zero h))
    · exact hu.ne_zero (Subtype.ext h)

  have hE₀ : E₀ ≠ 0 := by
    rintro rfl
    apply hx_nonunit
    have h1 : IsUnit (c.x * c.y) := by
      rw [hxy, pow_zero, one_mul]
      exact hu
    exact isUnit_of_mul_isUnit_left h1
  have hmodmem : inclA K ϖ ^ E₀ ∈ maximalIdeal A := by
    have hϖm : inclA K ϖ ∈ maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hunit
      have h1 : IsUnit (red (inclA K ϖ)) := hunit.map red
      have h2 : red (inclA K ϖ) = 0 := (hϖ ϖ).2 ⟨1, (mul_one ϖ).symm⟩
      exact h1.ne_zero h2
    exact Ideal.pow_mem_of_mem _ hϖm E₀ (Nat.pos_of_ne_zero hE₀)
  have hmod0 : ((inclA K ϖ ^ E₀ : A) : AlgebraicClosure ℚ) ≠ 0 := by
    rw [SubmonoidClass.coe_pow, coe_inclA]
    exact pow_ne_zero _ hϖ0
  have hmem : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
      (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ V'.toValuationSubring ∧
      (∃ h : V'.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ A, (⟨V'.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))), h⟩ : A) ∈ maximalIdeal A) ∧
      V'.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))) ≠ 0 ∧
      ∃ m ∈ maximalIdeal A, ((inclA K ϖ ^ E₀ : A) : AlgebraicClosure ℚ) = V'.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))) * m := by
    intro V' hV'
    have hxA := hval c.x V' hV'
    have hyA := hval c.y V' hV'
    obtain ⟨huA, huu⟩ := hu_val V' hV'
    have hxm : (⟨V'.evalAt (c.x : ↥(modularFunctionFieldBar (N * q))), hxA⟩ : A) ∈ maximalIdeal A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      exact (valuation_evalAt_lt_one_iff_mem_maximalIdeal R K w hvalA V' hV' c.x).2 hxmem
    have hym : (⟨V'.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))), hyA⟩ : A) ∈ maximalIdeal A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      exact (valuation_evalAt_lt_one_iff_mem_maximalIdeal R K w hvalA V' hV' c.y).2 hymem
    have hp := hprod V' hV'
    have hwuF : (((huu.unit⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) * V'.evalAt (u : ↥(modularFunctionFieldBar (N * q))) = 1 := by
      have h1 := congrArg (fun z : A => (z : AlgebraicClosure ℚ)) (Units.inv_mul huu.unit)
      rw [huu.unit_spec] at h1
      exact h1
    have huv0 : V'.evalAt (u : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => by simp [h] at hwuF
    refine ⟨hreg c.y V' hV', ⟨hyA, hym⟩, ?_, ⟨⟨V'.evalAt (c.x : ↥(modularFunctionFieldBar (N * q))), hxA⟩ * ((huu.unit⁻¹ : Aˣ) : A),
      Ideal.mul_mem_right _ _ hxm, ?_⟩⟩
    · intro h
      rw [h, mul_zero] at hp
      exact (mul_ne_zero (pow_ne_zero _ hϖ0) huv0) hp.symm
    · show ((inclA K ϖ ^ E₀ : A) : AlgebraicClosure ℚ) = _
      rw [SubmonoidClass.coe_pow, coe_inclA]
      show (ϖ : AlgebraicClosure ℚ) ^ E₀
        = V'.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))) * (V'.evalAt (c.x : ↥(modularFunctionFieldBar (N * q))) * (((huu.unit⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ))
      linear_combination (-((((huu.unit⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ))) * hp
        + (-((ϖ : AlgebraicClosure ℚ) ^ E₀)) * hwuF

  have hφinj : ∀ v₁ v₂ : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr v₁ = frobOnPlacesGeomLevel k N data hKr v₂ → v₁ = v₂ := by
    intro v₁ v₂ h
    rw [← arithFrobC_smul_eq_frobOnPlacesGeomLevel, ← arithFrobC_smul_eq_frobOnPlacesGeomLevel] at h
    exact smul_left_cancel _ h
  have hφφ := frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P w hw
  have hstrict : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w → ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V' := by
    intro V' hV'
    refine ⟨fun h => h.2 ?_, fun h => h.2 ?_⟩
    · rw [hV']
      exact hφφ
    · have h1 : frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V')
          = frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) := by
        rw [← h.1, hV', hφφ]
      rw [hφinj _ _ h1, hφφ]

  let An : Annulus A ↥(modularFunctionFieldBar (N * q)) :=
    { dom := {V' | P.reduceFst V' = w}
      param := (c.y : ↥(modularFunctionFieldBar (N * q)))
      modulus := inclA K ϖ ^ E₀
      modulus_mem := hmodmem
      mem_dom := fun V' hV' => ⟨isRational_place (N * q) V', hmem V' hV'⟩
      existsUnique_evalAt_eq := fun c₀ hc₀ hc₀0 hadm => hexu c₀ hc₀ hc₀0 hadm
      ord_param_sub := fun V' hV' => hunif V' hV'
      unit_principle := fun f hf hord => hunit f hf hord }
  have hspec := Annulus.opposite_pair_spec An hmod0 hy0
  refine ⟨An, An.opposite hmod0, ?_, hspec.1, hspec.2.1, ?_, rfl, hspec.2.2.2⟩
  · intro V'
    constructor
    · intro hV'
      exact ⟨hV', (hstrict V' hV').1, (hstrict V' hV').2⟩
    · intro h
      exact h.1
  · show ((inclA K ϖ ^ E₀ : A) : AlgebraicClosure ℚ) = (ϖ : AlgebraicClosure ℚ) ^ E₀
    rw [SubmonoidClass.coe_pow, coe_inclA]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel (solution)
