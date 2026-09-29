-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.ord_y_sub_algebraMap_evalAt_eq_one_of_ringEquiv_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9fcd5f5c-b20a-56dd-bb98-c337d2048b88

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const
import Theorems.Thm_IsLocalRing_exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_maximalIdeal_coeffSubring_eq_span_of_ringEquiv_apply_nodeConst_eq_const
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_setOf_reduceFst_eq_and_forall_mem_iff_evalAt_eq_zero_finite
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_fieldOver_nodeIntegersOver
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_V_powerSeries
import Theorems.Thm_IsLocalRing_eq_and_exists_isUnit_and_eq_mul_of_mul_eq_pow_of_span_pair_isPrime
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_toNat_ord_eq_length_localizedModule_quotient_of_forall_mem_iff_evalAt_eq_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_length_localizedModule_quotient_map_eq_of_mem_minimalPrimes
import Theorems.Thm_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_y_sub_algebraMap_evalAt_eq_one_of_ringEquiv_uvCrossingModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AdicCompletion.instIsLocalRingMaximalIdeal ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk"
p2m_attr_erase "simp" "WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
set_option autoImplicit false

universe u

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel~U_mul_V"
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace CrossingValueBranch

section BranchReduction

variable {W : Type*} [CommRing W] {π : W} {E : ℕ}

private def coeffRed (π : W) (E : ℕ) (hE : 1 ≤ E) : W ⧸ Ideal.span {π ^ E} →+* W ⧸ Ideal.span {π} :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self π (Nat.one_le_iff_ne_zero.mp hE)))

private theorem coeffRed_mk (hE : 1 ≤ E) (a : W) :
    coeffRed π E hE (Ideal.Quotient.mk (Ideal.span {π ^ E}) a) = Ideal.Quotient.mk (Ideal.span {π}) a :=
  Ideal.Quotient.factor_mk _ a

private noncomputable def branchRed (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E})) :
    UVCrossingModel W (π ^ E) →+* PowerSeries (W ⧸ Ideal.span {π}) :=
  (PowerSeries.map (coeffRed π E hE)).comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {T})))

private theorem branchRed_apply (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (r : UVCrossingModel W (π ^ E)) :
    branchRed hE T e r = PowerSeries.map (coeffRed π E hE) (e (Ideal.Quotient.mk (Ideal.span {T}) r)) :=
  rfl

private theorem branchRed_self (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E})) :
    branchRed hE T e T = 0 := by
  rw [branchRed_apply, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self T), map_zero, map_zero]

private theorem branchRed_const (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (heC : ∀ w : W, e (Ideal.Quotient.mk _ (const (π ^ E) w))
      = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) w))
    (w : W) :
    branchRed hE T e (const (π ^ E) w) = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) := by
  rw [branchRed_apply, heC, PowerSeries.map_C, coeffRed_mk]

private theorem branchRed_eq_X (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    {S : UVCrossingModel W (π ^ E)} (heS : e (Ideal.Quotient.mk _ S) = PowerSeries.X) :
    branchRed hE T e S = PowerSeries.X := by
  rw [branchRed_apply, heS, PowerSeries.map_X]

private theorem branchRed_eq_zero_iff (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (heC : ∀ w : W, e (Ideal.Quotient.mk _ (const (π ^ E) w))
      = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) w))
    (r : UVCrossingModel W (π ^ E)) :
    branchRed hE T e r = 0 ↔ r ∈ Ideal.span {const (π ^ E) π, T} := by
  constructor
  · intro hr
    rw [branchRed_apply] at hr

    have hcoef : ∀ n, ∃ b : W, PowerSeries.coeff n (e (Ideal.Quotient.mk (Ideal.span {T}) r))
        = Ideal.Quotient.mk (Ideal.span {π ^ E}) (π * b) := by
      intro n
      have hn := congrArg (PowerSeries.coeff n) hr
      rw [PowerSeries.coeff_map, map_zero] at hn
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
        (PowerSeries.coeff n (e (Ideal.Quotient.mk (Ideal.span {T}) r)))
      rw [← ha, coeffRed_mk] at hn
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hn)
      exact ⟨b, by rw [← ha, ← hb, mul_comm]⟩
    choose b hb using hcoef
    have hg : e (Ideal.Quotient.mk (Ideal.span {T}) r)
        = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) π)
          * PowerSeries.mk fun n => Ideal.Quotient.mk (Ideal.span {π ^ E}) (b n) := by
      ext n
      simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← map_mul, hb n]

    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
      ((e.symm) (PowerSeries.mk fun n => Ideal.Quotient.mk (Ideal.span {π ^ E}) (b n)))
    have hr' : Ideal.Quotient.mk (Ideal.span {T}) r = Ideal.Quotient.mk (Ideal.span {T}) (const (π ^ E) π * s) := by
      apply e.injective
      rw [map_mul (Ideal.Quotient.mk (Ideal.span {T})), map_mul e, heC π, hs, RingEquiv.apply_symm_apply, hg]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hr')
    exact Ideal.mem_span_pair.mpr ⟨s, t, by linear_combination ht⟩
  · intro hr
    obtain ⟨a, c, hac⟩ := Ideal.mem_span_pair.mp hr
    rw [← hac, map_add, map_mul, map_mul, branchRed_self, branchRed_const hE T e heC, mul_zero, add_zero,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), map_zero, mul_zero]

private theorem isPrime_span_const_and_not_mem (hp : (Ideal.span {π}).IsPrime) (hE : 1 ≤ E)
    (T S : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (heS : e (Ideal.Quotient.mk _ S) = PowerSeries.X)
    (heC : ∀ w : W, e (Ideal.Quotient.mk _ (const (π ^ E) w))
      = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) w)) :
    (Ideal.span {const (π ^ E) π, T}).IsPrime ∧ S ∉ Ideal.span {const (π ^ E) π, T} := by
  haveI := hp
  haveI : IsDomain (W ⧸ Ideal.span {π}) := Ideal.Quotient.isDomain _
  have hker : RingHom.ker (branchRed hE T e) = Ideal.span {const (π ^ E) π, T} := by
    ext r
    rw [RingHom.mem_ker]
    exact branchRed_eq_zero_iff hE T e heC r
  refine ⟨?_, fun hS => ?_⟩
  · rw [← hker]
    exact RingHom.ker_isPrime _
  have h0 := (branchRed_eq_zero_iff hE T e heC S).mpr hS
  rw [branchRed_eq_X hE T e heS] at h0
  exact PowerSeries.X_ne_zero h0

private theorem coeff_natTrailingDegree_eval₂_X_mul {S : Type*} [CommRing S] (p : Polynomial S)
    (u : PowerSeries S) :
    PowerSeries.coeff p.natTrailingDegree (p.eval₂ (PowerSeries.C) (PowerSeries.X * u))
      = p.trailingCoeff * PowerSeries.constantCoeff u ^ p.natTrailingDegree := by
  rw [Polynomial.trailingCoeff, Polynomial.eval₂_eq_sum_range, map_sum,
    Finset.sum_eq_single p.natTrailingDegree]
  · rw [PowerSeries.coeff_C_mul, mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
  · intro i _ hne
    rw [PowerSeries.coeff_C_mul, mul_pow, PowerSeries.coeff_X_pow_mul']
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt, zero_mul]
    · rw [if_neg (not_le.mpr hgt), mul_zero]
  · intro hnot
    rw [Finset.mem_range, not_lt] at hnot
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hnot), map_zero, zero_mul, map_zero]

end BranchReduction

private theorem isPrime_span_const_U {W : Type*} [CommRing W] {π : W} (hp : (Ideal.span {π}).IsPrime)
    (E : ℕ) (hE : 1 ≤ E) :
    (Ideal.span {const (π ^ E) π, U (π ^ E)}).IsPrime ∧ V (π ^ E) ∉ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
  obtain ⟨e, heV, -, heC⟩ := exists_ringEquiv_quotient_span_U_powerSeries (π ^ E)
  exact isPrime_span_const_and_not_mem hp hE (U (π ^ E)) (V (π ^ E)) e heV heC

private theorem isPrime_span_const_V {W : Type*} [CommRing W] {π : W} (hp : (Ideal.span {π}).IsPrime)
    (E : ℕ) (hE : 1 ≤ E) :
    (Ideal.span {const (π ^ E) π, V (π ^ E)}).IsPrime ∧ U (π ^ E) ∉ Ideal.span {const (π ^ E) π, V (π ^ E)} := by
  obtain ⟨e, heU, -, heC⟩ := exists_ringEquiv_quotient_span_V_powerSeries (π ^ E)
  exact isPrime_span_const_and_not_mem hp hE (V (π ^ E)) (U (π ^ E)) e heU heC

private theorem eval_map_constHom_ne_zero {W : Type*} [CommRing W] {π : W} (hp : (Ideal.span {π}).IsPrime)
    (E : ℕ) (hE : 1 ≤ E) (g : Polynomial W) (hg : ∃ i, g.coeff i ∉ Ideal.span {π})
    (α : UVCrossingModel W (π ^ E)) (hα : IsUnit α) :
    (g.map (constHom (π ^ E))).eval (V (π ^ E) * α) ≠ 0 := by
  haveI := hp
  haveI : IsDomain (W ⧸ Ideal.span {π}) := Ideal.Quotient.isDomain _
  obtain ⟨e, heV, -, heC⟩ := exists_ringEquiv_quotient_span_U_powerSeries (π ^ E)
  intro h0
  have h1 := congrArg (branchRed hE (U (π ^ E)) e) h0
  rw [map_zero, Polynomial.eval_map, Polynomial.hom_eval₂, map_mul, branchRed_eq_X hE _ e heV] at h1
  have hcomp : (branchRed hE (U (π ^ E)) e).comp (constHom (π ^ E))
      = (PowerSeries.C (R := W ⧸ Ideal.span {π})).comp (Ideal.Quotient.mk (Ideal.span {π})) :=
    RingHom.ext fun w => by
      rw [RingHom.comp_apply, RingHom.comp_apply, constHom_apply, branchRed_const hE _ e heC]
  rw [hcomp, ← Polynomial.eval₂_map] at h1
  have hne : g.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := by
    obtain ⟨i, hi⟩ := hg
    intro hz
    apply hi
    have hzi := congrArg (fun p => Polynomial.coeff p i) hz
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hzi
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzi
  have hu : IsUnit (PowerSeries.constantCoeff (branchRed hE (U (π ^ E)) e α)) :=
    PowerSeries.isUnit_constantCoeff _ (hα.map _)
  have h2 := congrArg (PowerSeries.coeff (g.map (Ideal.Quotient.mk (Ideal.span {π}))).natTrailingDegree) h1
  rw [coeff_natTrailingDegree_eval₂_X_mul, map_zero] at h2
  exact mul_ne_zero (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hne) (pow_ne_zero _ hu.ne_zero) h2

private theorem map_map_span_pair_eq {S T R' : Type*} [CommRing S] [CommRing T] [CommRing R'] (f : S →+* T)
    (ι : T ≃+* R') {a b : S} {p u : R'} (w : R') (hw : IsUnit w) (ha : ι (f a) = p) (hb : ι (f b) = u * w) :
    Ideal.map ι (Ideal.map f (Ideal.span {a, b})) = Ideal.span {p, u} := by
  rw [Ideal.map_span f, Set.image_pair, Ideal.map_span ι, Set.image_pair, ha, hb]
  obtain ⟨wu, rfl⟩ := hw
  have hp1 : p ∈ Ideal.span {p, u} := Ideal.subset_span (Set.mem_insert _ _)
  have hu1 : u ∈ Ideal.span {p, u} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hp2 : p ∈ Ideal.span {p, u * ↑wu} := Ideal.subset_span (Set.mem_insert _ _)
  have hu2 : u * ↑wu ∈ Ideal.span {p, u * ↑wu} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hu2' : u ∈ Ideal.span {p, u * ↑wu} := by
    have h := Ideal.mul_mem_right (↑wu⁻¹ : R') _ hu2
    rwa [mul_assoc, Units.mul_inv, mul_one] at h
  apply le_antisymm
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hp1, Ideal.mul_mem_right _ _ hu1⟩
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hp2, hu2'⟩

private theorem maximalIdeal_eq_span_triple {B : Type*} [CommRing B] [IsLocalRing B] {ϖ x y g' h' : B}
    (hm : maximalIdeal B = Ideal.span {ϖ, g', h'}) (hg : Ideal.span {ϖ, g'} = Ideal.span {ϖ, x})
    (hh : Ideal.span {ϖ, h'} = Ideal.span {ϖ, y}) :
    maximalIdeal B = Ideal.span {ϖ, x, y} := by
  have hsplit : ∀ a b : B, Ideal.span {ϖ, a, b} = Ideal.span {ϖ, a} ⊔ Ideal.span {ϖ, b} := by
    intro a b
    rw [← Ideal.span_union]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  rw [hm, hsplit, hsplit, hg, hh]

private theorem map_eval_map {O B R' : Type*} [CommSemiring O] [CommSemiring B] [CommSemiring R'] (κ : O →+* B)
    (θ : B →+* R') (φ : O →+* R') (h : θ.comp κ = φ) (g : Polynomial O) (y : B) :
    θ ((g.map κ).eval y) = (g.map φ).eval (θ y) := by
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂, h]

private theorem isDiscreteValuationRing_coeffSubring {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K) := by
  refine (NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K).resolve_left ?_
  intro hEq
  have hq : q.Prime := Fact.out
  have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hqK : ((q : AlgebraicClosure ℚ))⁻¹ ∈ NodeLocalized.coeffSubring A K := by
    rw [hEq, Subalgebra.mem_toSubring, IntermediateField.mem_toSubalgebra]
    exact inv_mem (natCast_mem K q)
  have hqA : ((q : AlgebraicClosure ℚ))⁻¹ ∈ A := hqK.1
  have hunit : IsUnit (q : ↥A) := by
    refine IsUnit.of_mul_eq_one ⟨_, hqA⟩ (Subtype.ext ?_)
    rw [MulMemClass.coe_mul, OneMemClass.coe_one, SubringClass.coe_natCast]
    exact mul_inv_cancel₀ hq0
  have h1 := hunit.map red
  rw [map_natCast, CharP.cast_eq_zero k q] at h1
  exact not_isUnit_zero h1

private theorem ne_zero_of_redRestrict_eq_zero_iff {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    ϖ ≠ 0 := by
  intro hϖz
  have hq : q.Prime := Fact.out
  have h1 : NodeLocalized.redRestrict red K (q : ↥(NodeLocalized.coeffSubring A K)) = 0 := by
    rw [map_natCast, CharP.cast_eq_zero]
  obtain ⟨d', hd'⟩ := (hϖ _).mp h1
  rw [hϖz, zero_mul] at hd'
  have h2 : ((q : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) = 0 := by rw [hd']; rfl
  rw [SubringClass.coe_natCast, Nat.cast_eq_zero] at h2
  exact hq.ne_zero h2

private theorem evalAt_sub_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {y : F} (hy : y ∈ v.toValuationSubring) (a : K) :
    v.evalAt (y - algebraMap K F a) = v.evalAt y - a := by
  have ha : algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem' a
  have hsub : y - algebraMap K F a ∈ v.toValuationSubring := sub_mem hy ha
  apply v.algebraMap_residueField_injective
  have h1 : (⟨y - algebraMap K F a, hsub⟩ : v.toValuationSubring) =
      ⟨y, hy⟩ - algebraMap K v.toValuationSubring a := rfl
  rw [v.algebraMap_evalAt hv hsub, map_sub, v.algebraMap_evalAt hv hy, h1, map_sub, v.residue_algebraMap]

private theorem ord_eq_zero_of_evalAt_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {z : F} (hz : z ∈ v.toValuationSubring) (h : v.evalAt z ≠ 0) : v.ord z = 0 := by
  have hres : IsLocalRing.residue _ (⟨z, hz⟩ : v.toValuationSubring) ≠ 0 := by
    rw [← v.algebraMap_evalAt hv hz]
    exact (map_ne_zero_iff _ v.algebraMap_residueField_injective).mpr h
  have hunit : IsUnit (⟨z, hz⟩ : v.toValuationSubring) := by
    by_contra hnu
    exact hres ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  have h0 := v.ord_coe_unit hunit.unit
  rwa [IsUnit.unit_spec] at h0

private noncomputable def evalRingHom {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) : v.toValuationSubring →+* K where
  toFun z := v.evalAt (z : F)
  map_one' := by
    show v.evalAt ((1 : v.toValuationSubring) : F) = 1
    rw [OneMemClass.coe_one, v.evalAt_one]
  map_mul' z z' := by
    show v.evalAt ((z * z' : v.toValuationSubring) : F) = v.evalAt (z : F) * v.evalAt (z' : F)
    apply v.algebraMap_residueField_injective
    rw [map_mul, MulMemClass.coe_mul, v.algebraMap_evalAt hv (mul_mem z.2 z'.2), v.algebraMap_evalAt hv z.2,
      v.algebraMap_evalAt hv z'.2, ← map_mul]
    rfl
  map_zero' := by
    show v.evalAt ((0 : v.toValuationSubring) : F) = 0
    rw [ZeroMemClass.coe_zero, ← map_zero (algebraMap K F), v.evalAt_algebraMap_eq]
  map_add' z z' := by
    show v.evalAt ((z + z' : v.toValuationSubring) : F) = v.evalAt (z : F) + v.evalAt (z' : F)
    apply v.algebraMap_residueField_injective
    rw [map_add, AddMemClass.coe_add, v.algebraMap_evalAt hv (add_mem z.2 z'.2), v.algebraMap_evalAt hv z.2,
      v.algebraMap_evalAt hv z'.2, ← map_add]
    rfl

private theorem evalAt_eval_map {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {y : F} (hy : y ∈ v.toValuationSubring) (p : Polynomial K) :
    v.evalAt ((p.map (algebraMap K F)).eval y) = p.eval (v.evalAt y) := by
  have halg : algebraMap K F = v.toValuationSubring.subtype.comp (algebraMap K v.toValuationSubring) :=
    RingHom.ext fun a => (v.coe_algebraMap a).symm
  have h1 : (p.map (algebraMap K F)).eval y =
      (((p.map (algebraMap K v.toValuationSubring)).eval ⟨y, hy⟩ : v.toValuationSubring) : F) := by
    rw [Polynomial.eval_map, Polynomial.eval_map, halg]
    exact (Polynomial.hom_eval₂ p _ v.toValuationSubring.subtype ⟨y, hy⟩).symm
  have h2 : v.evalAt ((((p.map (algebraMap K v.toValuationSubring)).eval ⟨y, hy⟩ : v.toValuationSubring) : F)) =
      evalRingHom v hv ((p.map (algebraMap K v.toValuationSubring)).eval ⟨y, hy⟩) := rfl
  have hcomp : (evalRingHom v hv).comp (algebraMap K v.toValuationSubring) = RingHom.id K :=
    RingHom.ext fun a => by
      show v.evalAt ((algebraMap K v.toValuationSubring a : v.toValuationSubring) : F) = a
      rw [v.coe_algebraMap, v.evalAt_algebraMap_eq]
  have h3 : evalRingHom v hv ⟨y, hy⟩ = v.evalAt y := rfl
  rw [h1, h2, Polynomial.eval_map, Polynomial.hom_eval₂, hcomp, h3, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]

private theorem ord_multiset_prod {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (s : Multiset F) (hs : ∀ z ∈ s, z ≠ 0) : v.ord s.prod = (s.map v.ord).sum := by
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.prod_zero, Multiset.map_zero, Multiset.sum_zero, v.ord_one]
  | cons z s ih =>
    have hz : z ≠ 0 := hs z (Multiset.mem_cons_self z s)
    have hs' : ∀ t ∈ s, t ≠ 0 := fun t ht => hs t (Multiset.mem_cons_of_mem ht)
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => hs' 0 h0 rfl
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, v.ord_mul hz hprod, ih hs']

private theorem ord_eval_map_eq_ord_sub {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {y : F} (hy : y ∈ v.toValuationSubring)
    (g : Polynomial K) (hsep : g.Separable) (hne : (g.map (algebraMap K F)).eval y ≠ 0)
    (hroot : g.eval (v.evalAt y) = 0) :
    v.ord ((g.map (algebraMap K F)).eval y) = v.ord (y - algebraMap K F (v.evalAt y)) := by
  classical
  have hg0 : g ≠ 0 := fun h => hne (by rw [h, Polynomial.map_zero, Polynomial.eval_zero])
  have hlead : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
  have hprod : g = Polynomial.C g.leadingCoeff * (g.roots.map fun a => Polynomial.X - Polynomial.C a).prod :=
    (IsAlgClosed.splits g).eq_prod_roots
  have hfac : (g.map (algebraMap K F)).eval y =
      algebraMap K F g.leadingCoeff * (g.roots.map fun a => y - algebraMap K F a).prod := by
    conv_lhs => rw [hprod]
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.map_multiset_prod,
      Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => ?_)
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
  have hmem : v.evalAt y ∈ g.roots := (Polynomial.mem_roots hg0).mpr hroot
  have hnodup : g.roots.Nodup := Polynomial.nodup_roots hsep
  have hfz : ∀ a ∈ g.roots, y - algebraMap K F a ≠ 0 := fun a ha h0 => by
    have hya : y = algebraMap K F a := sub_eq_zero.mp h0
    apply hne
    rw [hya, Polynomial.eval_map, Polynomial.eval₂_hom, Polynomial.IsRoot.def.mp ((Polynomial.mem_roots hg0).mp ha),
      map_zero]
  have hfz' : ∀ z ∈ g.roots.map (fun a => y - algebraMap K F a), z ≠ 0 := fun z hz => by
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hz
    exact hfz a ha
  have hprod0 : (g.roots.map fun a => y - algebraMap K F a).prod ≠ 0 :=
    Multiset.prod_ne_zero fun h0 => hfz' 0 h0 rfl
  have hconst0 : algebraMap K F g.leadingCoeff ≠ 0 := (map_ne_zero _).mpr hlead
  have hconst : v.ord (algebraMap K F g.leadingCoeff) = 0 :=
    ord_eq_zero_of_evalAt_ne_zero v hv (v.algebraMap_mem' _) (by rw [v.evalAt_algebraMap_eq]; exact hlead)
  have hsum : ((g.roots.map fun a => y - algebraMap K F a).map v.ord).sum =
      v.ord (y - algebraMap K F (v.evalAt y)) := by
    rw [Multiset.map_map, ← Multiset.cons_erase hmem, Multiset.map_cons, Multiset.sum_cons, Function.comp_apply]
    have hrest : ((g.roots.erase (v.evalAt y)).map (v.ord ∘ fun a => y - algebraMap K F a)) =
        (g.roots.erase (v.evalAt y)).map fun _ => (0 : ℤ) := by
      refine Multiset.map_congr rfl fun a ha => ?_
      have hne' : a ≠ v.evalAt y := ((hnodup.mem_erase_iff).mp ha).1
      exact ord_eq_zero_of_evalAt_ne_zero v hv (sub_mem hy (v.algebraMap_mem' a))
        (by rw [evalAt_sub_algebraMap v hv hy]; exact sub_ne_zero.mpr (Ne.symm hne'))
    rw [hrest, Multiset.map_const', Multiset.sum_replicate, smul_zero, add_zero]
  rw [hfac, v.ord_mul hconst0 hprod0, hconst, zero_add, ord_multiset_prod v _ hfz', hsum]

private theorem exists_mem_forall_mul_inv_mem {L : Type*} [Field L] (A : ValuationSubring L) (s : Finset L)
    (hs : ∀ b ∈ s, b ≠ 0) (hne : s.Nonempty) : ∃ a ∈ s, ∀ b ∈ s, b * a⁻¹ ∈ A := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hne Finset.not_nonempty_empty
  | @insert b t hbt ih =>
    have hb0 : b ≠ 0 := hs b (Finset.mem_insert_self b t)
    have hbb : b * b⁻¹ ∈ A := by rw [mul_inv_cancel₀ hb0]; exact one_mem A
    by_cases ht : t.Nonempty
    · obtain ⟨a, hat, ha⟩ := ih (fun c hc => hs c (Finset.mem_insert_of_mem hc)) ht
      have ha0 : a ≠ 0 := hs a (Finset.mem_insert_of_mem hat)
      by_cases hba : b * a⁻¹ ∈ A
      · refine ⟨a, Finset.mem_insert_of_mem hat, fun c hc => ?_⟩
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact hba
        · exact ha c hc
      · have hab : a * b⁻¹ ∈ A := by
          have h := A.mem_or_inv_mem (b * a⁻¹)
          rw [mul_inv_rev, inv_inv] at h
          exact h.resolve_left hba
        refine ⟨b, Finset.mem_insert_self b t, fun c hc => ?_⟩
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact hbb
        · have h1 : c * b⁻¹ = (c * a⁻¹) * (a * b⁻¹) := by rw [mul_assoc, inv_mul_cancel_left₀ ha0]
          rw [h1]
          exact mul_mem (ha c hc) hab
    · rw [Finset.not_nonempty_iff_eq_empty] at ht
      subst ht
      refine ⟨b, Finset.mem_insert_self b _, fun c hc => ?_⟩
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hbb
      · exact absurd hc (Finset.notMem_empty c)

private theorem exists_map_eq_C_mul_map (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : Polynomial K) :
    ∃ (D : ↥(NodeLocalized.coeffSubring A K)) (P : Polynomial ↥(NodeLocalized.coeffSubring A K)), D ≠ 0 ∧
      P.map (NodeLocalized.coeffSubring A K).subtype =
        Polynomial.C (D : AlgebraicClosure ℚ) * p.map (algebraMap K (AlgebraicClosure ℚ)) ∧
      (p.Monic → ∃ i, IsUnit (P.coeff i)) := by
  classical

  set s : Finset (AlgebraicClosure ℚ) :=
    insert 1 (p.support.image fun i => ((p.coeff i : K) : AlgebraicClosure ℚ)) with hs
  have hs0 : ∀ b ∈ s, b ≠ 0 := fun b hb => by
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact one_ne_zero
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
      rw [Ne, ZeroMemClass.coe_eq_zero]
      exact Polynomial.mem_support_iff.mp hi
  obtain ⟨a, has, ha⟩ := exists_mem_forall_mul_inv_mem A s hs0 ⟨1, Finset.mem_insert_self _ _⟩
  have ha0 : a ≠ 0 := hs0 a has

  have haK : a ∈ K := by
    rcases Finset.mem_insert.mp has with rfl | has'
    · exact one_mem K
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp has'
      exact (p.coeff i).2
  have hDA : a⁻¹ ∈ A := by simpa using ha 1 (Finset.mem_insert_self _ _)
  have hDmem : a⁻¹ ∈ NodeLocalized.coeffSubring A K := Subring.mem_inf.mpr ⟨hDA, (inv_mem haK : a⁻¹ ∈ K)⟩
  refine ⟨⟨a⁻¹, hDmem⟩, ?_⟩

  have hcoef : ∀ i, a⁻¹ * ((p.coeff i : K) : AlgebraicClosure ℚ) ∈ NodeLocalized.coeffSubring A K := fun i => by
    by_cases hi : p.coeff i = 0
    · rw [hi, ZeroMemClass.coe_zero, mul_zero]; exact zero_mem _
    · refine Subring.mem_inf.mpr ⟨?_, (mul_mem (inv_mem haK) (p.coeff i).2 : _ ∈ K)⟩
      rw [mul_comm]
      exact ha _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Polynomial.mem_support_iff.mpr hi, rfl⟩))
  have hlift : Polynomial.C (a⁻¹) * p.map (algebraMap K (AlgebraicClosure ℚ)) ∈
      Polynomial.lifts (NodeLocalized.coeffSubring A K).subtype := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
    exact ⟨⟨_, hcoef i⟩, rfl⟩
  obtain ⟨P, hP⟩ := (Polynomial.mem_lifts _).mp hlift
  refine ⟨P, fun h => ha0 (inv_eq_zero.mp (congrArg Subtype.val h)), hP, fun hmonic => ?_⟩

  have hPcoef : ∀ i, ((P.coeff i : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) =
      a⁻¹ * ((p.coeff i : K) : AlgebraicClosure ℚ) := fun i => by
    have h := congrArg (fun r => Polynomial.coeff r i) hP
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at h
    exact h
  rcases Finset.mem_insert.mp has with rfl | has'
  · refine ⟨p.natDegree, ?_⟩
    have h1 : P.coeff p.natDegree = 1 := Subtype.ext (by
      rw [hPcoef, Polynomial.coeff_natDegree, hmonic.leadingCoeff, OneMemClass.coe_one, OneMemClass.coe_one,
        inv_one, one_mul])
    rw [h1]; exact isUnit_one
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp has'
    refine ⟨i, ?_⟩
    have h1 : P.coeff i = 1 := Subtype.ext (by rw [hPcoef, hi, OneMemClass.coe_one, inv_mul_cancel₀ ha0])
    rw [h1]; exact isUnit_one

private theorem exists_polynomial_isUnit_coeff_bezout_eval_eq_zero (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) :
    ∃ (g a b : Polynomial ↥(NodeLocalized.coeffSubring A K)) (d : ↥(NodeLocalized.coeffSubring A K)), d ≠ 0 ∧
      (∃ i, IsUnit (g.coeff i)) ∧ a * g + b * Polynomial.derivative g = Polynomial.C d ∧
      (g.map (NodeLocalized.coeffSubring A K).subtype).eval x = 0 := by
  have hℚ : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have hint : IsIntegral K x := hℚ.isIntegral.tower_top
  have hμ0 : minpoly K x ≠ 0 := minpoly.ne_zero hint
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hsep : (minpoly K x).Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  obtain ⟨u, v, huv⟩ : ∃ u v : Polynomial K, u * minpoly K x + v * Polynomial.derivative (minpoly K x) = 1 := hsep
  obtain ⟨D₁, P, hD₁, hP, hunit⟩ := exists_map_eq_C_mul_map A K (minpoly K x)
  obtain ⟨D₂, Pu, hD₂, hPu, -⟩ := exists_map_eq_C_mul_map A K u
  obtain ⟨D₃, Pv, hD₃, hPv, -⟩ := exists_map_eq_C_mul_map A K v
  refine ⟨P, Polynomial.C D₃ * Pu, Polynomial.C D₂ * Pv, D₂ * D₃ * D₁, mul_ne_zero (mul_ne_zero hD₂ hD₃) hD₁,
    hunit (minpoly.monic hint), ?_, ?_⟩
  · apply Polynomial.map_injective (NodeLocalized.coeffSubring A K).subtype Subtype.val_injective
    have huv' := congrArg (Polynomial.map (algebraMap K (AlgebraicClosure ℚ))) huv
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      Polynomial.map_one] at huv'
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_C, ← Polynomial.derivative_map, hP, hPu, hPv, Polynomial.map_C,
      Polynomial.derivative_C_mul]
    simp only [Subring.coe_subtype, MulMemClass.coe_mul, Polynomial.C_mul]
    linear_combination (Polynomial.C (D₂ : AlgebraicClosure ℚ) * Polynomial.C (D₃ : AlgebraicClosure ℚ) *
      Polynomial.C (D₁ : AlgebraicClosure ℚ)) * huv'
  · rw [hP, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval,
      mul_zero]

section Furniture

variable {W : Type u} [CommRing W]

private def eulerWeight (n : Fin 2 →₀ ℕ) : W := (n 1 : W) - (n 0 : W)

private theorem eulerWeight_add (m n : Fin 2 →₀ ℕ) :
    (eulerWeight (m + n) : W) = eulerWeight m + eulerWeight n := by
  simp only [eulerWeight, Finsupp.add_apply, Nat.cast_add]
  ring

private noncomputable def eulerLin : MvPowerSeries (Fin 2) W →ₗ[W] MvPowerSeries (Fin 2) W where
  toFun f := fun n => eulerWeight n * MvPowerSeries.coeff n f
  map_add' f g := by
    funext n
    show eulerWeight n * MvPowerSeries.coeff n (f + g) = eulerWeight n * MvPowerSeries.coeff n f +
      eulerWeight n * MvPowerSeries.coeff n g
    rw [map_add, mul_add]
  map_smul' w f := by
    funext n
    show eulerWeight n * MvPowerSeries.coeff n (w • f) = w • (eulerWeight n * MvPowerSeries.coeff n f)
    rw [map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm]

private theorem coeff_eulerLin (n : Fin 2 →₀ ℕ) (f : MvPowerSeries (Fin 2) W) :
    MvPowerSeries.coeff n (eulerLin f) = eulerWeight n * MvPowerSeries.coeff n f := rfl

private noncomputable def euler : Derivation W (MvPowerSeries (Fin 2) W) (MvPowerSeries (Fin 2) W) :=
  Derivation.mk' eulerLin fun f g => by
    ext n
    rw [smul_eq_mul, smul_eq_mul, mul_comm g (eulerLin f), coeff_eulerLin, MvPowerSeries.coeff_mul, map_add,
      MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [coeff_eulerLin, coeff_eulerLin, ← hij, eulerWeight_add]
    ring

private theorem coeff_euler (n : Fin 2 →₀ ℕ) (f : MvPowerSeries (Fin 2) W) :
    MvPowerSeries.coeff n (euler f) = ((n 1 : W) - (n 0 : W)) * MvPowerSeries.coeff n f := rfl

private theorem constantCoeff_euler (f : MvPowerSeries (Fin 2) W) : MvPowerSeries.constantCoeff (euler f) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_euler, Finsupp.coe_zero, Pi.zero_apply,
    Pi.zero_apply, Nat.cast_zero, sub_zero, zero_mul]

private theorem euler_X_one : euler (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) = MvPowerSeries.X 1 := by
  ext n
  rw [coeff_euler, MvPowerSeries.coeff_X]
  split_ifs with h
  · rw [h, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide), Nat.cast_one, Nat.cast_zero, sub_zero,
      mul_one]
  · rw [mul_zero]

private theorem euler_X_zero : euler (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) = -MvPowerSeries.X 0 := by
  ext n
  rw [coeff_euler, MvPowerSeries.coeff_X, map_neg, MvPowerSeries.coeff_X]
  split_ifs with h
  · rw [h, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide), Nat.cast_one, Nat.cast_zero, zero_sub,
      mul_one]
  · rw [mul_zero, neg_zero]

private theorem euler_C (w : W) : euler (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) = 0 := by
  ext n
  rw [coeff_euler, MvPowerSeries.coeff_C, LinearMap.map_zero]
  split_ifs with h
  · rw [h, Finsupp.coe_zero, Pi.zero_apply, Pi.zero_apply, Nat.cast_zero, sub_zero, zero_mul]
  · rw [mul_zero]

private theorem euler_crossing (c : W) :
    euler ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C c) = 0 := by
  rw [map_sub, Derivation.leibniz, euler_X_one, euler_X_zero, euler_C, smul_eq_mul, smul_eq_mul]
  ring

private theorem derivation_mem_of_mem_sq {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (J : Ideal A) {x : A} (hx : x ∈ J ^ 2) : D x ∈ J := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) fun y z hy hz => ?_
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact J.add_mem (J.mul_mem_right _ ha) (J.mul_mem_right _ hb)
  · rw [map_add]
    exact J.add_mem hy hz

private theorem mul_aeval_notMem_sq_sup (c d : W) (p a b : Polynomial W)
    (hbez : a * p + b * Polynomial.derivative p = Polynomial.C d)
    (eu : (MvPowerSeries (Fin 2) W)ˣ) (Q : Ideal (MvPowerSeries (Fin 2) W)) [hQ : Q.IsPrime]
    (hr : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C c ∈ Q)
    (hc : (MvPowerSeries.C c : MvPowerSeries (Fin 2) W) ∉ Q) (hd : (MvPowerSeries.C d : MvPowerSeries (Fin 2) W) ∉ Q)
    (s : MvPowerSeries (Fin 2) W) (hs : s ∉ Q) :
    s * Polynomial.aeval (MvPowerSeries.X 1 * (eu : MvPowerSeries (Fin 2) W)) p ∉
      Q ^ 2 ⊔ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C c} := by
  set y : MvPowerSeries (Fin 2) W := MvPowerSeries.X 1 * (eu : MvPowerSeries (Fin 2) W) with hy
  set G : MvPowerSeries (Fin 2) W := Polynomial.aeval y p with hG
  intro hmem

  by_cases hGQ : G ∈ Q
  swap
  · refine hGQ ((hQ.mem_or_mem ?_).resolve_left hs)
    exact (sup_le (Ideal.pow_le_self two_ne_zero) ((Ideal.span_singleton_le_iff_mem _).mpr hr)) hmem

  have hθ : ∀ x ∈ Q ^ 2 ⊔ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
      MvPowerSeries.C c}, euler x ∈ Q := by
    intro x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    refine Q.add_mem (derivation_mem_of_mem_sq euler Q hx₁) ?_
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hx₂
    rw [Derivation.leibniz, euler_crossing, smul_zero, zero_add, smul_eq_mul]
    exact Q.mul_mem_right _ hr

  have hp' : Polynomial.aeval y (Polynomial.derivative p) ∉ Q := by
    intro h
    apply hd
    have hev := congrArg (Polynomial.aeval y) hbez
    rw [map_add, map_mul, map_mul, Polynomial.aeval_C, ← MvPowerSeries.c_eq_algebraMap] at hev
    rw [← hev]
    exact Q.add_mem (Q.mul_mem_left _ hGQ) (Q.mul_mem_left _ h)
  have hX : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ∉ Q := by
    intro h
    apply hc
    have : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
        ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C c) =
        MvPowerSeries.C c := by
      ring
    rw [← this]
    exact Q.sub_mem (Q.mul_mem_left _ h) hr
  have hu : (eu : MvPowerSeries (Fin 2) W) + euler eu ∉ Q := by
    intro h
    refine hQ.ne_top (Q.eq_top_of_isUnit_mem h ?_)
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_add, constantCoeff_euler, add_zero,
      ← MvPowerSeries.isUnit_iff_constantCoeff]
    exact Units.isUnit eu

  have hθG : euler G = Polynomial.aeval y (Polynomial.derivative p) * (MvPowerSeries.X 1 *
      ((eu : MvPowerSeries (Fin 2) W) + euler eu)) := by
    rw [hG, Derivation.map_aeval, smul_eq_mul, hy, Derivation.leibniz, euler_X_one, smul_eq_mul, smul_eq_mul]
    ring
  have hθsG : s * euler G ∈ Q := by
    have h := hθ _ hmem
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h
    exact (Submodule.add_mem_iff_left Q (Q.mul_mem_right _ hGQ)).mp h
  rcases hQ.mem_or_mem hθsG with h | h
  · exact hs h
  rw [hθG] at h
  rcases hQ.mem_or_mem h with h | h
  · exact hp' h
  rcases hQ.mem_or_mem h with h | h
  · exact hX h
  · exact hu h

private theorem U_mul_V (c : W) : U c * V c = const c c := by
  show mk c (MvPowerSeries.X 0) * mk c (MvPowerSeries.X 1) = mk c (MvPowerSeries.C c)
  rw [← map_mul]
  exact Ideal.Quotient.eq.mpr (Ideal.subset_span rfl)

private theorem eval_map_constHom_V_mul_mk (c : W) (p : Polynomial W) (f : MvPowerSeries (Fin 2) W) :
    (p.map (constHom c)).eval (V c * mk c f) = mk c (Polynomial.aeval (MvPowerSeries.X 1 * f) p) := by
  rw [Polynomial.eval_map, show V c * mk c f = mk c (MvPowerSeries.X 1 * f) from (map_mul (mk c) _ _).symm,
    show constHom c = (mk c).comp MvPowerSeries.C from rfl, ← Polynomial.hom_eval₂, Polynomial.aeval_def,
    MvPowerSeries.c_eq_algebraMap]

private theorem mul_eval_notMem_sq {c d : W} {p a b : Polynomial W}
    (hbez : a * p + b * Polynomial.derivative p = Polynomial.C d) (eu : (MvPowerSeries (Fin 2) W)ˣ)
    (Q : Ideal (UVCrossingModel W c)) [hQ : Q.IsPrime] (hc : const c c ∉ Q) (hd : const c d ∉ Q)
    {s : UVCrossingModel W c} (hs : s ∉ Q) :
    s * (p.map (constHom c)).eval (V c * mk c eu) ∉ Q ^ 2 := by
  intro h
  obtain ⟨s, rfl⟩ := mk_surjective c s
  rw [eval_map_constHom_V_mul_mk, ← map_mul, ← Ideal.map_comap_of_surjective _ (mk_surjective c) Q,
    ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ (mk_surjective c)] at h
  obtain ⟨j, hj, hjs⟩ := h
  refine mul_aeval_notMem_sq_sup c d p a b hbez eu (Q.comap (mk c)) ?_ hc hd s hs ?_
  · rw [Ideal.mem_comap, show mk c ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
      MvPowerSeries.C c) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)]
    exact (Q.comap (mk c)).zero_mem
  · rw [← sub_sub_cancel j (s * Polynomial.aeval (MvPowerSeries.X 1 * (eu : MvPowerSeries (Fin 2) W)) p)]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hj) (Submodule.mem_sup_right (Ideal.Quotient.eq.mp hjs))

private theorem isUnit_of_mul_sub_one_eq [IsLocalRing W] {c : W} (hc : c ∈ IsLocalRing.maximalIdeal W)
    {f g h : MvPowerSeries (Fin 2) W}
    (hfg : h * (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C c) = f * g - 1) : IsUnit f := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  have h0 := congrArg MvPowerSeries.constantCoeff hfg
  simp only [map_sub, map_mul, map_one, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, zero_mul,
    zero_sub, mul_neg] at h0
  have h1 : MvPowerSeries.constantCoeff f * MvPowerSeries.constantCoeff g =
      1 - c * MvPowerSeries.constantCoeff h := by
    linear_combination -h0
  exact isUnit_of_mul_isUnit_left (h1 ▸ IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hc)))

private theorem exists_unit_mk_eq [IsLocalRing W] {π : W} (hπ : ¬ IsUnit π) {E : ℕ} (hE : 1 ≤ E)
    {α : UVCrossingModel W (π ^ E)} (hα : IsUnit α) :
    ∃ eu : (MvPowerSeries (Fin 2) W)ˣ, mk (π ^ E) eu = α := by
  obtain ⟨f, rfl⟩ := mk_surjective (π ^ E) α
  obtain ⟨β, hβ⟩ := hα.exists_right_inv
  obtain ⟨g, rfl⟩ := mk_surjective (π ^ E) β
  have h0 : mk (π ^ E) (f * g - 1) = 0 := by rw [map_sub, map_mul, map_one, hβ, sub_self]
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hf : IsUnit f := isUnit_of_mul_sub_one_eq
    (Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal π).mpr hπ) E hE) hh
  exact ⟨hf.unit, by rw [IsUnit.unit_spec]⟩

private theorem not_isUnit_const [IsLocalRing W] {π : W} (hπ : ¬ IsUnit π) {E : ℕ} (hE : 1 ≤ E) :
    ¬ IsUnit (const (π ^ E) π) := by
  intro hu
  have hUV : IsUnit (U (π ^ E) * V (π ^ E)) := by
    rw [U_mul_V, ← constHom_apply, map_pow]
    exact hu.pow E
  have hU : IsUnit (U (π ^ E)) := isUnit_of_mul_isUnit_left hUV
  obtain ⟨β, hβ⟩ := hU.exists_right_inv
  obtain ⟨g, rfl⟩ := mk_surjective (π ^ E) β
  have h0 : mk (π ^ E) (MvPowerSeries.X 0 * g - 1) = 0 := by
    rw [map_sub, map_mul, map_one, show mk (π ^ E) (MvPowerSeries.X 0) = U (π ^ E) from rfl, hβ, sub_self]
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hX : IsUnit (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) := isUnit_of_mul_sub_one_eq
    (Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal π).mpr hπ) E hE) hh
  rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at hX
  exact not_isUnit_zero hX

private theorem height_eq_one_of_ne_bot_of_ne_maximalIdeal {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hdim : ringKrullDim R ≤ 2) (Q : Ideal R) [hQ : Q.IsPrime] (hQ0 : Q ≠ ⊥)
    (hQm : Q ≠ IsLocalRing.maximalIdeal R) : Q.height = 1 := by
  haveI : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hQ0)
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime
    (lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ.ne_top) hQm)
  rw [Ideal.height_bot, zero_add] at h1
  have h4 : ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) ≤ 2 := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact hdim
  have h4' : (IsLocalRing.maximalIdeal R).height ≤ 2 := WithBot.coe_le_coe.mp (by rwa [WithBot.coe_ofNat])
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) h4')
  rw [← hc] at h3 h4'
  have hb : Q.height ≠ ⊤ := by
    intro ht
    rw [ht, top_add] at h3
    exact ENat.coe_ne_top c (top_le_iff.mp h3)
  obtain ⟨b, hb'⟩ := ENat.ne_top_iff_exists.mp hb
  rw [← hb'] at h1 h3 ⊢
  norm_cast at h1 h3 h4' ⊢
  omega

private theorem length_eq_one_of_forall_mul_notMem_sq {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R)
    [hQ : Q.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime Q)] {G : R} (hGQ : G ∈ Q)
    (hsq : ∀ s ∉ Q, s * G ∉ Q ^ 2) :
    Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl (R ⧸ Ideal.span {G})) = 1 := by
  set L := Localization.AtPrime Q with hL
  have hm : IsLocalRing.maximalIdeal L = Q.map (algebraMap R L) := Localization.AtPrime.map_eq_maximalIdeal.symm
  set g : L := algebraMap R L G with hg
  have hgm : g ∈ IsLocalRing.maximalIdeal L := hm ▸ Ideal.mem_map_of_mem _ hGQ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible L
  have hmϖ : IsLocalRing.maximalIdeal L = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hmϖ ▸ hgm)

  have htu : IsUnit t := by
    by_contra htu
    obtain ⟨t', ht'⟩ := Ideal.mem_span_singleton'.mp (hmϖ ▸ (IsLocalRing.mem_maximalIdeal t).mpr htu)
    have hg2 : g ∈ IsLocalRing.maximalIdeal L ^ 2 := by
      rw [hmϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
      exact ⟨t', by rw [← ht, ← ht']; ring⟩
    rw [hm, ← Ideal.map_pow] at hg2
    obtain ⟨⟨j, s⟩, hjs⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl L).mp hg2
    rw [hg, ← map_mul] at hjs
    obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists Q.primeCompl L).mp hjs
    refine hsq (u * s) (fun h => (hQ.mem_or_mem h).elim u.2 s.2) ?_
    rw [show (u : R) * s * G = u * (G * s) by ring, hu]
    exact Ideal.mul_mem_left _ _ j.2
  have hspan : Ideal.span {g} = IsLocalRing.maximalIdeal L := by
    rw [hmϖ, ← ht, Ideal.span_singleton_mul_left_unit htu]

  set m₀ : LocalizedModule Q.primeCompl (R ⧸ Ideal.span {G}) :=
    LocalizedModule.mk (Ideal.Quotient.mk (Ideal.span {G}) 1) 1 with hm₀
  set φ : L →ₗ[L] LocalizedModule Q.primeCompl (R ⧸ Ideal.span {G}) := LinearMap.toSpanSingleton L _ m₀ with hφ
  have hφs : Function.Surjective φ := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
      refine ⟨Localization.mk r s, ?_⟩
      rw [hφ, LinearMap.toSpanSingleton_apply, hm₀, LocalizedModule.mk_smul_mk, mul_one, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, map_one, mul_one]
  have hker : LinearMap.ker φ = IsLocalRing.maximalIdeal L := by
    apply le_antisymm
    · apply IsLocalRing.le_maximalIdeal
      intro htop
      have h1 : φ 1 = 0 := LinearMap.mem_ker.mp (htop ▸ Submodule.mem_top)
      rw [hφ, LinearMap.toSpanSingleton_apply, one_smul, hm₀, ← LocalizedModule.zero_mk 1,
        LocalizedModule.mk_eq] at h1
      obtain ⟨u, hu⟩ := h1
      simp only [one_smul] at hu
      rw [Submonoid.smul_def, Submonoid.smul_def, smul_zero, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_one,
        mul_one, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hu
      obtain ⟨a, ha⟩ := hu
      exact u.2 (ha ▸ Q.mul_mem_left a hGQ)
    · have hG0 : Ideal.Quotient.mk (Ideal.span {G}) G = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self G)
      rw [← hspan, Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, hφ, LinearMap.toSpanSingleton_apply, hm₀,
        hg, ← Localization.mk_one_eq_algebraMap, LocalizedModule.mk_smul_mk, mul_one, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, map_one, mul_one, hG0, LocalizedModule.zero_mk]
  haveI : IsSimpleModule L (L ⧸ LinearMap.ker φ) := by
    rw [isSimpleModule_iff_isCoatom, hker]
    exact (IsLocalRing.maximalIdeal.isMaximal L).out
  rw [(φ.quotKerEquivOfSurjective hφs).symm.length_eq]
  exact Module.length_eq_one ..

end Furniture

private theorem length_localizedModule_quotient_eval_eq_one
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (α : UVCrossingModel W (π ^ E)) (hα : IsUnit α)
    (p a b : Polynomial W) (d : W) (hd : d ≠ 0)
    (hbez : a * p + b * Polynomial.derivative p = Polynomial.C d)
    (hG0 : (p.map (constHom (π ^ E))).eval (V (π ^ E) * α) ≠ 0)
    (Q : Ideal (UVCrossingModel W (π ^ E))) [Q.IsPrime] (hQπ : const (π ^ E) π ∉ Q)
    (hGQ : (p.map (constHom (π ^ E))).eval (V (π ^ E) * α) ∈ Q) :
    Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl
          (UVCrossingModel W (π ^ E) ⧸ Ideal.span {(p.map (constHom (π ^ E))).eval (V (π ^ E) * α)})) = 1 := by

  haveI : IsNoetherianRing (UVCrossingModel W (π ^ E)) := UVCrossingModel.isNoetherianRing (π ^ E)
  obtain ⟨hdom, hloc, hic⟩ := UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow π hπ E hE
  have hQ : Q.IsPrime := ‹Q.IsPrime›

  obtain ⟨eu, rfl⟩ := exists_unit_mk_eq hπ.not_isUnit hE hα

  have hcQ : const (π ^ E) (π ^ E) ∉ Q := by
    intro h
    rw [← constHom_apply, map_pow] at h
    exact hQπ (hQ.mem_of_pow_mem E h)
  have hdQ : const (π ^ E) d ∉ Q := by
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπ
    intro h
    rw [hv, ← constHom_apply, map_mul, map_pow] at h
    rcases hQ.mem_or_mem h with h | h
    · exact hQ.ne_top (Q.eq_top_of_isUnit_mem h ((Units.isUnit v).map _))
    · exact hQπ (hQ.mem_of_pow_mem n h)

  have hsq : ∀ s ∉ Q, s * (p.map (constHom (π ^ E))).eval (V (π ^ E) * mk (π ^ E) eu) ∉ Q ^ 2 :=
    fun s hs => mul_eval_notMem_sq hbez eu Q hcQ hdQ hs

  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact hG0 ((Submodule.mem_bot _).mp hGQ)
  have hQm : Q ≠ maximalIdeal (UVCrossingModel W (π ^ E)) := by
    rintro rfl
    exact hQπ ((IsLocalRing.mem_maximalIdeal _).mpr (not_isUnit_const hπ.not_isUnit hE))
  haveI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one Q
      (height_eq_one_of_ne_bot_of_ne_maximalIdeal (UVCrossingModel.ringKrullDim_le_two π hπ E hE) Q hQ0 hQm)
  exact length_eq_one_of_forall_mul_notMem_sq Q hGQ hsq

end CrossingValueBranch

set_option maxHeartbeats 6400000 in
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
    ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
      V'.ord ((↑c.y : ↥(modularFunctionFieldBar (N * q)))
          - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))
              (V'.evalAt (↑c.y : ↥(modularFunctionFieldBar (N * q))))) = 1 := by
  intro V' hV'
  have _ := hmodel
  classical

  haveI hdvr : IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K) :=
    CrossingValueBranch.isDiscreteValuationRing_coeffSubring red K
  have hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π := by rw [← hσπ, hconst]
  have hϖ0 : ϖ ≠ 0 := CrossingValueBranch.ne_zero_of_redRestrict_eq_zero_iff red K ϖ hϖ
  have hϖgen : maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ} :=
    maximalIdeal_coeffSubring_eq_span_of_ringEquiv_apply_nodeConst_eq_const R K w ϖ π hπ E hE ι hιϖ
  obtain ⟨τ, hτ, hτϖ⟩ :=
    exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const R K w ϖ hϖgen hres π hπ E hE ι hιϖ

  obtain ⟨hdomR, hlocR, -⟩ := isIntegrallyClosed_of_uniformizer_pow π hπ E hE
  haveI := hdomR
  haveI := hlocR
  have hpprime : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ.prime
  obtain ⟨hPU, hVnot⟩ := CrossingValueBranch.isPrime_span_const_U hpprime E hE
  obtain ⟨hPV, hUnot⟩ := CrossingValueBranch.isPrime_span_const_V hpprime E hE
  have hUV : U (π ^ E) * V (π ^ E) = const (π ^ E) π ^ E := by
    rw [← constHom_apply, ← map_pow]
    show mk (π ^ E) (MvPowerSeries.X 0) * mk (π ^ E) (MvPowerSeries.X 1) = mk (π ^ E) (MvPowerSeries.C (π ^ E))
    rw [← map_mul]
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton _))

  have hxnu : ¬ IsUnit c.x := by
    intro hxu
    have h := hxu.map ((R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w)))
    have h2 : ((R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))) c.x =
        R.nodeResidue₁ w ⟨c.x, c.x.2.1⟩ := rfl
    rw [h2, c.x_fst] at h
    exact not_isUnit_zero h
  have hE₀ : 1 ≤ E₀ := by
    by_contra h
    have h0 : E₀ = 0 := by omega
    rw [h0, pow_zero, one_mul] at hxy
    exact hxnu (isUnit_of_mul_isUnit_left (hxy ▸ hu))
  have hXY : ι (algebraMap _ _ c.x) * ι (algebraMap _ _ c.y) = const (π ^ E) π ^ E₀ * ι (algebraMap _ _ u) := by
    rw [← map_mul ι, ← map_mul (algebraMap _ _), hxy, map_mul, map_mul, map_pow, map_pow, hιϖ]
  have hX : ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ c.x) - γ * U (π ^ E) ∈ Ideal.span {const (π ^ E) π, V (π ^ E)} := by
    obtain ⟨γ, hγ, h⟩ := hres₂ c.x 1 c.nodeResidue₂_x_ne_zero (by rw [Nat.cast_one]; exact c.x_snd)
    exact ⟨γ, hγ, by simpa only [pow_one] using h⟩
  have hY : ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ c.y) - γ * V (π ^ E) ∈ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
    obtain ⟨γ, hγ, h⟩ := hres₁ c.y 1 c.nodeResidue₁_y_ne_zero (by rw [Nat.cast_one]; exact c.y_fst)
    exact ⟨γ, hγ, by simpa only [pow_one] using h⟩
  obtain ⟨hEE, αU, αV, hαU, hαV, hιx, hιy⟩ :=
    IsLocalRing.eq_and_exists_isUnit_and_eq_mul_of_mul_eq_pow_of_span_pair_isPrime
      hE hE₀ hUV hPU hPV hUnot hVnot ((hu.map _).map ι) hXY hX hY

  have hgU : Ideal.map ι (Ideal.map (algebraMap _ _) (Ideal.span {R.nodeConst K w ϖ, c.x})) =
      Ideal.span {const (π ^ E) π, U (π ^ E)} :=
    CrossingValueBranch.map_map_span_pair_eq _ ι αU hαU hιϖ hιx
  have hhV : Ideal.map ι (Ideal.map (algebraMap _ _) (Ideal.span {R.nodeConst K w ϖ, c.y})) =
      Ideal.span {const (π ^ E) π, V (π ^ E)} :=
    CrossingValueBranch.map_map_span_pair_eq _ ι αV hαV hιϖ hιy
  obtain ⟨g', h', -, -, -, hmax', -, -, -, -, hspan_g, hspan_h⟩ :=
    IsLocalRing.exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel π hπ E hE ι
      (R.nodeConst K w ϖ) c.x c.y hιϖ hgU hhV
  have hmax : maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y} :=
    CrossingValueBranch.maximalIdeal_eq_span_triple hmax' hspan_g hspan_h
  have hht := IsLocalRing.eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two ι (ringKrullDim_le_two π hπ E hE)
  have hfrac := exists_mul_eq_of_mem_fieldOver_nodeIntegersOver R hqN K w hw

  have hratV : V'.IsRational := isRational_place_modularFunctionFieldBar (N * q) V'
  have hyV : (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ V'.toValuationSubring :=
    R.mem_toValuationSubring_of_mem_nodeIntegers c.y.2.1 hV'
  let inclV : ↥(R.nodeIntegersOver K w) →+* ↥V'.toValuationSubring :=
    { toFun := fun g' => ⟨(g' : ↥(modularFunctionFieldBar (N * q))), R.mem_toValuationSubring_of_mem_nodeIntegers
        g'.2.1 hV'⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let 𝔮 : Ideal ↥(R.nodeIntegersOver K w) := (maximalIdeal ↥V'.toValuationSubring).comap inclV
  haveI h𝔮prime : 𝔮.IsPrime := Ideal.comap_isPrime inclV _
  have h𝔮V : ∀ g' : ↥(R.nodeIntegersOver K w),
      g' ∈ 𝔮 ↔ V'.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = 0 := fun g' => by
    have h1 : algebraMap (AlgebraicClosure ℚ) V'.ResidueField (V'.evalAt (g' : ↥(modularFunctionFieldBar (N * q)))) =
        IsLocalRing.residue _ (inclV g') :=
      V'.algebraMap_evalAt hratV (R.mem_toValuationSubring_of_mem_nodeIntegers g'.2.1 hV')
    rw [Ideal.mem_comap, ← IsLocalRing.residue_eq_zero_iff, ← h1,
      map_eq_zero_iff _ V'.algebraMap_residueField_injective]
  have h𝔮 : ∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ 𝔮 := fun o ho hmem => by
    have h := (h𝔮V _).mp hmem
    rw [R.coe_nodeConst, V'.evalAt_algebraMap_eq] at h
    exact ho (Subtype.ext h)
  have h𝔮m : 𝔮 ≠ maximalIdeal ↥(R.nodeIntegersOver K w) := fun h =>
    h𝔮 ϖ hϖ0 (by rw [h, hmax]; exact Ideal.subset_span (Set.mem_insert _ _))
  have hht𝔮 : ∀ 𝔭 : Ideal ↥(R.nodeIntegersOver K w), 𝔭.IsPrime → 𝔭 < 𝔮 → 𝔭 = ⊥ :=
    fun 𝔭 h𝔭 hlt => hht 𝔭 𝔮 h𝔭 h𝔮prime h𝔮m hlt

  obtain ⟨g, a, b, d, hd0, ⟨i₀, hgi₀⟩, hbez, hgy₀⟩ :=
    CrossingValueBranch.exists_polynomial_isUnit_coeff_bezout_eval_eq_zero A K
      (V'.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))))
  have hfcoe :
      (((g.map (R.nodeConst K w)).eval c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) =
      ((g.map (NodeLocalized.coeffSubring A K).subtype).map
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))).eval
          (c.y : ↥(modularFunctionFieldBar (N * q))) := by
    have hsub : (R.nodeIntegersOver K w).subtype.comp (R.nodeConst K w) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).comp
          (NodeLocalized.coeffSubring A K).subtype := RingHom.ext fun o => R.coe_nodeConst K w o
    rw [Polynomial.map_map, ← hsub, Polynomial.eval_map, Polynomial.eval_map]
    exact Polynomial.hom_eval₂ g (R.nodeConst K w) (R.nodeIntegersOver K w).subtype c.y
  have hfV : V'.evalAt ((((g.map (R.nodeConst K w)).eval c.y : ↥(R.nodeIntegersOver K w)) :
      ↥(modularFunctionFieldBar (N * q)))) = 0 := by
    rw [hfcoe, CrossingValueBranch.evalAt_eval_map V' hratV hyV, hgy₀]
  have hf𝔮 : (g.map (R.nodeConst K w)).eval c.y ∈ 𝔮 := (h𝔮V _).mpr hfV
  have hθo : ∀ o : ↥(NodeLocalized.coeffSubring A K), (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) (R.nodeConst K w o) =
      const (π ^ E) (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)) :=
    fun o => hτ o
  have hθ : (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))).comp (R.nodeConst K w) =
      (constHom (π ^ E)).comp (τ.toRingHom.comp
          (algebraMap ↥(NodeLocalized.coeffSubring A K)
            (AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K))
              ↥(NodeLocalized.coeffSubring A K)))) :=
    RingHom.ext fun o => hθo o
  have hθy : (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) c.y =
      V (π ^ E) * αV := hιy
  have hfF : (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))))
        ((g.map (R.nodeConst K w)).eval c.y) =
      (g.map ((constHom (π ^ E)).comp (τ.toRingHom.comp
          (algebraMap ↥(NodeLocalized.coeffSubring A K)
            (AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K))
              ↥(NodeLocalized.coeffSubring A K)))))).eval (V (π ^ E) * αV) :=
    (CrossingValueBranch.map_eval_map (R.nodeConst K w) _ _ hθ g c.y).trans (congrArg (fun t =>
      (g.map ((constHom (π ^ E)).comp (τ.toRingHom.comp
          (algebraMap ↥(NodeLocalized.coeffSubring A K)
            (AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K))
              ↥(NodeLocalized.coeffSubring A K)))))).eval t) hθy)
  have hF0 : (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))))
        ((g.map (R.nodeConst K w)).eval c.y) ≠ 0 := by
    rw [hfF, ← Polynomial.map_map]
    refine CrossingValueBranch.eval_map_constHom_ne_zero hpprime E hE _ ⟨i₀, ?_⟩ αV hαV
    rw [Polynomial.coeff_map]
    intro hmem
    exact hpprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (hgi₀.map _))
  have hf0 : (g.map (R.nodeConst K w)).eval c.y ≠ 0 := fun h0 => hF0 (by rw [h0, map_zero])
  have h𝔮0 : 𝔮 ≠ ⊥ := fun h => hf0 ((Ideal.mem_bot).mp (h ▸ hf𝔮))

  have hordf := toNat_ord_eq_length_localizedModule_quotient_of_forall_mem_iff_evalAt_eq_zero R K w hfrac V' hV' 𝔮
    h𝔮V hht𝔮 _ hf0

  have hSfin := setOf_reduceFst_eq_and_forall_mem_iff_evalAt_eq_zero_finite R K w 𝔮 h𝔮0
  have hS : ∀ V, V ∈ hSfin.toFinset ↔ (P.reduceFst V = w ∧
      ∀ g' : ↥(R.nodeIntegersOver K w), g' ∈ 𝔮 ↔ V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = 0) :=
    fun V => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hcard := card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero R K w c ϖ hϖ0 hmax hres hvalA hw
    π hπ E hE ι hιϖ αU hαU hιx hht hfrac hϖgen τ hτ hτϖ 𝔮 h𝔮 h𝔮0 hqN hord hres₁ hres₂ hSfin.toFinset hS
  have hV'S : V' ∈ hSfin.toFinset := (hS V').mpr ⟨hV', h𝔮V⟩
  have hcard0 : (hSfin.toFinset.card : ℕ∞) ≠ 0 := by exact_mod_cast Finset.card_ne_zero_of_mem hV'S
  have hexQ : ∃ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)),
      Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
        (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes ∧
      const (π ^ E) π ∉ Q.asIdeal := by
    by_contra hno
    refine hcard0 ?_
    rw [hcard]
    refine finsum_eq_zero_of_forall_eq_zero fun Q => ?_
    rw [finsum_eq_if, if_neg fun hQ => hno ⟨Q, hQ⟩]
  obtain ⟨Q, hQ, hQπ⟩ := hexQ
  haveI := Q.isPrime

  have hlenQ := length_localizedModule_quotient_map_eq_of_mem_minimalPrimes R K w c ϖ hϖ0 hmax hres hvalA hw
    π hπ E hE ι hιϖ αU hαU hιx hht hfrac hϖgen τ hτ hτϖ 𝔮 h𝔮 h𝔮0 hqN hord hres₁ hres₂ Q hQ hQπ _ hf0
  have hGQ : (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))))
        ((g.map (R.nodeConst K w)).eval c.y) ∈ Q.asIdeal :=
    hQ.1.2 (Ideal.mem_map_of_mem _ hf𝔮)
  obtain ⟨n, ud, hud⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ hϖ0 hϖgen)
  have hτd : τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ d) ≠ 0 := by
    rw [hud, map_mul, map_mul, map_pow, map_pow, hτϖ]
    exact mul_ne_zero ((ud.isUnit.map (algebraMap ↥(NodeLocalized.coeffSubring A K) _)).map τ).ne_zero
      (pow_ne_zero _ hπ.ne_zero)
  have hbezW := congrArg (Polynomial.map (τ.toRingHom.comp (algebraMap ↥(NodeLocalized.coeffSubring A K)
      (AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K))))) hbez
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, Polynomial.map_C]
    at hbezW
  have hlen1 := CrossingValueBranch.length_localizedModule_quotient_eval_eq_one π hπ E hE αV hαV _ _ _ _ hτd hbezW
    (by rw [Polynomial.map_map, ← hfF]; exact hF0) Q.asIdeal hQπ (by rw [Polynomial.map_map, ← hfF]; exact hGQ)
  have hlen1' : Module.length (Localization.AtPrime Q.asIdeal) (LocalizedModule Q.asIdeal.primeCompl
      (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥(R.nodeIntegersOver K w) _
        ((g.map (R.nodeConst K w)).eval c.y))})) = 1 := by
    rw [Polynomial.map_map, ← hfF] at hlen1
    exact hlen1

  have hordfy : V'.ord ((((g.map (R.nodeConst K w)).eval c.y : ↥(R.nodeIntegersOver K w)) :
      ↥(modularFunctionFieldBar (N * q)))) =
      V'.ord ((c.y : ↥(modularFunctionFieldBar (N * q))) -
        algebraMap _ _ (V'.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))))) := by
    have hbezℚ := congrArg (Polynomial.map (NodeLocalized.coeffSubring A K).subtype) hbez
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, Polynomial.map_C]
      at hbezℚ
    have hsep : (g.map (NodeLocalized.coeffSubring A K).subtype).Separable := by
      have hd' : ((NodeLocalized.coeffSubring A K).subtype d) ≠ 0 := fun h => hd0 (Subtype.ext h)
      have h1 : Polynomial.C ((NodeLocalized.coeffSubring A K).subtype d)⁻¹ *
            a.map (NodeLocalized.coeffSubring A K).subtype * g.map (NodeLocalized.coeffSubring A K).subtype +
          Polynomial.C ((NodeLocalized.coeffSubring A K).subtype d)⁻¹ *
            b.map (NodeLocalized.coeffSubring A K).subtype *
              Polynomial.derivative (g.map (NodeLocalized.coeffSubring A K).subtype) = 1 := by
        rw [mul_assoc, mul_assoc, ← mul_add, hbezℚ, ← Polynomial.C_mul, inv_mul_cancel₀ hd', Polynomial.C_1]
      exact ⟨_, _, h1⟩
    have hfne : ((g.map (NodeLocalized.coeffSubring A K).subtype).map
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))).eval
          (c.y : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
      rw [← hfcoe, Ne, ZeroMemClass.coe_eq_zero]; exact hf0
    rw [hfcoe]
    exact CrossingValueBranch.ord_eval_map_eq_ord_sub V' hratV hyV _ hsep hfne hgy₀
  have hordnn : 0 ≤ V'.ord ((((g.map (R.nodeConst K w)).eval c.y : ↥(R.nodeIntegersOver K w)) :
      ↥(modularFunctionFieldBar (N * q)))) :=
    R.ord_nonneg_of_mem_nodeIntegers ((g.map (R.nodeConst K w)).eval c.y).2.1 hV'
  rw [← hordfy]
  rw [← hlenQ, hlen1'] at hordf
  have h1 : (V'.ord ((((g.map (R.nodeConst K w)).eval c.y : ↥(R.nodeIntegersOver K w)) :
      ↥(modularFunctionFieldBar (N * q))))).toNat = 1 := by exact_mod_cast hordf
  omega

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_y_sub_algebraMap_evalAt_eq_one_of_ringEquiv_uvCrossingModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_y_sub_algebraMap_evalAt_eq_one_of_ringEquiv_uvCrossingModel (solution)
