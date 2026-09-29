-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a0b88e28-0de2-5afe-8011-a09830cc67b8

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ringHom_adicCompletion_coeffSubring_valuationInteger
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
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_prime_const_notMem_and_norm_sub_eq_eval_of_pow_eq_mul
import Theorems.Thm_IsLocalRing_eq_and_exists_isUnit_and_eq_mul_of_mul_eq_pow_of_span_pair_isPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel
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

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
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

private theorem eq_of_isPrime_of_le_of_ringKrullDim_le_two {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hdim : ringKrullDim R ≤ 2) {P Q : Ideal R} (hP : P.IsPrime) (hQ : Q.IsPrime) (hP0 : P ≠ ⊥) (hPQ : P ≤ Q)
    (hQm : Q ≠ IsLocalRing.maximalIdeal R) : P = Q := by
  by_contra hne
  haveI := hP
  haveI := hQ
  haveI : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hP0)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hPQ hne)
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
  rw [← hb'] at h2 h3
  have ha : P.height ≠ ⊤ := by
    intro ht
    rw [ht, top_add] at h2
    exact ENat.coe_ne_top b (top_le_iff.mp h2)
  obtain ⟨a, ha'⟩ := ENat.ne_top_iff_exists.mp ha
  rw [← ha'] at h1 h2
  norm_cast at h1 h2 h3 h4'
  omega

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

private theorem evalAt_algebraMap_sub {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) (a : K) {g : F} (hg : g ∈ v.toValuationSubring) :
    v.evalAt (algebraMap K F a - g) = a - v.evalAt g := by
  have ha : algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem' a
  have hsub : algebraMap K F a - g ∈ v.toValuationSubring := sub_mem ha hg
  apply v.algebraMap_residueField_injective
  have h1 : (⟨algebraMap K F a - g, hsub⟩ : v.toValuationSubring) =
      algebraMap K v.toValuationSubring a - ⟨g, hg⟩ := rfl
  rw [v.algebraMap_evalAt hv hsub, map_sub, v.algebraMap_evalAt hv hg, h1, map_sub, v.residue_algebraMap]

private noncomputable def coeC (A : ValuationSubring (AlgebraicClosure ℚ)) :
    AlgebraicClosure ℚ →+* (A.valuation).Completion :=
  (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).comp
    (WithVal.equiv A.valuation).symm.toRingHom

private theorem coeC_apply (A : ValuationSubring (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) :
    coeC A x = (x : (A.valuation).Completion) := rfl

private theorem coeC_injective (A : ValuationSubring (AlgebraicClosure ℚ)) : Function.Injective (coeC A) :=
  (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).injective.comp
    (WithVal.equiv A.valuation).symm.injective

private theorem exists_polynomial_coeff_isUnit_eval_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)] (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hϖgen : maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ}) (c₀ : A) :
    ∃ g : Polynomial ↥(NodeLocalized.coeffSubring A K), (∃ i, IsUnit (g.coeff i)) ∧
      (g.map (NodeLocalized.coeffSubring A K).subtype).eval (c₀ : AlgebraicClosure ℚ) = 0 := by
  have halg : IsAlgebraic ℤ (c₀ : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨p, hp0, hpc₀⟩ := halg
  have hp₁c₀ : Polynomial.aeval (c₀ : AlgebraicClosure ℚ) p.primPart = 0 := by
    rw [p.eq_C_content_mul_primPart, map_mul, Polynomial.aeval_C] at hpc₀
    refine (mul_eq_zero.mp hpc₀).resolve_left ?_
    rw [eq_intCast, Int.cast_eq_zero, Polynomial.content_eq_zero_iff]
    exact hp0
  have hprim : p.primPart.IsPrimitive := p.isPrimitive_primPart
  have hq : q.Prime := Fact.out
  have hcoef : ∃ i, ¬ (q : ℤ) ∣ p.primPart.coeff i := by
    by_contra h
    push Not at h
    have hu := hprim _ ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr h)
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
    exact hq.one_lt.ne' hu
  obtain ⟨i, hi⟩ := hcoef
  refine ⟨p.primPart.map (Int.castRingHom _), ⟨i, ?_⟩, ?_⟩
  · rw [Polynomial.coeff_map, eq_intCast]
    by_contra hnu
    have hmem : ((p.primPart.coeff i : ℤ) : ↥(NodeLocalized.coeffSubring A K)) ∈
        maximalIdeal ↥(NodeLocalized.coeffSubring A K) := (mem_maximalIdeal _).mpr hnu
    rw [hϖgen, Ideal.mem_span_singleton'] at hmem
    obtain ⟨d', hd'⟩ := hmem
    have h0 : NodeLocalized.redRestrict red K ((p.primPart.coeff i : ℤ) : ↥(NodeLocalized.coeffSubring A K)) = 0 :=
      (hϖ _).mpr ⟨d', by rw [← hd', mul_comm]⟩
    rw [map_intCast] at h0
    exact hi ((CharP.intCast_eq_zero_iff k q _).mp h0)
  · have hZ : (NodeLocalized.coeffSubring A K).subtype.comp (Int.castRingHom _) =
        algebraMap ℤ (AlgebraicClosure ℚ) := RingHom.ext_int _ _
    rw [Polynomial.map_map, hZ, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hp₁c₀

private theorem const_notMem_of_ne_zero {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    {π : W} (hπ : Irreducible π) (E : ℕ) {Q : Ideal (UVCrossingModel W (π ^ E))} (hQ : Q.IsPrime)
    (hπQ : const (π ^ E) π ∉ Q) {t : W} (ht : t ≠ 0) : const (π ^ E) t ∉ Q := by
  intro hmem
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hπ
  rw [hv, ← constHom_apply, map_mul, map_pow] at hmem
  rcases hQ.mem_or_mem hmem with h | h
  · exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h ((Units.isUnit v).map _))
  · rw [constHom_apply] at h
    exact hπQ (hQ.mem_of_pow_mem _ h)

private theorem mem_minimalPrimes_map_comap {B R' : Type*} [CommRing B] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (hdim : ringKrullDim R' ≤ 2) (θ : B →+* R') (Q : Ideal R') (hQ : Q.IsPrime)
    (hQm : Q ≠ maximalIdeal R') {f : B} (hf : f ∈ Ideal.comap θ Q) (hf0 : θ f ≠ 0) :
    Q ∈ (Ideal.map θ (Ideal.comap θ Q)).minimalPrimes := by
  refine ⟨⟨hQ, Ideal.map_comap_le⟩, ?_⟩
  rintro P' ⟨hP', hIP'⟩ hP'Q
  have hfP' : θ f ∈ P' := hIP' (Ideal.mem_map_of_mem _ hf)
  have hP'0 : P' ≠ ⊥ := fun h => hf0 ((Ideal.mem_bot).mp (h ▸ hfP'))
  exact le_of_eq (eq_of_isPrime_of_le_of_ringKrullDim_le_two hdim hP' hQ hP'0 hP'Q hQm).symm

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

set_option synthInstance.maxHeartbeats 800000 in
open Valued in

private theorem eq_zero_of_algebraMap_eq_zero {A : ValuationSubring (AlgebraicClosure ℚ)}
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (j : AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) →+*
      𝒪[(A.valuation).Completion])
    (hj : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ((j (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o) : 𝒪[(A.valuation).Completion]) :
          (A.valuation).Completion) = ((o : AlgebraicClosure ℚ) : (A.valuation).Completion))
    {o : ↥(NodeLocalized.coeffSubring A K)}
    (h : algebraMap ↥(NodeLocalized.coeffSubring A K)
      (AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K)) o = 0) :
    o = 0 := by
  have h2 := hj o
  rw [h, map_zero, ZeroMemClass.coe_zero, ← coeC_apply, eq_comm, map_eq_zero_iff _ (coeC_injective A),
    ZeroMemClass.coe_eq_zero] at h2
  exact h2

set_option synthInstance.maxHeartbeats 800000 in
open Valued in

private theorem exists_mem_and_evalAt_eq {A : ValuationSubring (AlgebraicClosure ℚ)}
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    {W : Type*} [CommRing W]
    (τ : AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) ≃+* W)
    (j : AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) →+*
      𝒪[(A.valuation).Completion])
    (hj : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ((j (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o) : 𝒪[(A.valuation).Completion]) :
          (A.valuation).Completion) = ((o : AlgebraicClosure ℚ) : (A.valuation).Completion))
    {M : ℕ} [NeZero M] (SQ : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M)))
    (y : ↥(modularFunctionFieldBar M)) (hy : ∀ V ∈ SQ, y ∈ V.toValuationSubring)
    (e : ↥(NodeLocalized.coeffSubring A K) → ↥(modularFunctionFieldBar M))
    (he : ∀ o, e o = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M) (o : AlgebraicClosure ℚ) - y)
    (χ : Polynomial W)
    (hprod : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      (((∏ V ∈ SQ, V.evalAt (e o)) : AlgebraicClosure ℚ) : (A.valuation).Completion) =
        ((j (τ.symm (χ.eval (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)))) :
          𝒪[(A.valuation).Completion]) : (A.valuation).Completion))
    (c₀ : AlgebraicClosure ℚ)
    (hχc₀ : χ.eval₂ ((𝒪[(A.valuation).Completion]).subtype.comp (j.comp τ.symm.toRingHom))
      (c₀ : (A.valuation).Completion) = 0) :
    ∃ V ∈ SQ, V.evalAt y = c₀ := by
  have hrat : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M), V.IsRational :=
    fun V => isRational_place_modularFunctionFieldBar M V
  set ψ : W →+* (A.valuation).Completion :=
    (𝒪[(A.valuation).Completion]).subtype.comp (j.comp τ.symm.toRingHom) with hψ
  have hψapp : ∀ w' : W, ψ w' = ((j (τ.symm w') : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) :=
    fun _ => rfl
  have hψo : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ψ (τ (algebraMap _ _ o)) = coeC A (o : AlgebraicClosure ℚ) := by
    intro o
    rw [hψapp, τ.symm_apply_apply, hj o, coeC_apply]
  have hRHS : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ((j (τ.symm (χ.eval (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)))) :
          𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
        (χ.map ψ).eval (coeC A (o : AlgebraicClosure ℚ)) := by
    intro o
    rw [← hψapp, ← hψo o, Polynomial.eval_map, Polynomial.eval₂_hom]
  have hLHS : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      (((∏ V ∈ SQ, V.evalAt (e o)) : AlgebraicClosure ℚ) : (A.valuation).Completion) =
        (∏ V ∈ SQ, (Polynomial.X - Polynomial.C (coeC A (V.evalAt y)))).eval (coeC A (o : AlgebraicClosure ℚ)) := by
    intro o
    rw [Polynomial.eval_prod, ← coeC_apply, map_prod]
    refine Finset.prod_congr rfl fun V hV => ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, ← map_sub, he o,
      evalAt_algebraMap_sub V (hrat V) _ (hy V hV)]
  set P₁ : Polynomial (A.valuation).Completion :=
    ∏ V ∈ SQ, (Polynomial.X - Polynomial.C (coeC A (V.evalAt y))) with hP₁
  have hPeq : P₁ = χ.map ψ := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective ((coeC_injective A).comp Subtype.val_injective) :
      (Set.range (fun o : ↥(NodeLocalized.coeffSubring A K) => coeC A (o : AlgebraicClosure ℚ))).Infinite)
    rintro _ ⟨o, rfl⟩
    show P₁.eval (coeC A (o : AlgebraicClosure ℚ)) = (χ.map ψ).eval (coeC A (o : AlgebraicClosure ℚ))
    rw [← hLHS o, ← hRHS o]
    exact hprod o
  have hroot : P₁.eval (coeC A c₀) = 0 := by
    rw [hPeq, Polynomial.eval_map]
    exact hχc₀
  rw [hP₁, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hroot
  obtain ⟨V, hV, hV0⟩ := hroot
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hV0
  exact ⟨V, hV, (coeC_injective A hV0).symm⟩

end CrossingValueBranch

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
open Valued in
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
    ∀ c₀ : A, c₀ ∈ maximalIdeal A → (c₀ : AlgebraicClosure ℚ) ≠ 0 →
      (∃ m ∈ maximalIdeal A, (ϖ : AlgebraicClosure ℚ) ^ E₀ = (c₀ : AlgebraicClosure ℚ) * (m : AlgebraicClosure ℚ)) →
      ∃ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.reduceFst V' = w ∧ V'.evalAt (↑c.y : ↥(modularFunctionFieldBar (N * q))) = (c₀ : AlgebraicClosure ℚ) := by
  intro c₀ hc₀ hc₀0 hwin
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
  obtain ⟨j, hj⟩ := PlaceSpecialization.exists_ringHom_adicCompletion_coeffSubring_valuationInteger (A := A) K

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

  obtain ⟨g, ⟨i₀, hgi₀⟩, hgc₀⟩ :=
    CrossingValueBranch.exists_polynomial_coeff_isUnit_eval_eq_zero red K ϖ hϖ hϖgen c₀
  have hwinE : ∃ m ∈ maximalIdeal A,
      (ϖ : AlgebraicClosure ℚ) ^ E = (c₀ : AlgebraicClosure ℚ) * (m : AlgebraicClosure ℚ) := by
    rw [← hEE]; exact hwin
  obtain ⟨Q, hπQ, hFQ, χ, hχ, hχc₀⟩ :=
    exists_prime_const_notMem_and_norm_sub_eq_eval_of_pow_eq_mul K ϖ π hπ E hE τ hτϖ j hj αV hαV c₀ hc₀ hwinE g hgc₀

  let 𝔮 : Ideal ↥(R.nodeIntegersOver K w) := Ideal.comap (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
    (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) Q.asIdeal
  haveI h𝔮prime : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  have hτ0 : ∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → τ (algebraMap _ _ o) ≠ 0 := fun o ho h0 =>
    ho (CrossingValueBranch.eq_zero_of_algebraMap_eq_zero K j hj
      (by rw [← τ.symm_apply_apply (algebraMap _ _ o), h0, map_zero]))
  have hθo : ∀ o : ↥(NodeLocalized.coeffSubring A K), (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) (R.nodeConst K w o) =
      const (π ^ E) (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)) :=
    fun o => hτ o
  have h𝔮 : ∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ 𝔮 := fun o ho hmem =>
    CrossingValueBranch.const_notMem_of_ne_zero hπ E Q.isPrime hπQ (hτ0 o ho) ((hθo o) ▸ Ideal.mem_comap.mp hmem)
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
  have hf𝔮 : (g.map (R.nodeConst K w)).eval c.y ∈ 𝔮 := Ideal.mem_comap.mpr (by rw [hfF]; exact hFQ)
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

  have hSfin := setOf_reduceFst_eq_and_forall_mem_iff_evalAt_eq_zero_finite R K w 𝔮 h𝔮0
  have hS : ∀ V, V ∈ hSfin.toFinset ↔ (P.reduceFst V = w ∧
      ∀ g' : ↥(R.nodeIntegersOver K w), g' ∈ 𝔮 ↔ V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = 0) :=
    fun V => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hcard := card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero R K w c ϖ hϖ0 hmax hres hvalA hw
    π hπ E hE ι hιϖ αU hαU hιx hht hfrac hϖgen τ hτ hτϖ 𝔮 h𝔮 h𝔮0 hqN hord hres₁ hres₂ hSfin.toFinset hS

  have hQm : Q.asIdeal ≠ maximalIdeal (UVCrossingModel W (π ^ E)) := fun h =>
    hπQ (h ▸ le_maximalIdeal hPU.ne_top (Ideal.subset_span (Set.mem_insert _ _)))
  have hQ : Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes ∧
      const (π ^ E) π ∉ Q.asIdeal :=
    ⟨CrossingValueBranch.mem_minimalPrimes_map_comap (ringKrullDim_le_two π hπ E hE) _ Q.asIdeal Q.isPrime hQm
      hf𝔮 hF0, hπQ⟩

  let SQ := hSfin.toFinset.filter (fun V => ∃ ψ : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w))
      ↥(R.nodeIntegersOver K w) →+* 𝒪[(A.valuation).Completion],
    (∀ g' : ↥(R.nodeIntegersOver K w),
      ((ψ (algebraMap ↥(R.nodeIntegersOver K w) _ g') : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
        ((V.evalAt (g' : ↥(modularFunctionFieldBar (N * q))) : AlgebraicClosure ℚ) : (A.valuation).Completion)) ∧
    Q.asIdeal = RingHom.ker (ψ.comp ι.symm.toRingHom))
  have hSQ : ∀ V, V ∈ SQ ↔ (V ∈ hSfin.toFinset ∧
      ∃ ψ : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) →+*
          𝒪[(A.valuation).Completion],
        (∀ g' : ↥(R.nodeIntegersOver K w),
          ((ψ (algebraMap ↥(R.nodeIntegersOver K w) _ g') : 𝒪[(A.valuation).Completion]) :
              (A.valuation).Completion) =
            ((V.evalAt (g' : ↥(modularFunctionFieldBar (N * q))) : AlgebraicClosure ℚ) : (A.valuation).Completion)) ∧
        Q.asIdeal = RingHom.ker (ψ.comp ι.symm.toRingHom)) :=
    fun V => Finset.mem_filter
  have hprod : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ((∏ V ∈ SQ, V.evalAt (((R.nodeConst K w o - c.y : ↥(R.nodeIntegersOver K w)) :
          ↥(modularFunctionFieldBar (N * q)))) : AlgebraicClosure ℚ) : (A.valuation).Completion) =
        ((j (τ.symm (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal
            (ι (algebraMap ↥(R.nodeIntegersOver K w) _ (R.nodeConst K w o - c.y)))))) :
            𝒪[(A.valuation).Completion]) : (A.valuation).Completion) :=
    fun o => prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq R K w c ϖ hϖ0 hmax hres hvalA hw π hπ E hE
      ι hιϖ αU hαU hιx hht hfrac hϖgen τ hτ hτϖ 𝔮 h𝔮 h𝔮0 j hj (R.nodeConst K w o - c.y) hSfin.toFinset hS hcard
      Q hQ SQ hSQ

  have hSQw : ∀ V ∈ SQ, P.reduceFst V = w := fun V hV => ((hS V).mp ((hSQ V).mp hV).1).1
  have hySQ : ∀ V ∈ SQ, (c.y : ↥(modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring :=
    fun V hV => R.mem_toValuationSubring_of_mem_nodeIntegers c.y.2.1 (hSQw V hV)
  have hnorm : ∀ o : ↥(NodeLocalized.coeffSubring A K), Algebra.norm W (Ideal.Quotient.mk Q.asIdeal
      (ι (algebraMap ↥(R.nodeIntegersOver K w) _ (R.nodeConst K w o - c.y)))) =
        χ.eval (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)) := by
    intro o
    rw [map_sub, map_sub, hτ o, hιy]
    exact hχ _
  have hprod' : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ((∏ V ∈ SQ, V.evalAt ((fun o' : ↥(NodeLocalized.coeffSubring A K) =>
          ((R.nodeConst K w o' - c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))) o) :
          AlgebraicClosure ℚ) : (A.valuation).Completion) =
        ((j (τ.symm (χ.eval (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)))) :
          𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := fun o =>
    (hprod o).trans (congrArg (fun t : W => ((j (τ.symm t) : 𝒪[(A.valuation).Completion]) :
      (A.valuation).Completion)) (hnorm o))
  obtain ⟨V, hV, hVy⟩ := CrossingValueBranch.exists_mem_and_evalAt_eq K τ j hj SQ
    (c.y : ↥(modularFunctionFieldBar (N * q))) hySQ
    (fun o' => ((R.nodeConst K w o' - c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))))
    (fun _ => rfl) χ hprod' (c₀ : AlgebraicClosure ℚ) hχc₀
  exact ⟨V, hSQw V hV, hVy⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel (solution)
