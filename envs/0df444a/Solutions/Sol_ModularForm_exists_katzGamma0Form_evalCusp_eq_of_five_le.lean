-- Prove2me | solution 1 for ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e1e6acca-8423-5e20-b638-c162d766cb5e

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps
import Definitions.Def_ModularCurve_KatzLevelPYoneda
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero
import Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le
import Theorems.Thm_ModularCurve_cuspData_map_coeffMap
import Theorems.Thm_ModularCurve_LevelP_flat_univBasisRing_vcRing_borelRing
import Theorems.Thm_WeierstrassCurve_eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero
import Definitions.Def_ModularCurve_KatzLevelPQuotient
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_c4_tateLaurent
import Theorems.Thm_ModularCurve_c6_tatePowerSeries
import Theorems.Thm_ModularCurve_delta_tateLaurent
import Theorems.Thm_ModularCurve_j_tateLaurent
import Theorems.Thm_ModularCurve_j_map_qExpand_tateLaurent
import Theorems.Thm_ModularCurve_qExpansion_div_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jqNModC_jqModC
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Theorems.Thm_ModularCurve_qExpansion_E6_eq_map_mk
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_LevelP_BasisRing_flat
import Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
import Theorems.Thm_ModularCurve_LevelP_BasisRing_etale
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange
import Theorems.Thm_ModularCurve_LevelP_isLevelPStructure_borelDataPrime
import Theorems.Thm_ModularCurve_LevelP_isUnit_discriminant_quotientByLine
import Theorems.Thm_ModularCurve_LevelP_quotientByLine_eq_of_inLine
import Theorems.Thm_ModularCurve_LevelP_quotientByLine_tateBase_nonToricPoint_fst
import Theorems.Thm_ModularCurve_LevelP_quotientByLine_variableChange
import Theorems.Thm_ModularForm_exists_mvPolynomial_levelOne_relation_qExpansion_gamma0_of_weight_two
import Theorems.Thm_ModularCurve_LevelP_isDomain_and_isIntegrallyClosed_univBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le
p2m_attr_erase "instance" "WeierstrassCurve.Generic.isElliptic_curve instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Universal.halveX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def TateCurve.tateTorsionPoint_zero_zero"

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_ofPowerSeries~coeffMap_jqModC~coeffMap_jqNModC~IsCusp P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.ModularCurve ModularCurve.LevelP"

namespace CMP

theorem isUnit_ΨSq_univ' (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ a : ℕ, 1 ≤ a → a ≤ (p - 1) / 2 → IsUnit (((univCurveT p).ΨSq a).eval (univData p).xQ) := by
  intro a ha ha'
  have hpr : p.Prime := Fact.out
  have hndvd : ¬ (p : ℤ) ∣ (a : ℤ) := by
    intro h
    have h' : p ∣ a := by exact_mod_cast h
    have := Nat.le_of_dvd (by omega) h'
    have : (p - 1) / 2 < p := by omega
    omega
  exact (WeierstrassCurve.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero (univCurveT p) hp2
    ((isUnit_natCast_univBasisRing p).mul (isUnit_Δ_univCurveT p))
    (isLevelPStructure_univData p).preΨ_Q hndvd).1

open scoped TensorProduct in

theorem P9
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R)) (k : ℤ)
    (s : UnivBasisRing p)
    (hvc : ∀ g : UnivBasisRing p →+* VCRing p,
      (univCurveT p).map g = univVC p • vcCurve p →
      (univData p).map g = (vcData p).variableChange (univVC p) →
      g s = (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) * VCRing.ofUniv p s)
    (hborel : ∀ a : ℕ, 1 ≤ a → a ≤ (p - 1) / 2 → ∀ g : UnivBasisRing p →+* BorelRing p a,
      (univCurveT p).map g = borelCurve p a → (univData p).map g = borelData' p a →
      g s = BorelRing.ofUniv p a s) :
    ∃ F : KatzGamma0Form R p k,
      F.toKatzLevelPForm.evalUniv = KatzLevelPForm.univInclude R p s ∧
      ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
        (hW' : IsUnit ((p : A) * W.Δ)) (D : LevelPData A) (hD : IsLevelPStructure W p D),
        F.toKatzLevelPForm.toFun W hW D hD = UnivBasisRing.classify p W hW' D hD s := by

  have hV : IsLevelPStructure (univVC p • vcCurve p) p ((vcData p).variableChange (univVC p)) :=
    (isLevelPStructure_vcData p).variableChange (univVC p)
  have hB : ∀ a : ℕ, 1 ≤ a → a ≤ (p - 1) / 2 → IsLevelPStructure (borelCurve p a) p (borelData' p a) :=
    fun a ha ha' => LevelP.isLevelPStructure_borelDataPrime p hp2 ha ha'
  have hu := isUnit_ΨSq_univ' p hp2

  have hg1 : KatzLevelPForm.univInclude R p s = (1 : R) ⊗ₜ[ℤ] s := rfl
  have hg : LinearMap.lTensor R (LevelP.vcForm p hV k) (KatzLevelPForm.univInclude R p s) = 0 := by
    rw [hg1, LinearMap.lTensor_tmul, LevelP.vcForm_apply,
      hvc (LevelP.vcClassify p hV) (LevelP.univCurveT_map_vcClassify p hV) (LevelP.univData_map_vcClassify p hV),
      sub_self, TensorProduct.tmul_zero]
  have hb : ∀ (a : ℕ) (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2),
      LinearMap.lTensor R (LevelP.borelForm p (hB a ha ha')) (KatzLevelPForm.univInclude R p s) = 0 := by
    intro a ha ha'
    rw [hg1, LinearMap.lTensor_tmul, LevelP.borelForm_apply,
      hborel a ha ha' (LevelP.borelClassify p (hB a ha ha')) (LevelP.univCurveT_map_borelClassify p _)
        (LevelP.univData_map_borelClassify p _),
      sub_self, TensorProduct.tmul_zero]
  refine ⟨⟨KatzLevelPForm.ofUniv p R hp k hV _ hg,
    KatzLevelPForm.dependsOnlyOnSndLine_ofUniv p R hp k hV _ hg hB hu hb⟩,
    KatzLevelPForm.evalUniv_ofUniv p R hp k hV _ hg, ?_⟩
  intro A _ _ W hW hW' D hD
  show (KatzLevelPForm.ofUniv p R hp k hV _ hg).toFun W hW D hD = _
  rw [KatzLevelPForm.ofUniv_toFun, hg1, LevelP.sClassify_tmul, map_one, one_mul]

end CMP

namespace CMP

variable (p : ℕ)

def SI (k : ℤ) (s : UnivBasisRing p) : Prop :=
  ∀ g : UnivBasisRing p →+* VCRing p,
    (univCurveT p).map g = univVC p • vcCurve p →
    (univData p).map g = (vcData p).variableChange (univVC p) →
    g s = (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) * VCRing.ofUniv p s

def BI (s : UnivBasisRing p) : Prop :=
  ∀ a : ℕ, 1 ≤ a → a ≤ (p - 1) / 2 → ∀ g : UnivBasisRing p →+* BorelRing p a,
    (univCurveT p).map g = borelCurve p a → (univData p).map g = borelData' p a →
    g s = BorelRing.ofUniv p a s

variable {p}

theorem SI.add {k : ℤ} {s s' : UnivBasisRing p} (h : SI p k s) (h' : SI p k s') : SI p k (s + s') := by
  intro g hW hD; rw [map_add, h g hW hD, h' g hW hD, map_add, mul_add]

theorem SI.mul {k k' : ℤ} {s s' : UnivBasisRing p} (h : SI p k s) (h' : SI p k' s') :
    SI p (k + k') (s * s') := by
  intro g hW hD
  rw [map_mul, h g hW hD, h' g hW hD, map_mul, zpow_add, Units.val_mul]; ring

theorem SI.neg {k : ℤ} {s : UnivBasisRing p} (h : SI p k s) : SI p k (-s) := by
  intro g hW hD; rw [map_neg, h g hW hD, map_neg, mul_neg]

theorem SI.natCast_mul {k : ℤ} {s : UnivBasisRing p} (h : SI p k s) (m : ℕ) : SI p k ((m : UnivBasisRing p) * s) := by
  intro g hW hD; rw [map_mul, map_natCast, h g hW hD, map_mul, map_natCast]; ring

theorem BI.add {s s' : UnivBasisRing p} (h : BI p s) (h' : BI p s') : BI p (s + s') := by
  intro a ha ha' g hW hD; rw [map_add, h a ha ha' g hW hD, h' a ha ha' g hW hD, map_add]

theorem BI.mul {s s' : UnivBasisRing p} (h : BI p s) (h' : BI p s') : BI p (s * s') := by
  intro a ha ha' g hW hD; rw [map_mul, h a ha ha' g hW hD, h' a ha ha' g hW hD, map_mul]

theorem BI.neg {s : UnivBasisRing p} (h : BI p s) : BI p (-s) := by
  intro a ha ha' g hW hD; rw [map_neg, h a ha ha' g hW hD, map_neg]

theorem BI.natCast_mul {s : UnivBasisRing p} (h : BI p s) (m : ℕ) : BI p ((m : UnivBasisRing p) * s) := by
  intro a ha ha' g hW hD; rw [map_mul, map_natCast, h a ha ha' g hW hD, map_mul, map_natCast]

noncomputable abbrev Bq (R : Type*) [CommRing R] (b : ℕ → ℤ) : LaurentSeries R :=
  HahnSeries.ofPowerSeries ℤ R ((PowerSeries.mk b).map (Int.castRingHom R))

end CMP

namespace CMP

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_ofPowerSeries~coeffMap_jqModC~coeffMap_jqNModC~IsCusp P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.ModularCurve ModularCurve.LevelP HahnSeries"

section Naturality

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)

theorem coeffMap_ofPowerSeries (g : PowerSeries A) :
    coeffMap f (ofPowerSeries ℤ A g) = ofPowerSeries ℤ B (PowerSeries.map f g) := by
  ext n
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact map_zero f
  · rw [PowerSeries.coeff_map]

theorem coeffMap_laurentOfInt (g : PowerSeries ℤ) :
    coeffMap f (laurentOfInt A g) = laurentOfInt B g := by
  rw [laurentOfInt_apply, laurentOfInt_apply, coeffMap_ofPowerSeries]
  congr 1
  ext n
  simp only [PowerSeries.coeff_map, eq_intCast, map_intCast]

theorem coeffMap_qExpand (N : ℕ) [NeZero N] (x : LaurentSeries A) :
    coeffMap f (qExpand A N x) = qExpand B N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem tateBase_map_coeffMap (p : ℕ) [NeZero p] :
    (tateBase A p).map (coeffMap f) = tateBase B p := by
  simp only [tateBase, tateLaurent, WeierstrassCurve.map, coeffMap_qExpand, coeffMap_laurentOfInt]

theorem coeffMap_ofPowerSeries_mk_map (b : ℕ → ℤ) :
    coeffMap f (ofPowerSeries ℤ A ((PowerSeries.mk b).map (Int.castRingHom A))) =
      ofPowerSeries ℤ B ((PowerSeries.mk b).map (Int.castRingHom B)) := by
  rw [coeffMap_ofPowerSeries]
  congr 1
  ext n
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast, map_intCast]

end Naturality

section CuspTransport

theorem classify_congr (p : ℕ) {T : Type*} [CommRing T] {W W' : WeierstrassCurve T} (hWW' : W = W')
    {D D' : LevelPData T} (hDD' : D = D') (hW : IsUnit ((p : T) * W.Δ)) (hW' : IsUnit ((p : T) * W'.Δ))
    (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure W' p D') :
    UnivBasisRing.classify p W hW D hD = UnivBasisRing.classify p W' hW' D' hD' := by
  subst hWW' hDD'; rfl

variable {p : ℕ} [Fact p.Prime]

local notation "ℤp" => Localization.Away ((p : ℕ) : ℤ)

noncomputable def cyclSpec (R : Type*) [CommRing R] [Algebra ℤp R] (ζ : Rˣ)
    (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) : cyclRing ℤp p →+* R :=
  AdjoinRoot.lift (algebraMap ℤp R) (ζ : R) (by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic,
      Polynomial.cyclotomic_prime, Polynomial.eval_geom_sum]
    exact hζ)

theorem cyclSpec_cyclZeta (R : Type*) [CommRing R] [Algebra ℤp R] (ζ : Rˣ)
    (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) :
    Units.map (cyclSpec R ζ hζ : cyclRing ℤp p →* R) (cyclZeta ℤp p) = ζ := by
  ext
  rw [Units.coe_map, MonoidHom.coe_coe, val_cyclZeta, cyclSpec, AdjoinRoot.lift_root]

theorem classify_cusp_eq_of_univ (hp5 : 5 ≤ p) (s : UnivBasisRing p) (b : ℕ → ℤ)
    (h1 : ∀ (hc : IsLevelPStructure (tateBase (cyclRing ℤp p) p) p
        (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]))
        (h' : IsUnit ((p : LaurentSeries (cyclRing ℤp p)) * (tateBase (cyclRing ℤp p) p).Δ)),
        UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) h'
          (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) hc s =
          ofPowerSeries ℤ _ ((PowerSeries.mk b).map (Int.castRingHom _)))
    (R : Type*) [CommRing R] [Algebra ℤp R] (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)
    (hc : IsLevelPStructure (tateBase R p) p (cuspData R p ζ ![1, 0] ![0, 1]))
    (h' : IsUnit ((p : LaurentSeries R) * (tateBase R p).Δ)) :
    UnivBasisRing.classify p (tateBase R p) h' (cuspData R p ζ ![1, 0] ![0, 1]) hc s =
      ofPowerSeries ℤ R ((PowerSeries.mk b).map (Int.castRingHom R)) := by

  have hpZ : IsUnit ((p : ℕ) : ℤp) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := ℤp) ((p : ℕ) : ℤ)
    simpa using this
  have hp1 : IsUnit ((p : ℕ) : cyclRing ℤp p) := by
    simpa only [map_natCast] using hpZ.map (algebraMap ℤp (cyclRing ℤp p))
  have h'1 : IsUnit ((p : LaurentSeries (cyclRing ℤp p)) * (tateBase (cyclRing ℤp p) p).Δ) := by
    refine IsUnit.mul ?_ (isUnit_Δ_tateBase _ p)
    simpa only [map_natCast] using hp1.map (algebraMap (cyclRing ℤp p) (LaurentSeries (cyclRing ℤp p)))
  have hc1 : IsLevelPStructure (tateBase (cyclRing ℤp p) p) p
      (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) :=
    ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le hp5 hp1 (cyclZeta ℤp p)
      (sum_cyclZeta_pow_eq_zero ℤp p) 1 one_ne_zero

  have hW : (tateBase (cyclRing ℤp p) p).map (coeffMap (cyclSpec R ζ hζ)) = tateBase R p :=
    tateBase_map_coeffMap _ p
  have hD : (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]).map (coeffMap (cyclSpec R ζ hζ)) =
      cuspData R p ζ ![1, 0] ![0, 1] := by
    rw [ModularCurve.cuspData_map_coeffMap (cyclSpec R ζ hζ) p hp1 (cyclZeta ℤp p)
      (sum_cyclZeta_pow_eq_zero ℤp p), cyclSpec_cyclZeta]
  have hW' : IsUnit ((p : LaurentSeries R) *
      ((tateBase (cyclRing ℤp p) p).map (coeffMap (cyclSpec R ζ hζ))).Δ) := by rw [hW]; exact h'
  have hD' : IsLevelPStructure ((tateBase (cyclRing ℤp p) p).map (coeffMap (cyclSpec R ζ hζ))) p
      ((cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]).map (coeffMap (cyclSpec R ζ hζ))) := by
    rw [hW, hD]; exact hc
  have key := UnivBasisRing.comp_classify p (tateBase (cyclRing ℤp p) p) h'1 _ hc1
    (coeffMap (cyclSpec R ζ hζ)) hW' hD'

  rw [classify_congr p hW.symm hD.symm h' hW' hc hD', ← key, RingHom.comp_apply, h1 hc1 h'1,
    coeffMap_ofPowerSeries_mk_map]

end CuspTransport

end CMP

namespace ModularCurve
p2m_export "ModularCurve" "eisenstein6 constantCoeff_eisenstein6 laurentOfInt laurentOfInt_apply tateLaurent jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd eisenstein4 constantCoeff_eisenstein4 dedekindEtaUnit ofPowerSeries_coeff_of_neg modularFunctionField modularFunctionFieldFull LevelPData LevelPData.map_xQ LevelPData.variableChange_xQ IsLevelPStructure KatzLevelPForm KatzGamma0Form LevelPData.xQ cuspPoint_of_ne_zero cuspData cuspData_xQ isUnit_Δ_tateBase cyclRing cyclZeta val_cyclZeta sum_cyclZeta_pow_eq_zero nonToricPoint tateBase coeffMap coeffMap_coeff coeffMap_single coeffEmb coeffEmb_coeff LevelP.BasisRing KatzLevelPForm.univInclude LevelP.sClassify_tmul LevelP.vcClassify LevelP.univCurveT_map_vcClassify LevelP.univData_map_vcClassify LevelP.vcForm LevelP.vcForm_apply LevelP.borelClassify LevelP.univCurveT_map_borelClassify LevelP.univData_map_borelClassify LevelP.borelForm LevelP.borelForm_apply KatzLevelPForm.ofUniv KatzLevelPForm.ofUniv_toFun KatzLevelPForm.evalUniv_ofUniv KatzLevelPForm.dependsOnlyOnSndLine_ofUniv KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le cuspData_map_coeffMap LevelP.flat_univBasisRing_vcRing_borelRing LevelP.quotientByLine LevelP.quotientByLine_map c4_tateLaurent c6_tatePowerSeries delta_tateLaurent j_tateLaurent j_map_qExpand_tateLaurent qExpansion_div_mem_laurentBaseChange mem_of_coeffEmb_mem_laurentBaseChange modularFunctionField_eq_full isIntegral_adjoin_jqNModC_jqModC qExpansion_E4_eq_map_eisenstein4 qExpansion_E6_eq_map_mk qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit LevelP.BasisRing.flat transcendental_jqNModC LevelP.BasisRing.etale LevelP.isLevelPStructure_borelDataPrime LevelP.isUnit_discriminant_quotientByLine LevelP.quotientByLine_eq_of_inLine LevelP.quotientByLine_tateBase_nonToricPoint_fst LevelP.quotientByLine_variableChange LevelP.isDomain_and_isIntegrallyClosed_univBase"
namespace YonedaInv
p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_ofPowerSeries~coeffMap_jqModC~coeffMap_jqNModC~IsCusp"

section Transfer

variable (R₀ : Type u) [CommRing R₀] (p : ℕ) [Fact p.Prime]

theorem cyclRing_faithfullyFlat : Module.FaithfullyFlat R₀ (cyclRing R₀ p) := by
  rcases subsingleton_or_nontrivial R₀ with hR | hR
  · haveI : Subsingleton (cyclRing R₀ p) := (algebraMap R₀ (cyclRing R₀ p)).codomain_trivial
    rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
    exact ⟨inferInstance, fun I hI => absurd (Subsingleton.elim I ⊤) hI⟩
  · let pb := AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic p R₀)
    haveI : Module.Free R₀ (cyclRing R₀ p) := Module.Free.of_basis pb.basis
    haveI : Nontrivial (cyclRing R₀ p) := by
      apply Module.nontrivial_of_finrank_pos (R := R₀)
      rw [pb.finrank, AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_cyclotomic]
      have := (Fact.out : p.Prime).two_le
      have h : Nat.totient p = p - 1 := Nat.totient_prime (Fact.out)
      omega
    infer_instance

theorem isUnit_p_cyclRing (hp : IsUnit (p : R₀)) : IsUnit (p : cyclRing R₀ p) := by
  simpa only [map_natCast] using hp.map (algebraMap R₀ (cyclRing R₀ p))

theorem isUnit_p_mul_Δ_tateBase_cycl (hp : IsUnit (p : R₀)) :
    IsUnit ((p : LaurentSeries (cyclRing R₀ p)) * (tateBase (cyclRing R₀ p) p).Δ) := by
  refine IsUnit.mul ?_ (isUnit_Δ_tateBase _ p)
  simpa only [map_natCast] using (isUnit_p_cyclRing R₀ p hp).map (algebraMap (cyclRing R₀ p) (LaurentSeries (cyclRing R₀ p)))

variable {R₀ p}

theorem transfer (hp5 : 5 ≤ p) (hp : IsUnit (p : R₀)) (k : ℤ) (s : UnivBasisRing p)
    (hvc : ∀ g : UnivBasisRing p →+* VCRing p,
      (univCurveT p).map g = univVC p • vcCurve p →
      (univData p).map g = (vcData p).variableChange (univVC p) →
      g s = (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) * VCRing.ofUniv p s)
    (hborel : ∀ a : ℕ, 1 ≤ a → a ≤ (p - 1) / 2 → ∀ g : UnivBasisRing p →+* BorelRing p a,
      (univCurveT p).map g = borelCurve p a → (univData p).map g = borelData' p a →
      g s = BorelRing.ofUniv p a s)
    (h0 : ∀ (hc : IsLevelPStructure (tateBase (cyclRing R₀ p) p) p
        (cuspData (cyclRing R₀ p) p (cyclZeta R₀ p) ![1, 0] ![0, 1]))
        (h' : IsUnit ((p : LaurentSeries (cyclRing R₀ p)) * (tateBase (cyclRing R₀ p) p).Δ)),
        UnivBasisRing.classify p (tateBase (cyclRing R₀ p) p) h'
          (cuspData (cyclRing R₀ p) p (cyclZeta R₀ p) ![1, 0] ![0, 1]) hc s = 0) :
    KatzLevelPForm.univInclude R₀ p s = 0 ∧
      ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R₀ A] (W : WeierstrassCurve A)
        (hW' : IsUnit ((p : A) * W.Δ)) (D : LevelPData A) (hD : IsLevelPStructure W p D),
        UnivBasisRing.classify p W hW' D hD s = 0 := by
  have hpr : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨F, hF1, hF2⟩ := CMP.P9 hp2 hp k s hvc hborel
  haveI := cyclRing_faithfullyFlat R₀ p
  have hc : IsLevelPStructure (tateBase (cyclRing R₀ p) p) p
      (cuspData (cyclRing R₀ p) p (cyclZeta R₀ p) ![1, 0] ![0, 1]) :=
    ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le hp5
      (isUnit_p_cyclRing R₀ p hp) (cyclZeta R₀ p) (sum_cyclZeta_pow_eq_zero R₀ p) 1 one_ne_zero
  have hF0 : F.toKatzLevelPForm = 0 := by
    refine ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero hp2 hp
      (cyclRing R₀ p) (cyclZeta R₀ p) (sum_cyclZeta_pow_eq_zero R₀ p) hc F.toKatzLevelPForm
      F.dependsOnlyOnSndLine ?_
    rw [hF2 _ _ (isUnit_p_mul_Δ_tateBase_cycl R₀ p hp) _ hc]
    exact h0 hc _
  refine ⟨?_, fun A _ _ W hW' D hD => ?_⟩
  · rw [← hF1, hF0]; rfl
  · have hW : IsUnit W.Δ := isUnit_of_mul_isUnit_right hW'
    rw [← hF2 W hW hW' D hD, hF0]; rfl

theorem eq_zero_of_transfer (hp5 : 5 ≤ p) (k : ℤ) (s : UnivBasisRing p)
    (hvc : ∀ g : UnivBasisRing p →+* VCRing p,
      (univCurveT p).map g = univVC p • vcCurve p →
      (univData p).map g = (vcData p).variableChange (univVC p) →
      g s = (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) * VCRing.ofUniv p s)
    (hborel : ∀ a : ℕ, 1 ≤ a → a ≤ (p - 1) / 2 → ∀ g : UnivBasisRing p →+* BorelRing p a,
      (univCurveT p).map g = borelCurve p a → (univData p).map g = borelData' p a →
      g s = BorelRing.ofUniv p a s)
    (h0 : ∀ (hc : IsLevelPStructure (tateBase (cyclRing (Localization.Away (p : ℤ)) p) p) p
        (cuspData (cyclRing (Localization.Away (p : ℤ)) p) p (cyclZeta (Localization.Away (p : ℤ)) p) ![1, 0] ![0, 1]))
        (h' : IsUnit ((p : LaurentSeries (cyclRing (Localization.Away (p : ℤ)) p)) *
          (tateBase (cyclRing (Localization.Away (p : ℤ)) p) p).Δ)),
        UnivBasisRing.classify p (tateBase (cyclRing (Localization.Away (p : ℤ)) p) p) h'
          (cuspData (cyclRing (Localization.Away (p : ℤ)) p) p (cyclZeta (Localization.Away (p : ℤ)) p) ![1, 0] ![0, 1]) hc s = 0) :
    s = 0 := by

  let f : Localization.Away (p : ℤ) →+* UnivBasisRing p :=
    IsLocalization.Away.lift (p : ℤ) (g := Int.castRingHom (UnivBasisRing p))
      (by simpa using isUnit_natCast_univBasisRing p)
  letI : Algebra (Localization.Away (p : ℤ)) (UnivBasisRing p) := f.toAlgebra
  have hp : IsUnit ((p : ℕ) : Localization.Away (p : ℤ)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : ℤ)) (p : ℤ)
    simpa using this
  have key := (transfer hp5 hp k s hvc hborel h0).2 (univCurveT p)
    ((isUnit_natCast_univBasisRing p).mul (isUnit_Δ_univCurveT p)) (univData p)
    (isLevelPStructure_univData p)
  rwa [UnivBasisRing.classify_self, RingHom.id_apply] at key

end Transfer

end ModularCurve.YonedaInv

namespace CMP

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_ofPowerSeries~coeffMap_jqModC~coeffMap_jqNModC~IsCusp P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.ModularCurve ModularCurve.LevelP HahnSeries"

section Regular

variable (p : ℕ)

theorem natCast_mul_cancel_of_flat {S : Type*} [CommRing S] [Module.Flat ℤ S] {n : ℕ} (hn : n ≠ 0)
    {x y : S} (h : (n : S) * x = (n : S) * y) : x = y := by
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S)
    (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn : (n : ℤ) ≠ 0))
  apply hreg
  simp only [zsmul_eq_mul, Int.cast_natCast]
  exact h

theorem flat_int_vcRing : Module.Flat ℤ (VCRing p) := by
  have h := ModularCurve.LevelP.flat_univBasisRing_vcRing_borelRing p
  haveI := h.1; haveI := h.2.1
  exact Module.Flat.trans ℤ (UnivBasisRing p) (VCRing p)

theorem flat_int_borelRing (a : ℕ) : Module.Flat ℤ (BorelRing p a) := by
  have h := ModularCurve.LevelP.flat_univBasisRing_vcRing_borelRing p
  haveI := h.1; haveI := h.2.2 a
  exact Module.Flat.trans ℤ (UnivBasisRing p) (BorelRing p a)

theorem flat_int_univBasisRing : Module.Flat ℤ (UnivBasisRing p) :=
  (ModularCurve.LevelP.flat_univBasisRing_vcRing_borelRing p).1

theorem cyclRing_natCast_mul_cancel [Fact p.Prime] {n : ℕ} (hn : n ≠ 0)
    {x y : cyclRing (Localization.Away ((p : ℕ) : ℤ)) p}
    (h : (n : cyclRing (Localization.Away ((p : ℕ) : ℤ)) p) * x = (n : _) * y) : x = y := by
  set Zp := Localization.Away ((p : ℕ) : ℤ)
  have hpz : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hM : Submonoid.powers ((p : ℕ) : ℤ) ≤ nonZeroDivisors ℤ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hpz
  haveI : IsDomain Zp := IsLocalization.isDomain_localization hM
  haveI : Module.Free Zp (cyclRing Zp p) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic p Zp)).basis
  have hnz : (n : Zp) ≠ 0 := by
    intro h0
    apply (by exact_mod_cast hn : (n : ℤ) ≠ 0)
    apply IsLocalization.injective Zp hM
    rw [map_natCast, h0, map_zero]
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := cyclRing Zp p)
    (mem_nonZeroDivisors_of_ne_zero hnz)
  apply hreg
  simp only [Algebra.smul_def, map_natCast]
  exact h

theorem natCast_mul_cancel_laurent {R : Type*} [CommRing R] {n : ℕ}
    (hreg : ∀ x y : R, (n : R) * x = (n : R) * y → x = y)
    {x y : LaurentSeries R} (h : (n : LaurentSeries R) * x = (n : LaurentSeries R) * y) : x = y := by
  ext k
  have hk := congrArg (fun z : LaurentSeries R => z.coeff k) h
  beta_reduce at hk
  rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := R)) n, HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, HahnSeries.coeff_smul, smul_eq_mul, smul_eq_mul] at hk
  exact hreg _ _ hk

variable {p}

theorem SI.of_natCast_mul {k : ℤ} {n : ℕ} (hn : n ≠ 0) {s : UnivBasisRing p}
    (h : SI p k ((n : UnivBasisRing p) * s)) : SI p k s := by
  intro g hW hD
  haveI := flat_int_vcRing p
  have := h g hW hD
  rw [map_mul, map_natCast, map_mul, map_natCast, mul_left_comm] at this
  exact natCast_mul_cancel_of_flat hn this

theorem BI.of_natCast_mul {n : ℕ} (hn : n ≠ 0) {s : UnivBasisRing p}
    (h : BI p ((n : UnivBasisRing p) * s)) : BI p s := by
  intro a ha ha' g hW hD
  haveI := flat_int_borelRing p a
  have := h a ha ha' g hW hD
  rw [map_mul, map_natCast, map_mul, map_natCast] at this
  exact natCast_mul_cancel_of_flat hn this

end Regular

section Transport2

variable {p : ℕ} [Fact p.Prime]

local notation "ℤp" => Localization.Away ((p : ℕ) : ℤ)

theorem isUnit_p_Zp : IsUnit ((p : ℕ) : ℤp) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := ℤp) ((p : ℕ) : ℤ)
  simpa using this

theorem isUnit_p_cycl : IsUnit ((p : ℕ) : cyclRing ℤp p) := by
  simpa only [map_natCast] using (isUnit_p_Zp (p := p)).map (algebraMap ℤp (cyclRing ℤp p))

theorem isUnit_p_mul_Δ_tateBase_cycl1 :
    IsUnit ((p : LaurentSeries (cyclRing ℤp p)) * (tateBase (cyclRing ℤp p) p).Δ) := by
  refine IsUnit.mul ?_ (isUnit_Δ_tateBase _ p)
  simpa only [map_natCast] using
    (isUnit_p_cycl (p := p)).map (algebraMap (cyclRing ℤp p) (LaurentSeries (cyclRing ℤp p)))

theorem isLevelPStructure_cusp1 (hp5 : 5 ≤ p) :
    IsLevelPStructure (tateBase (cyclRing ℤp p) p) p
      (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) :=
  ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le hp5 isUnit_p_cycl (cyclZeta ℤp p)
    (sum_cyclZeta_pow_eq_zero ℤp p) 1 one_ne_zero

theorem classify_cusp_eq_coeffMap (hp5 : 5 ≤ p) (s : UnivBasisRing p)
    (R : Type*) [CommRing R] [Algebra ℤp R] (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)
    (hc : IsLevelPStructure (tateBase R p) p (cuspData R p ζ ![1, 0] ![0, 1]))
    (h' : IsUnit ((p : LaurentSeries R) * (tateBase R p).Δ)) :
    UnivBasisRing.classify p (tateBase R p) h' (cuspData R p ζ ![1, 0] ![0, 1]) hc s =
      coeffMap (cyclSpec R ζ hζ) (UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p)
        isUnit_p_mul_Δ_tateBase_cycl1 (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1])
        (isLevelPStructure_cusp1 hp5) s) := by
  have hW : (tateBase (cyclRing ℤp p) p).map (coeffMap (cyclSpec R ζ hζ)) = tateBase R p :=
    tateBase_map_coeffMap _ p
  have hD : (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]).map (coeffMap (cyclSpec R ζ hζ)) =
      cuspData R p ζ ![1, 0] ![0, 1] := by
    rw [ModularCurve.cuspData_map_coeffMap (cyclSpec R ζ hζ) p isUnit_p_cycl (cyclZeta ℤp p)
      (sum_cyclZeta_pow_eq_zero ℤp p), cyclSpec_cyclZeta]
  have hW' : IsUnit ((p : LaurentSeries R) *
      ((tateBase (cyclRing ℤp p) p).map (coeffMap (cyclSpec R ζ hζ))).Δ) := by rw [hW]; exact h'
  have hD' : IsLevelPStructure ((tateBase (cyclRing ℤp p) p).map (coeffMap (cyclSpec R ζ hζ))) p
      ((cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]).map (coeffMap (cyclSpec R ζ hζ))) := by
    rw [hW, hD]; exact hc
  have key := UnivBasisRing.comp_classify p (tateBase (cyclRing ℤp p) p) isUnit_p_mul_Δ_tateBase_cycl1 _
    (isLevelPStructure_cusp1 hp5) (coeffMap (cyclSpec R ζ hζ)) hW' hD'
  rw [classify_congr p hW.symm hD.symm h' hW' hc hD', ← key, RingHom.comp_apply]

@[reducible] noncomputable def algebraZpCyclZMod (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) :
    Algebra ℤp (cyclRing (ZMod ℓ) p) :=
  ((algebraMap (ZMod ℓ) (cyclRing (ZMod ℓ) p)).comp
    (IsLocalization.Away.lift ((p : ℕ) : ℤ) (g := Int.castRingHom (ZMod ℓ)) (by
      rw [eq_intCast, Int.cast_natCast]
      refine IsUnit.mk0 _ ?_
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      exact hℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h)))).toAlgebra

theorem isUnit_p_zmod (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) : IsUnit ((p : ℕ) : ZMod ℓ) := by
  refine IsUnit.mk0 _ ?_
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact hℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h)

theorem dvd_of_cusp_mul (hp5 : 5 ≤ p) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (k : ℤ) (s : UnivBasisRing p)
    (hSI : SI p k s) (hBI : BI p s) (y : LaurentSeries (cyclRing ℤp p))
    (hcusp : UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p)
        isUnit_p_mul_Δ_tateBase_cycl1 (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1])
        (isLevelPStructure_cusp1 hp5) s = (ℓ : LaurentSeries (cyclRing ℤp p)) * y) :
    ∃ s' : UnivBasisRing p, s = (ℓ : UnivBasisRing p) * s' := by

  by_cases hu : IsUnit ((ℓ : ℕ) : UnivBasisRing p)
  · exact ⟨↑hu.unit⁻¹ * s, by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]⟩
  have hpr : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega

  letI := algebraZpCyclZMod (p := p) ℓ hℓ
  have h0 : ∀ (hc : IsLevelPStructure (tateBase (cyclRing (ZMod ℓ) p) p) p
        (cuspData (cyclRing (ZMod ℓ) p) p (cyclZeta (ZMod ℓ) p) ![1, 0] ![0, 1]))
      (h' : IsUnit ((p : LaurentSeries (cyclRing (ZMod ℓ) p)) * (tateBase (cyclRing (ZMod ℓ) p) p).Δ)),
      UnivBasisRing.classify p (tateBase (cyclRing (ZMod ℓ) p) p) h'
        (cuspData (cyclRing (ZMod ℓ) p) p (cyclZeta (ZMod ℓ) p) ![1, 0] ![0, 1]) hc s = 0 := by
    intro hc h'
    rw [classify_cusp_eq_coeffMap hp5 s (cyclRing (ZMod ℓ) p) (cyclZeta (ZMod ℓ) p)
      (sum_cyclZeta_pow_eq_zero (ZMod ℓ) p) hc h', hcusp, map_mul, map_natCast]
    have : ((ℓ : ℕ) : LaurentSeries (cyclRing (ZMod ℓ) p)) = 0 := by
      rw [← map_natCast (algebraMap (ZMod ℓ) (LaurentSeries (cyclRing (ZMod ℓ) p))) ℓ, ZMod.natCast_self,
        map_zero]
    rw [this, zero_mul]

  obtain ⟨-, hall⟩ := ModularCurve.YonedaInv.transfer (R₀ := ZMod ℓ) hp5 (isUnit_p_zmod ℓ hℓ) k s hSI hBI h0
  haveI : CharP (UnivBasisRing p ⧸ Ideal.span {((ℓ : ℕ) : UnivBasisRing p)}) ℓ :=
    CharP.quotient (UnivBasisRing p) ℓ hu
  letI : Algebra (ZMod ℓ) (UnivBasisRing p ⧸ Ideal.span {((ℓ : ℕ) : UnivBasisRing p)}) :=
    (ZMod.castHom (dvd_refl ℓ) _).toAlgebra
  set π := Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : UnivBasisRing p)}) with hπ
  have hW' : IsUnit ((p : UnivBasisRing p ⧸ Ideal.span {((ℓ : ℕ) : UnivBasisRing p)}) *
      ((univCurveT p).map π).Δ) := by
    rw [WeierstrassCurve.map_Δ, ← map_natCast π p, ← map_mul]
    exact ((isUnit_natCast_univBasisRing p).mul (isUnit_Δ_univCurveT p)).map π
  have key := hall ((univCurveT p).map π) hW' ((univData p).map π) ((isLevelPStructure_univData p).map π)
  rw [← UnivBasisRing.comp_classify p (univCurveT p)
      ((isUnit_natCast_univBasisRing p).mul (isUnit_Δ_univCurveT p)) (univData p)
      (isLevelPStructure_univData p) π hW' ((isLevelPStructure_univData p).map π),
    UnivBasisRing.classify_self, RingHom.comp_id, hπ, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton'] at key
  obtain ⟨s', hs'⟩ := key
  exact ⟨s', by rw [← hs', mul_comm]⟩

end Transport2

section Descent

variable {p : ℕ} [Fact p.Prime]

local notation "ℤp" => Localization.Away ((p : ℕ) : ℤ)

theorem descent_proof (hp5 : 5 ≤ p) (b : ℕ → ℤ) : ∀ (m : ℕ), m ≠ 0 → ∀ (ψ : UnivBasisRing p),
    SI p 2 ψ → BI p ψ →
    UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) isUnit_p_mul_Δ_tateBase_cycl1
        (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) (isLevelPStructure_cusp1 hp5) ψ =
      (m : LaurentSeries _) * Bq _ b →
    ∃ s : UnivBasisRing p, SI p 2 s ∧ BI p s ∧
      UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) isUnit_p_mul_Δ_tateBase_cycl1
        (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) (isLevelPStructure_cusp1 hp5) s = Bq _ b := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm ψ hSI hBI hcusp
  by_cases h1 : m = 1
  · subst h1
    exact ⟨ψ, hSI, hBI, by rw [hcusp, Nat.cast_one, one_mul]⟩

  set ℓ := m.minFac with hℓdef
  haveI hℓ : Fact ℓ.Prime := ⟨Nat.minFac_prime h1⟩
  obtain ⟨m', hm'⟩ : ℓ ∣ m := Nat.minFac_dvd m
  have hm'0 : m' ≠ 0 := by rintro rfl; exact hm (by rw [hm', mul_zero])
  have hm'lt : m' < m := by
    rw [hm']; exact lt_mul_left (Nat.pos_of_ne_zero hm'0) hℓ.out.one_lt

  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : UnivBasisRing p, ψ = (ℓ : UnivBasisRing p) * ψ' := by
    by_cases hℓp : ℓ = p
    · refine ⟨↑(isUnit_natCast_univBasisRing p).unit⁻¹ * ψ, ?_⟩
      rw [← mul_assoc, hℓp, IsUnit.mul_val_inv, one_mul]
    · refine dvd_of_cusp_mul hp5 ℓ hℓp 2 ψ hSI hBI ((m' : LaurentSeries _) * Bq _ b) ?_
      rw [hcusp, hm', Nat.cast_mul, mul_assoc]

  have hℓ0 : ℓ ≠ 0 := hℓ.out.ne_zero
  rw [hψ'] at hSI hBI hcusp
  have hSI' : SI p 2 ψ' := SI.of_natCast_mul hℓ0 hSI
  have hBI' : BI p ψ' := BI.of_natCast_mul hℓ0 hBI
  have hcusp' : UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) isUnit_p_mul_Δ_tateBase_cycl1
      (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) (isLevelPStructure_cusp1 hp5) ψ' =
      (m' : LaurentSeries _) * Bq _ b := by
    rw [map_mul, map_natCast, hm', Nat.cast_mul, mul_assoc] at hcusp
    exact natCast_mul_cancel_laurent (fun x y hxy => cyclRing_natCast_mul_cancel p hℓ0 hxy) hcusp
  exact ih m' hm'lt hm'0 ψ' hSI' hBI' hcusp'

end Descent

end CMP

namespace CMP

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_ofPowerSeries~coeffMap_jqModC~coeffMap_jqNModC~IsCusp P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.ModularCurve ModularCurve.LevelP WeierstrassCurve~cusp"

section Elements

theorem map_ringInverse {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {x : A}
    (hx : IsUnit x) : φ (Ring.inverse x) = Ring.inverse (φ x) := by
  have h1 : φ x * φ (Ring.inverse x) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hx, map_one]
  calc φ (Ring.inverse x) = Ring.inverse (φ x) * (φ x * φ (Ring.inverse x)) := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ (hx.map φ), one_mul]
    _ = Ring.inverse (φ x) := by rw [h1, mul_one]

variable (p : ℕ) [Fact p.Prime]

theorem isUnit_ΨSq_univData (hp2 : p ≠ 2) :
    ∀ a ∈ Finset.Icc 1 ((p - 1) / 2), IsUnit (((univCurveT p).ΨSq a).eval (univData p).xQ) := by
  intro a ha
  rw [Finset.mem_Icc] at ha
  have hpr : p.Prime := Fact.out
  have hndvd : ¬ (p : ℤ) ∣ (a : ℤ) := by
    intro h
    have h' : p ∣ a := by exact_mod_cast h
    have := Nat.le_of_dvd (by omega) h'
    have : (p - 1) / 2 < p := by omega
    omega
  exact (WeierstrassCurve.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero (univCurveT p) hp2
    ((isUnit_natCast_univBasisRing p).mul (isUnit_Δ_univCurveT p))
    (isLevelPStructure_univData p).preΨ_Q hndvd).1

theorem isUnit_ΨSq_map (hp2 : p ≠ 2) {T : Type*} [CommRing T] (g : UnivBasisRing p →+* T) :
    ∀ a ∈ Finset.Icc 1 ((p - 1) / 2), IsUnit ((((univCurveT p).map g).ΨSq a).eval (g (univData p).xQ)) := by
  intro a ha
  have := (isUnit_ΨSq_univData p hp2 a ha).map g
  rwa [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← WeierstrassCurve.map_ΨSq] at this

noncomputable def Wq : WeierstrassCurve (UnivBasisRing p) :=
  LevelP.quotientByLine (univCurveT p) p (univData p).xQ

noncomputable def jT : UnivBasisRing p := (univCurveT p).c₄ ^ 3 * Ring.inverse (univCurveT p).Δ

noncomputable def jQ : UnivBasisRing p := (Wq p).c₄ ^ 3 * Ring.inverse (Wq p).Δ

noncomputable def frame : UnivBasisRing p := -((Wq p).c₄ ^ 2 * (Wq p).c₆ * Ring.inverse (Wq p).Δ)

variable {p}

theorem isUnit_Δ_Wq (hp2 : p ≠ 2) : IsUnit (Wq p).Δ :=
  ModularCurve.LevelP.isUnit_discriminant_quotientByLine (univCurveT p) hp2
    ((isUnit_natCast_univBasisRing p).mul (isUnit_Δ_univCurveT p)) (isLevelPStructure_univData p).preΨ_Q

theorem Wq_map (hp2 : p ≠ 2) {T : Type*} [CommRing T] (g : UnivBasisRing p →+* T) :
    (Wq p).map g = LevelP.quotientByLine ((univCurveT p).map g) p (g (univData p).xQ) :=
  LevelP.quotientByLine_map _ p _ g (isUnit_ΨSq_univData p hp2)

theorem Wq_map_vc (hp2 : p ≠ 2) (g : UnivBasisRing p →+* VCRing p)
    (hW : (univCurveT p).map g = univVC p • vcCurve p)
    (hD : (univData p).map g = (vcData p).variableChange (univVC p)) :
    (Wq p).map g = univVC p • (Wq p).map (VCRing.ofUniv p) := by
  have hx : g (univData p).xQ = ((vcData p).variableChange (univVC p)).xQ := by
    rw [← hD]; rfl
  rw [Wq_map hp2, hW, hx, LevelPData.variableChange_xQ, Wq_map hp2, vcCurve, vcData, LevelPData.map_xQ]
  exact ModularCurve.LevelP.quotientByLine_variableChange _ p _ (isUnit_ΨSq_map p hp2 _)

theorem Wq_map_borel (hp2 : p ≠ 2) {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2)
    (g : UnivBasisRing p →+* BorelRing p a)
    (hW : (univCurveT p).map g = borelCurve p a) (hD : (univData p).map g = borelData' p a) :
    (Wq p).map g = (Wq p).map (BorelRing.ofUniv p a) := by
  have hx : g (univData p).xQ = (borelData' p a).xQ := by rw [← hD]; rfl
  have hx0 : BorelRing.ofUniv p a (univData p).xQ = (borelData p a).xQ := rfl
  rw [Wq_map hp2, Wq_map hp2, hW, hx, hx0, borelCurve]
  refine ModularCurve.LevelP.quotientByLine_eq_of_inLine _ hp2 ?_ ?_ ?_
  · rw [← borelCurve]; exact (isUnit_natCast_borelRing p a).mul (isUnit_Δ_borelCurve p a)
  · exact (isLevelPStructure_borelData p a).preΨ_Q
  · refine ⟨a, ha, ha', ?_⟩
    rw [borelData'_xQ, borelX, map_mul,
      map_ringInverse _ (isUnit_ΨSq_univData p hp2 a (Finset.mem_Icc.mpr ⟨ha, ha'⟩))]
    have hΨ : BorelRing.ofUniv p a (((univCurveT p).ΨSq a).eval (univData p).xQ) =
        (((univCurveT p).map (BorelRing.ofUniv p a)).ΨSq a).eval (borelData p a).xQ := by
      rw [WeierstrassCurve.map_ΨSq, Polynomial.eval_map, ← hx0, Polynomial.eval₂_at_apply]
    have hΦ : BorelRing.ofUniv p a (((univCurveT p).Φ a).eval (univData p).xQ) =
        (((univCurveT p).map (BorelRing.ofUniv p a)).Φ a).eval (borelData p a).xQ := by
      rw [WeierstrassCurve.map_Φ, Polynomial.eval_map, ← hx0, Polynomial.eval₂_at_apply]
    rw [hΨ, hΦ, mul_assoc, Ring.inverse_mul_cancel _ ?_, mul_one]
    rw [← hΨ]
    exact (isUnit_ΨSq_univData p hp2 a (Finset.mem_Icc.mpr ⟨ha, ha'⟩)).map _

theorem Wq_map_cusp (hp2 : p ≠ 2) (R : Type*) [CommRing R] (hp : IsUnit (p : R)) (ζ : Rˣ)
    (hc : IsLevelPStructure (tateBase R p) p (cuspData R p ζ ![1, 0] ![0, 1]))
    (h' : IsUnit ((p : LaurentSeries R) * (tateBase R p).Δ)) :
    (Wq p).map (UnivBasisRing.classify p (tateBase R p) h' (cuspData R p ζ ![1, 0] ![0, 1]) hc) =
      tateLaurent R := by
  have hx : UnivBasisRing.classify p (tateBase R p) h' (cuspData R p ζ ![1, 0] ![0, 1]) hc (univData p).xQ =
      (nonToricPoint R p 1 1).1 := by
    have := congrArg LevelPData.xQ (univData_map_classify p (tateBase R p) h' (cuspData R p ζ ![1, 0] ![0, 1]) hc)
    rw [LevelPData.map_xQ] at this
    rw [this, cuspData_xQ, cuspPoint_of_ne_zero ζ (by simp)]
    simp [ZMod.val_one]
  rw [Wq_map hp2, univCurveT_map_classify, hx]
  exact ModularCurve.LevelP.quotientByLine_tateBase_nonToricPoint_fst R p hp2 hp

theorem coe_u_inv_zpow_natCast (u : (VCRing p)ˣ) (n : ℕ) : ((u⁻¹ ^ (n : ℤ) : (VCRing p)ˣ) : VCRing p) = (↑u⁻¹) ^ n := by
  rw [zpow_natCast, Units.val_pow_eq_pow_val]

theorem BI_ofBase (x : UnivBase p) : BI p (UnivBasisRing.ofBase p x) := by
  intro a ha ha' g hW hD
  have h1 : g.comp (UnivBasisRing.ofBase p) = (BorelRing.ofUniv p a).comp (UnivBasisRing.ofBase p) := by
    refine UnivBase.ringHom_ext p ?_
    rw [← WeierstrassCurve.map_map, ← WeierstrassCurve.map_map]
    change (univCurveT p).map g = (univCurveT p).map (BorelRing.ofUniv p a)
    rw [hW]; rfl
  exact RingHom.congr_fun h1 x

theorem SI_c₄ : SI p 4 ((univCurveT p).c₄) := by
  intro g hW hD
  rw [← WeierstrassCurve.map_c₄, hW, WeierstrassCurve.variableChange_c₄, vcCurve, WeierstrassCurve.map_c₄,
    zpow_ofNat, Units.val_pow_eq_pow_val]

theorem SI_Δ : SI p 12 ((univCurveT p).Δ) := by
  intro g hW hD
  rw [← WeierstrassCurve.map_Δ, hW, WeierstrassCurve.variableChange_Δ, vcCurve, WeierstrassCurve.map_Δ,
    zpow_ofNat, Units.val_pow_eq_pow_val]

theorem SI_Wq_c₄ (hp2 : p ≠ 2) : SI p 4 ((Wq p).c₄) := by
  intro g hW hD
  rw [← WeierstrassCurve.map_c₄, Wq_map_vc hp2 g hW hD, WeierstrassCurve.variableChange_c₄,
    WeierstrassCurve.map_c₄, zpow_ofNat, Units.val_pow_eq_pow_val]

theorem SI_Wq_c₆ (hp2 : p ≠ 2) : SI p 6 ((Wq p).c₆) := by
  intro g hW hD
  rw [← WeierstrassCurve.map_c₆, Wq_map_vc hp2 g hW hD, WeierstrassCurve.variableChange_c₆,
    WeierstrassCurve.map_c₆, zpow_ofNat, Units.val_pow_eq_pow_val]

theorem SI_Wq_Δ (hp2 : p ≠ 2) : SI p 12 ((Wq p).Δ) := by
  intro g hW hD
  rw [← WeierstrassCurve.map_Δ, Wq_map_vc hp2 g hW hD, WeierstrassCurve.variableChange_Δ,
    WeierstrassCurve.map_Δ, zpow_ofNat, Units.val_pow_eq_pow_val]

theorem SI.ringInverse {k : ℤ} {s : UnivBasisRing p} (hs : IsUnit s) (h : SI p k s) :
    SI p (-k) (Ring.inverse s) := by
  intro g hW hD
  rw [map_ringInverse g hs, h g hW hD, Ring.mul_inverse_rev,
    map_ringInverse _ hs, Ring.inverse_unit, zpow_neg, mul_comm]

theorem BI.ringInverse {s : UnivBasisRing p} (hs : IsUnit s) (h : BI p s) : BI p (Ring.inverse s) := by
  intro a ha ha' g hW hD
  rw [map_ringInverse g hs, h a ha ha' g hW hD,
    map_ringInverse _ hs]

theorem SI.pow {k : ℤ} {s : UnivBasisRing p} (h : SI p k s) (n : ℕ) : SI p (n * k) (s ^ n) := by
  induction n with
  | zero => intro g hW hD; simp
  | succ n ih =>
    have := ih.mul h
    have hk : ((n + 1 : ℕ) : ℤ) * k = n * k + k := by push_cast; ring
    rw [pow_succ, hk]
    exact this

theorem BI.pow {s : UnivBasisRing p} (h : BI p s) (n : ℕ) : BI p (s ^ n) := by
  induction n with
  | zero => intro a ha ha' g hW hD; simp
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem BI_Wq_c₄ (hp2 : p ≠ 2) : BI p ((Wq p).c₄) := by
  intro a ha ha' g hW hD
  rw [← WeierstrassCurve.map_c₄, Wq_map_borel hp2 ha ha' g hW hD, WeierstrassCurve.map_c₄]

theorem BI_Wq_c₆ (hp2 : p ≠ 2) : BI p ((Wq p).c₆) := by
  intro a ha ha' g hW hD
  rw [← WeierstrassCurve.map_c₆, Wq_map_borel hp2 ha ha' g hW hD, WeierstrassCurve.map_c₆]

theorem BI_Wq_Δ (hp2 : p ≠ 2) : BI p ((Wq p).Δ) := by
  intro a ha ha' g hW hD
  rw [← WeierstrassCurve.map_Δ, Wq_map_borel hp2 ha ha' g hW hD, WeierstrassCurve.map_Δ]

theorem BI_c₄ : BI p ((univCurveT p).c₄) := by
  intro a ha ha' g hW hD
  rw [← WeierstrassCurve.map_c₄, hW, borelCurve, WeierstrassCurve.map_c₄]

theorem BI_Δ : BI p ((univCurveT p).Δ) := by
  intro a ha ha' g hW hD
  rw [← WeierstrassCurve.map_Δ, hW, borelCurve, WeierstrassCurve.map_Δ]

theorem SI_frame (hp2 : p ≠ 2) : SI p 2 (frame p) := by
  have h := (((SI_Wq_c₄ hp2).pow 2).mul (SI_Wq_c₆ hp2)).mul ((SI_Wq_Δ (p := p) hp2).ringInverse (isUnit_Δ_Wq hp2))
  have hk : ((2 : ℕ) : ℤ) * 4 + 6 + -12 = 2 := by norm_num
  rw [hk] at h
  exact h.neg

theorem BI_frame (hp2 : p ≠ 2) : BI p (frame p) :=
  ((((BI_Wq_c₄ hp2).pow 2).mul (BI_Wq_c₆ hp2)).mul ((BI_Wq_Δ hp2).ringInverse (isUnit_Δ_Wq hp2))).neg

theorem SI_jQ (hp2 : p ≠ 2) : SI p 0 (jQ p) := by
  have h := ((SI_Wq_c₄ hp2).pow 3).mul ((SI_Wq_Δ (p := p) hp2).ringInverse (isUnit_Δ_Wq hp2))
  have hk : ((3 : ℕ) : ℤ) * 4 + -12 = 0 := by norm_num
  rwa [hk] at h

theorem BI_jQ (hp2 : p ≠ 2) : BI p (jQ p) :=
  ((BI_Wq_c₄ hp2).pow 3).mul ((BI_Wq_Δ hp2).ringInverse (isUnit_Δ_Wq hp2))

theorem SI_jT : SI p 0 (jT p) := by
  have h := ((SI_c₄ (p := p)).pow 3).mul ((SI_Δ (p := p)).ringInverse (isUnit_Δ_univCurveT p))
  have hk : ((3 : ℕ) : ℤ) * 4 + -12 = 0 := by norm_num
  rwa [hk] at h

theorem BI_jT : BI p (jT p) :=
  ((BI_c₄ (p := p)).pow 3).mul ((BI_Δ (p := p)).ringInverse (isUnit_Δ_univCurveT p))

theorem SI.zero_iff_invariant {s : UnivBasisRing p} : SI p 0 s ↔ ∀ g : UnivBasisRing p →+* VCRing p,
    (univCurveT p).map g = univVC p • vcCurve p →
    (univData p).map g = (vcData p).variableChange (univVC p) → g s = VCRing.ofUniv p s := by
  constructor
  · intro h g hW hD; rw [h g hW hD, zpow_zero, Units.val_one, one_mul]
  · intro h g hW hD; rw [h g hW hD, zpow_zero, Units.val_one, one_mul]

theorem map_aeval_int {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (v : Fin 2 → A)
    (P : MvPolynomial (Fin 2) ℤ) : f (MvPolynomial.aeval v P) = MvPolynomial.aeval (f ∘ v) P := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem comp_vec2 {A B : Type*} (f : A → B) (x y : A) : f ∘ ![x, y] = ![f x, f y] := by
  ext i; fin_cases i <;> rfl

theorem aeval_int_irrel {A : Type*} [CommRing A] {σ : Type*} (i₁ i₂ : Algebra ℤ A) (v : σ → A)
    (P : MvPolynomial σ ℤ) : @MvPolynomial.aeval ℤ A σ _ _ i₁ v P = @MvPolynomial.aeval ℤ A σ _ _ i₂ v P := by
  rw [@MvPolynomial.aeval_def ℤ A σ _ _ i₁, @MvPolynomial.aeval_def ℤ A σ _ _ i₂]
  congr 1
  exact RingHom.ext_int _ _

theorem aevalPoly_int_irrel {A : Type*} [CommRing A] (i₁ i₂ : Algebra ℤ A) (x : A) (P : Polynomial ℤ) :
    @Polynomial.aeval ℤ A _ _ i₁ x P = @Polynomial.aeval ℤ A _ _ i₂ x P := by
  rw [@Polynomial.aeval_def ℤ A _ _ i₁, @Polynomial.aeval_def ℤ A _ _ i₂]
  congr 1
  exact RingHom.ext_int _ _

theorem SI_aeval_zero {s t : UnivBasisRing p} (hs : SI p 0 s) (ht : SI p 0 t) (N : MvPolynomial (Fin 2) ℤ) :
    SI p 0 (MvPolynomial.aeval ![s, t] N) := by
  rw [SI.zero_iff_invariant] at hs ht ⊢
  intro g hW hD
  rw [map_aeval_int, map_aeval_int, comp_vec2, comp_vec2, hs g hW hD, ht g hW hD]

theorem BI_aeval {s t : UnivBasisRing p} (hs : BI p s) (ht : BI p t) (N : MvPolynomial (Fin 2) ℤ) :
    BI p (MvPolynomial.aeval ![s, t] N) := by
  intro a ha ha' g hW hD
  rw [map_aeval_int, map_aeval_int, comp_vec2, comp_vec2, hs a ha ha' g hW hD, ht a ha ha' g hW hD]

theorem SI_c₆ : SI p 6 ((univCurveT p).c₆) := by
  intro g hW hD
  rw [← WeierstrassCurve.map_c₆, hW, WeierstrassCurve.variableChange_c₆, vcCurve, WeierstrassCurve.map_c₆,
    zpow_ofNat, Units.val_pow_eq_pow_val]

theorem BI_c₆ : BI p ((univCurveT p).c₆) := by
  intro a ha ha' g hW hD
  rw [← WeierstrassCurve.map_c₆, hW, borelCurve, WeierstrassCurve.map_c₆]

variable (p) in

noncomputable def cand (N : MvPolynomial (Fin 2) ℤ) : UnivBasisRing p :=
  MvPolynomial.aeval ![jT p, jQ p] N * frame p

theorem SI_cand (hp2 : p ≠ 2) (N : MvPolynomial (Fin 2) ℤ) : SI p 2 (cand p N) := by
  have := (SI_aeval_zero (SI_jT (p := p)) (SI_jQ hp2) N).mul (SI_frame hp2)
  rwa [zero_add] at this

theorem BI_cand (hp2 : p ≠ 2) (N : MvPolynomial (Fin 2) ℤ) : BI p (cand p N) :=
  (BI_aeval (BI_jT (p := p)) (BI_jQ hp2) N).mul (BI_frame hp2)

end Elements

end CMP

namespace CMP

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_ofPowerSeries~coeffMap_jqModC~coeffMap_jqNModC~IsCusp P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.ModularCurve ModularCurve.LevelP WeierstrassCurve~cusp HahnSeries"

section CuspImages

variable {p : ℕ} [Fact p.Prime] (R : Type*) [CommRing R] (hp : IsUnit (p : R)) (ζ : Rˣ)
  (hc : IsLevelPStructure (tateBase R p) p (cuspData R p ζ ![1, 0] ![0, 1]))
  (h' : IsUnit ((p : LaurentSeries R) * (tateBase R p).Δ))

noncomputable abbrev E4L : LaurentSeries R := ofPowerSeries ℤ R (eisenstein4.map (Int.castRingHom R))
noncomputable abbrev E6L : LaurentSeries R := ofPowerSeries ℤ R (eisenstein6.map (Int.castRingHom R))
noncomputable abbrev ΔL : LaurentSeries R :=
  ofPowerSeries ℤ R ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom R))

local notation "cl" => UnivBasisRing.classify p (tateBase R p) h' (cuspData R p ζ ![1, 0] ![0, 1]) hc

omit hp in
theorem tateLaurent_c₆ : (tateLaurent R).c₆ = -E6L R := by
  rw [tateLaurent, WeierstrassCurve.map_c₆, c6_tatePowerSeries, map_neg, laurentOfInt_apply]

theorem j_eq_c₄_pow_mul_ringInverse {S : Type*} [CommRing S] (W : WeierstrassCurve S) [W.IsElliptic] :
    W.c₄ ^ 3 * Ring.inverse W.Δ = W.j := by
  rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', Ring.inverse_unit, mul_comm]

theorem cl_c₄ : cl (univCurveT p).c₄ = qExpand R p (E4L R) := by
  rw [← WeierstrassCurve.map_c₄, univCurveT_map_classify, tateBase, WeierstrassCurve.map_c₄, c4_tateLaurent]

theorem cl_c₆ : cl (univCurveT p).c₆ = -qExpand R p (E6L R) := by
  rw [← WeierstrassCurve.map_c₆, univCurveT_map_classify, tateBase, WeierstrassCurve.map_c₆, tateLaurent_c₆,
    map_neg]

theorem cl_Δ : cl (univCurveT p).Δ = qExpand R p (ΔL R) := by
  rw [← WeierstrassCurve.map_Δ, univCurveT_map_classify, tateBase, WeierstrassCurve.map_Δ, delta_tateLaurent]

theorem cl_jT : cl (jT p) = jqNModC R p := by
  rw [jT, map_mul, map_pow, map_ringInverse _ (isUnit_Δ_univCurveT p),
    ← WeierstrassCurve.map_c₄, ← WeierstrassCurve.map_Δ, univCurveT_map_classify,
    j_eq_c₄_pow_mul_ringInverse]
  exact j_map_qExpand_tateLaurent R p

include hp in
theorem cl_Wq_c₄ (hp2 : p ≠ 2) : cl (Wq p).c₄ = E4L R := by
  rw [← WeierstrassCurve.map_c₄, Wq_map_cusp hp2 R hp ζ hc h', c4_tateLaurent]

include hp in
theorem cl_Wq_c₆ (hp2 : p ≠ 2) : cl (Wq p).c₆ = -E6L R := by
  rw [← WeierstrassCurve.map_c₆, Wq_map_cusp hp2 R hp ζ hc h', tateLaurent_c₆]

include hp in
theorem cl_Wq_Δ (hp2 : p ≠ 2) : cl (Wq p).Δ = ΔL R := by
  rw [← WeierstrassCurve.map_Δ, Wq_map_cusp hp2 R hp ζ hc h', delta_tateLaurent]

include hp in
theorem cl_jQ (hp2 : p ≠ 2) : cl (jQ p) = jqModC R := by
  rw [jQ, map_mul, map_pow, map_ringInverse _ (isUnit_Δ_Wq hp2),
    ← WeierstrassCurve.map_c₄, ← WeierstrassCurve.map_Δ, Wq_map_cusp hp2 R hp ζ hc h',
    j_eq_c₄_pow_mul_ringInverse, j_tateLaurent]

omit hp in
theorem isUnit_ΔL : IsUnit (ΔL R) := by
  have h := (tateLaurent R).isUnit_Δ
  rwa [delta_tateLaurent] at h

include hp in

theorem cl_frame (hp2 : p ≠ 2) : cl (frame p) = E4L R ^ 2 * E6L R * Ring.inverse (ΔL R) := by
  rw [frame, map_neg, map_mul, map_mul, map_pow, map_ringInverse _ (isUnit_Δ_Wq hp2),
    cl_Wq_c₄ R hp ζ hc h' hp2, cl_Wq_c₆ R hp ζ hc h' hp2, cl_Wq_Δ R hp ζ hc h' hp2]
  ring

include hp in

theorem cl_cand (hp2 : p ≠ 2) (N : MvPolynomial (Fin 2) ℤ) :
    cl (cand p N) = MvPolynomial.aeval ![jqNModC R p, jqModC R] N * (E4L R ^ 2 * E6L R * Ring.inverse (ΔL R)) := by
  rw [cand, map_mul, map_aeval_int, comp_vec2, cl_jT R ζ hc h', cl_jQ R hp ζ hc h' hp2, cl_frame R hp ζ hc h' hp2]
  exact congrArg₂ (· * ·) (aeval_int_irrel _ _ _ _) rfl

theorem cl_aeval_jT (D : Polynomial ℤ) :
    cl (Polynomial.aeval (jT p) D) = Polynomial.aeval (jqNModC R p) D := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, cl_jT R ζ hc h']
  congr 1
  exact RingHom.ext_int _ _

end CuspImages

end CMP

namespace CMP

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_ofPowerSeries~coeffMap_jqModC~coeffMap_jqNModC~IsCusp P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.ModularCurve ModularCurve.LevelP WeierstrassCurve~cusp HahnSeries"

section BaseElems

variable (p : ℕ) [Fact p.Prime]

noncomputable def jU : UnivBase p := (univCurve p).c₄ ^ 3 * Ring.inverse (univCurve p).Δ

variable {p}

theorem univCurveT_eq_map : univCurveT p = (univCurve p).map (UnivBasisRing.ofBase p) := rfl

theorem ofBase_c₄ : UnivBasisRing.ofBase p (univCurve p).c₄ = (univCurveT p).c₄ := by
  rw [univCurveT_eq_map, WeierstrassCurve.map_c₄]

theorem ofBase_c₆ : UnivBasisRing.ofBase p (univCurve p).c₆ = (univCurveT p).c₆ := by
  rw [univCurveT_eq_map, WeierstrassCurve.map_c₆]

theorem ofBase_Δ : UnivBasisRing.ofBase p (univCurve p).Δ = (univCurveT p).Δ := by
  rw [univCurveT_eq_map, WeierstrassCurve.map_Δ]

theorem ofBase_jU : UnivBasisRing.ofBase p (jU p) = jT p := by
  rw [jU, jT, map_mul, map_pow, map_ringInverse _ (isUnit_Δ_univCurve p), ofBase_c₄, ofBase_Δ]

theorem ofBase_aeval_jU (D : Polynomial ℤ) :
    UnivBasisRing.ofBase p (Polynomial.aeval (jU p) D) = Polynomial.aeval (jT p) D := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, ofBase_jU]
  congr 1; exact RingHom.ext_int _ _

theorem ofBase_aeval_c₄c₆ (Q : MvPolynomial (Fin 2) ℤ) :
    UnivBasisRing.ofBase p (MvPolynomial.aeval ![(univCurve p).c₄, -(univCurve p).c₆] Q) =
      MvPolynomial.aeval ![(univCurveT p).c₄, -(univCurveT p).c₆] Q := by
  rw [map_aeval_int, comp_vec2, map_neg, ofBase_c₄, ofBase_c₆]

variable (R : Type*) [CommRing R] (ζ : Rˣ)
  (hc : IsLevelPStructure (tateBase R p) p (cuspData R p ζ ![1, 0] ![0, 1]))
  (h' : IsUnit ((p : LaurentSeries R) * (tateBase R p).Δ))

theorem cl_aeval_c₄c₆ (Q : MvPolynomial (Fin 2) ℤ) :
    UnivBasisRing.classify p (tateBase R p) h' (cuspData R p ζ ![1, 0] ![0, 1]) hc
        (MvPolynomial.aeval ![(univCurveT p).c₄, -(univCurveT p).c₆] Q) =
      MvPolynomial.aeval ![qExpand R p (E4L R), qExpand R p (E6L R)] Q := by
  rw [map_aeval_int, comp_vec2, map_neg, cl_c₄ R ζ hc h', cl_c₆ R ζ hc h', neg_neg]
  exact aeval_int_irrel _ _ _ _

end BaseElems

end CMP

namespace CMP

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_ofPowerSeries~coeffMap_jqModC~coeffMap_jqNModC~IsCusp P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.ModularCurve ModularCurve.LevelP HahnSeries Polynomial"

section PresentTransport

variable {A B : Type*} [CommRing A] [CommRing B]

theorem coeffMap_injective' (f : A →+* B) (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem coeffMap_jqModC (f : A →+* B) : coeffMap f (jqModC A) = jqModC B := by
  rw [jqModC, jqModC, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries]
  congr 2
  ext n
  simp only [PowerSeries.coeff_map, eq_intCast, map_intCast]

theorem coeffMap_jqNModC (f : A →+* B) (N : ℕ) [NeZero N] : coeffMap f (jqNModC A N) = jqNModC B N := by
  rw [jqNModC, jqNModC, coeffMap_qExpand, coeffMap_jqModC]

theorem coeffMap_E4L (f : A →+* B) : coeffMap f (E4L A) = E4L B := by
  rw [E4L, E4L, ← laurentOfInt_apply, ← laurentOfInt_apply, coeffMap_laurentOfInt]

theorem coeffMap_E6L (f : A →+* B) : coeffMap f (E6L A) = E6L B := by
  rw [E6L, E6L, ← laurentOfInt_apply, ← laurentOfInt_apply, coeffMap_laurentOfInt]

theorem coeffMap_ΔL (f : A →+* B) : coeffMap f (ΔL A) = ΔL B := by
  rw [ΔL, ΔL, ← laurentOfInt_apply, ← laurentOfInt_apply, coeffMap_laurentOfInt]

theorem coeffMap_Bq (f : A →+* B) (b : ℕ → ℤ) : coeffMap f (Bq A b) = Bq B b := coeffMap_ofPowerSeries_mk_map f b

theorem map_aevalPoly_int (f : A →+* B) (x : A) (D : Polynomial ℤ) :
    f (Polynomial.aeval x D) = Polynomial.aeval (f x) D := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1; exact RingHom.ext_int _ _

def PresentId (R : Type*) [CommRing R] (p : ℕ) [NeZero p] (N : MvPolynomial (Fin 2) ℤ) (D : Polynomial ℤ)
    (b : ℕ → ℤ) : Prop :=
  @Polynomial.aeval ℤ (LaurentSeries R) _ _ (Ring.toIntAlgebra _) (jqNModC R p) D * Bq R b * ΔL R =
    @MvPolynomial.aeval ℤ (LaurentSeries R) (Fin 2) _ _ (Ring.toIntAlgebra _) ![jqNModC R p, jqModC R] N *
      E4L R ^ 2 * E6L R

theorem PresentId.map (f : A →+* B) {p : ℕ} [NeZero p] {N : MvPolynomial (Fin 2) ℤ} {D : Polynomial ℤ}
    {b : ℕ → ℤ} (h : PresentId A p N D b) : PresentId B p N D b := by
  have := congrArg (coeffMap f) h
  rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_aevalPoly_int, map_aeval_int, comp_vec2, coeffMap_jqNModC,
    coeffMap_jqModC, coeffMap_Bq, coeffMap_ΔL, coeffMap_E4L, coeffMap_E6L] at this
  exact this

theorem PresentId.of_injective (f : A →+* B) {p : ℕ} [NeZero p] {N : MvPolynomial (Fin 2) ℤ}
    {D : Polynomial ℤ} {b : ℕ → ℤ} (hf : Function.Injective f) (h : PresentId B p N D b) :
    PresentId A p N D b := by
  apply coeffMap_injective' f hf
  rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_aevalPoly_int, map_aeval_int, comp_vec2, coeffMap_jqNModC,
    coeffMap_jqModC, coeffMap_Bq, coeffMap_ΔL, coeffMap_E4L, coeffMap_E6L]
  exact h

theorem aevalPoly_map_intCast {L : Type*} [CommRing L] [Algebra ℚ L] (x : L) (D : Polynomial ℤ) :
    Polynomial.aeval x (D.map (Int.castRingHom ℚ)) = @Polynomial.aeval ℤ L _ _ (Ring.toIntAlgebra L) x D := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, @Polynomial.aeval_def ℤ L _ _ (Ring.toIntAlgebra L)]
  congr 1; exact RingHom.ext_int _ _

theorem aeval_map_intCast {L : Type*} [CommRing L] [Algebra ℚ L] (v : Fin 2 → L) (N : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial.aeval v (MvPolynomial.map (Int.castRingHom ℚ) N) =
      @MvPolynomial.aeval ℤ L (Fin 2) _ _ (Ring.toIntAlgebra L) v N := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, @MvPolynomial.aeval_def ℤ L (Fin 2) _ _ (Ring.toIntAlgebra L)]
  congr 1; exact RingHom.ext_int _ _

theorem presentId_of_rat {p : ℕ} [NeZero p] {N : MvPolynomial (Fin 2) ℤ} {D : Polynomial ℤ} {b : ℕ → ℤ}
    (h : Polynomial.aeval (jqNModC ℚ p) (D.map (Int.castRingHom ℚ)) * Bq ℚ b *
        laurentOfInt ℚ (PowerSeries.X * dedekindEtaUnit) =
      MvPolynomial.aeval ![jqNModC ℚ p, jqModC ℚ] (MvPolynomial.map (Int.castRingHom ℚ) N) *
        laurentOfInt ℚ eisenstein4 ^ 2 * laurentOfInt ℚ eisenstein6)
    (R : Type*) [CommRing R] : PresentId R p N D b := by
  have hQ : PresentId ℚ p N D b := by
    rw [aevalPoly_map_intCast, aeval_map_intCast, laurentOfInt_apply, laurentOfInt_apply, laurentOfInt_apply] at h
    exact h
  have hZ : PresentId ℤ p N D b := PresentId.of_injective (Int.castRingHom ℚ) (RingHom.injective_int _) hQ
  exact hZ.map (Int.castRingHom R)

end PresentTransport

end CMP

noncomputable section

namespace CMP
namespace Present

p2m_open "UpperHalfPlane ModularCurve~coeffMap_qExpand~coeffMap_ofPowerSeries~coeffMap_jqModC~coeffMap_jqNModC~IsCusp P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.ModularCurve Polynomial"
open scoped MatrixGroups

section Analytic

section Restrict

variable {Γ : Subgroup (GL (Fin 2) ℝ)} (hle : Γ ≤ 𝒮ℒ) {k : ℤ}

def restrictSL (f : ModularForm 𝒮ℒ k) : ModularForm Γ k where
  toFun := (f : ℍ → ℂ)
  slash_action_eq' γ hγ := f.slash_action_eq' γ (hle hγ)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (IsCusp.mono hle hc)

@[scoped simp]
theorem coe_restrictSL (f : ModularForm 𝒮ℒ k) : ⇑(restrictSL hle f) = (f : ℍ → ℂ) := rfl

theorem gamma0_le_SL (p : ℕ) : (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

end Restrict

open CongruenceSubgroup

variable (p : ℕ)

def eisDenomForm : ModularForm (Gamma0 p) ((4 : ℤ) + 4 + 6) :=
  ((restrictSL (gamma0_le_SL p) ModularForm.E₄).mul
    (restrictSL (gamma0_le_SL p) ModularForm.E₄)).mul
    (restrictSL (gamma0_le_SL p) ModularForm.E₆)

theorem coe_eisDenomForm :
    (eisDenomForm p : ℍ → ℂ) = (ModularForm.E₄ : ℍ → ℂ) ^ 2 * (ModularForm.E₆ : ℍ → ℂ) := by
  simp only [eisDenomForm, ModularForm.coe_mul, coe_restrictSL, sq]

def cuspToMod {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : CuspForm Γ k) : ModularForm Γ k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  bdd_at_cusps' hc := fun g hg => ((f.zero_at_cusps' hc) g hg).boundedAtFilter

@[scoped simp]
theorem coe_cuspToMod {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : CuspForm Γ k) :
    ⇑(cuspToMod f) = (f : ℍ → ℂ) := rfl

variable (h : ModularForm (Gamma0 p) 2)

def numForm : ModularForm (Gamma0 p) ((2 : ℤ) + 12) :=
  h.mul (restrictSL (gamma0_le_SL p) (cuspToMod CuspForm.discriminant))

theorem coe_numForm :
    (numForm p h : ℍ → ℂ) = (h : ℍ → ℂ) * (ModularForm.discriminant : ℍ → ℂ) := by
  simp only [numForm, ModularForm.coe_mul, coe_restrictSL, coe_cuspToMod]
  rfl

def eisDenomForm' : ModularForm (Gamma0 p) ((2 : ℤ) + 12) :=
  (show ((4 : ℤ) + 4 + 6) = ((2 : ℤ) + 12) by ring) ▸ eisDenomForm p

theorem coe_eisDenomForm' :
    (eisDenomForm' p : ℍ → ℂ) = (ModularForm.E₄ : ℍ → ℂ) ^ 2 * (ModularForm.E₆ : ℍ → ℂ) := by
  rw [show (eisDenomForm' p : ℍ → ℂ) = (eisDenomForm p : ℍ → ℂ) from ?_, coe_eisDenomForm]
  unfold eisDenomForm'
  congr 1

theorem one_mem_strictPeriods_Gamma0 :
    (1 : ℝ) ∈ (Gamma0 p : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, ?_, ?_⟩
  · exact CongruenceSubgroup.Gamma0_mem.mpr (by simp [ModularGroup.T])
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom_apply,
        Matrix.SpecialLinearGroup.mapGL]

theorem eisDenomForm'_ne_zero [Fact (Nat.Prime p)] : eisDenomForm' p ≠ 0 := by
  have hone := one_mem_strictPeriods_Gamma0 p
  intro heq
  have hq0 : qExpansion 1 (eisDenomForm' p : ℍ → ℂ) = 0 :=
    (ModularForm.qExpansion_eq_zero_iff one_pos hone (eisDenomForm' p)).mpr heq
  rw [coe_eisDenomForm', show (ModularForm.E₄ : ℍ → ℂ) ^ 2 * (ModularForm.E₆ : ℍ → ℂ) =
        (⇑(ModularForm.E₄.mul ModularForm.E₄) : ℍ → ℂ) * (ModularForm.E₆ : ℍ → ℂ) by
      rw [ModularForm.coe_mul]; ring,
    ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL] at hq0
  have hc0 := congrArg (fun s => s.constantCoeff) hq0
  beta_reduce at hc0
  rw [map_mul, map_mul, ModularCurve.qExpansion_E4_eq_map_eisenstein4,
    ModularCurve.qExpansion_E6_eq_map_mk] at hc0
  have hcc : ∀ (Z : PowerSeries ℤ), PowerSeries.constantCoeff
      ((PowerSeries.map (Int.castRingHom ℂ)) Z) = ((Z.constantCoeff : ℤ) : ℂ) := fun Z => rfl
  rw [hcc, hcc, ModularCurve.constantCoeff_eisenstein4, PowerSeries.constantCoeff_mk] at hc0
  norm_num at hc0

theorem qExp_h_eq (b : ℕ → ℤ) (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n) :
    qExpansion 1 (h : ℍ → ℂ) = (PowerSeries.mk b).map (Int.castRingHom ℂ) := by
  ext n
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk, Int.coe_castRingHom]
  exact (hb n).symm

theorem qExp_numForm_eq :
    qExpansion 1 (numForm p h : ℍ → ℂ) =
      qExpansion 1 (h : ℍ → ℂ) * qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) := by
  rw [coe_numForm, show (ModularForm.discriminant : ℍ → ℂ) =
        (restrictSL (gamma0_le_SL p) (cuspToMod CuspForm.discriminant) : ℍ → ℂ) from rfl]
  exact ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods_Gamma0 p) h _

theorem qExp_eisDenomForm'_eq :
    qExpansion 1 (eisDenomForm' p : ℍ → ℂ) =
      qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) ^ 2 * qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) := by
  rw [coe_eisDenomForm', show (ModularForm.E₄ : ℍ → ℂ) ^ 2 * (ModularForm.E₆ : ℍ → ℂ) =
        (⇑(ModularForm.E₄.mul ModularForm.E₄) : ℍ → ℂ) * (ModularForm.E₆ : ℍ → ℂ) by
      rw [ModularForm.coe_mul]; ring,
    ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL]
  ring

end Analytic

section Series

theorem coeffEmb_ofPowerSeries_map (L : Type*) [Field L] [Algebra ℚ L] (Z : PowerSeries ℤ) :
    coeffEmb L (HahnSeries.ofPowerSeries ℤ ℚ (Z.map (Int.castRingHom ℚ))) =
      HahnSeries.ofPowerSeries ℤ L (Z.map (Int.castRingHom L)) := by
  ext k
  rw [coeffEmb_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map, PowerSeries.coeff_map]
    simp
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

def numSeries (b : ℕ → ℤ) : PowerSeries ℤ := PowerSeries.mk b * (PowerSeries.X * dedekindEtaUnit)

def denSeries : PowerSeries ℤ := eisenstein4 ^ 2 * eisenstein6

def xh (b : ℕ → ℤ) : LaurentSeries ℚ :=
  HahnSeries.ofPowerSeries ℤ ℚ ((numSeries b).map (Int.castRingHom ℚ)) /
    HahnSeries.ofPowerSeries ℤ ℚ (denSeries.map (Int.castRingHom ℚ))

theorem denSeries_map_ne_zero : HahnSeries.ofPowerSeries ℤ ℚ (denSeries.map (Int.castRingHom ℚ)) ≠ 0 := by
  intro h0
  have h1 := congrArg (fun x : LaurentSeries ℚ => x.coeff 0) h0
  beta_reduce at h1
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, denSeries, map_mul,
    map_pow, constantCoeff_eisenstein4, constantCoeff_eisenstein6] at h1
  norm_num at h1

theorem xh_mem_adjoin (p : ℕ) [Fact p.Prime] [NeZero p] (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (b : ℕ → ℤ) (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n) :
    xh b ∈ IntermediateField.adjoin ℚ {jqNModC ℚ p, jqModC ℚ} := by
  have hX := ModularCurve.qExpansion_div_mem_laurentBaseChange p (numForm p h) (eisDenomForm' p)
    (eisDenomForm'_ne_zero p)
  rw [qExp_numForm_eq, qExp_h_eq p h b hb,
    ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, ← map_mul,
    qExp_eisDenomForm'_eq, ModularCurve.qExpansion_E4_eq_map_eisenstein4,
    ModularCurve.qExpansion_E6_eq_map_mk, ← map_pow, ← map_mul] at hX
  have hE6 : (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) =
      eisenstein6 := rfl
  rw [hE6] at hX
  have hcoeff : coeffEmb ℂ (xh b) =
      (HahnSeries.ofPowerSeries ℤ ℂ ((numSeries b).map (Int.castRingHom ℂ))) /
        HahnSeries.ofPowerSeries ℤ ℂ (denSeries.map (Int.castRingHom ℂ)) := by
    rw [xh, map_div₀, coeffEmb_ofPowerSeries_map, coeffEmb_ofPowerSeries_map]
  have hmem := ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange ℂ (modularFunctionFieldFull p)
    (xh b) (by rw [hcoeff]; exact hX)
  rw [← ModularCurve.modularFunctionField_eq_full] at hmem
  have hF : IntermediateField.adjoin ℚ {jqNModC ℚ p, jqModC ℚ} = modularFunctionField p := by
    rw [Set.pair_comm]; rfl
  rw [hF]
  exact hmem

open IntermediateField in

theorem isIntegral_jqModC (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] :
    IsIntegral K⟮jqNModC K p⟯ (jqModC K) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hint := ModularCurve.isIntegral_adjoin_jqNModC_jqModC K p
  set F : IntermediateField K (LaurentSeries K) := modularFunctionFieldC K p with hFdef
  set tF : F := ⟨jqNModC K p, jqNModC_mem K p⟩ with htF
  set aF : F := ⟨jqModC K, jqModC_mem K p⟩ with haF
  set A : Subalgebra K F := Algebra.adjoin K ({tF} : Set F) with hA

  have hle : A ≤ (K⟮jqNModC K p⟯.toSubalgebra).comap (F.val : F →ₐ[K] LaurentSeries K) := by
    refine Algebra.adjoin_le ?_
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact (Subalgebra.mem_comap _ _ _).mpr (IntermediateField.mem_adjoin_simple_self K (jqNModC K p))
  have hmemA : ∀ a : A, ((a : F) : LaurentSeries K) ∈ K⟮jqNModC K p⟯ := fun a =>
    (Subalgebra.mem_comap _ _ _).mp (hle a.2)
  let φ : A →+* K⟮jqNModC K p⟯ :=
    ((F.val : F →ₐ[K] LaurentSeries K).toRingHom.comp A.val.toRingHom).codRestrict _ hmemA
  have key := IsIntegral.map_of_comp_eq (R := A) (S := F) (T := K⟮jqNModC K p⟯)
    (U := LaurentSeries K) φ (F.val : F →ₐ[K] LaurentSeries K).toRingHom
    (RingHom.ext fun a => rfl) hint
  exact key

end Series

section Structure

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

open IntermediateField in

theorem exists_mul_aeval_eq_of_mem_adjoin_pair {t α z : E}
    (hα : IsIntegral K⟮t⟯ α) (hz : z ∈ K⟮t, α⟯) :
    ∃ (D : K[X]) (N : MvPolynomial (Fin 2) K), aeval t D ≠ 0 ∧
      z * aeval t D = MvPolynomial.aeval ![t, α] N := by
  classical
  rw [← adjoin_simple_adjoin_simple, mem_restrictScalars] at hz
  have hz2 : z ∈ (K⟮t⟯⟮α⟯).toSubalgebra := hz
  rw [adjoin_simple_toSubalgebra_of_isAlgebraic hα.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hz2
  obtain ⟨Q, hQ⟩ := hz2
  have hcoef : ∀ i : ℕ, ∃ r s : K[X], aeval t s ≠ 0 ∧
      ((Q.coeff i : K⟮t⟯) : E) = aeval t r / aeval t s := by
    intro i
    obtain ⟨r, s, hrs⟩ := (mem_adjoin_simple_iff (F := K) ((Q.coeff i : K⟮t⟯) : E)).mp (Q.coeff i).2
    by_cases hs : aeval t s = 0
    · exact ⟨0, 1, by simp, by rw [hrs, hs, div_zero, map_zero, map_one, zero_div]⟩
    · exact ⟨r, s, hs, hrs⟩
  choose r s hs hrs using hcoef
  refine ⟨∏ i ∈ Q.support, s i,
    ∑ i ∈ Q.support, Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
      (r i * ∏ j ∈ Q.support.erase i, s j) * MvPolynomial.X 1 ^ i, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hs i
  · have hzsum : z = ∑ i ∈ Q.support, ((Q.coeff i : K⟮t⟯) : E) * α ^ i := by
      rw [← hQ]
      change Polynomial.aeval α Q = _
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
      rfl
    rw [hzsum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [map_mul, map_pow, MvPolynomial.aeval_X, ← Polynomial.aeval_algHom_apply,
      MvPolynomial.aeval_X, map_prod, ← Finset.mul_prod_erase _ _ hi, hrs i, map_mul, map_prod]
    have hsi := hs i
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    try ring

end Structure

section Clearing

theorem exists_int_mul_eq (S : Finset ℚ) :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ c ∈ S, ∃ z : ℤ, (z : ℚ) = M * c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a S _ ih =>
    obtain ⟨M, hM, hS⟩ := ih
    refine ⟨M * a.den, mul_ne_zero hM (Int.natCast_ne_zero.mpr a.den_ne_zero), ?_⟩
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · refine ⟨M * c.num, ?_⟩
      push_cast
      rw [← Rat.mul_den_eq_num]
      ring
    · obtain ⟨z, hz⟩ := hS c hc
      refine ⟨z * c.den * 0 + z * a.den, ?_⟩
      push_cast
      rw [hz]
      ring

theorem exists_clear (D : ℚ[X]) (N : MvPolynomial (Fin 2) ℚ) :
    ∃ (M : ℤ) (Dz : ℤ[X]) (Nz : MvPolynomial (Fin 2) ℤ), M ≠ 0 ∧
      Dz.map (Int.castRingHom ℚ) = Polynomial.C (M : ℚ) * D ∧
      MvPolynomial.map (Int.castRingHom ℚ) Nz = MvPolynomial.C (M : ℚ) * N := by
  classical
  obtain ⟨M, hM, hS⟩ := exists_int_mul_eq
    (D.support.image D.coeff ∪ N.support.image fun v => MvPolynomial.coeff v N)
  have hD : ∀ i ∈ D.support, ∃ z : ℤ, (z : ℚ) = M * D.coeff i := fun i hi =>
    hS _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi))
  have hN : ∀ v ∈ N.support, ∃ z : ℤ, (z : ℚ) = M * MvPolynomial.coeff v N := fun v hv =>
    hS _ (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun v => MvPolynomial.coeff v N) hv))
  choose! zD hzD using hD
  choose! zN hzN using hN
  refine ⟨M, ∑ i ∈ D.support, Polynomial.C (zD i) * Polynomial.X ^ i,
    ∑ v ∈ N.support, MvPolynomial.monomial v (zN v), hM, ?_, ?_⟩
  · rw [Polynomial.map_sum]
    conv_rhs => rw [D.as_sum_support_C_mul_X_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      eq_intCast, hzD i hi, ← mul_assoc, ← Polynomial.C_mul]
  · rw [map_sum]
    conv_rhs => rw [N.as_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [MvPolynomial.map_monomial, eq_intCast, hzN v hv, MvPolynomial.C_mul_monomial]

end Clearing

theorem exists_presentation {p : ℕ} [Fact p.Prime]
    (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n) :
    ∃ (N : MvPolynomial (Fin 2) ℤ) (D : Polynomial ℤ), D ≠ 0 ∧
      Polynomial.aeval (ModularCurve.jqNModC ℚ p) (D.map (Int.castRingHom ℚ)) *
          HahnSeries.ofPowerSeries ℤ ℚ ((PowerSeries.mk b).map (Int.castRingHom ℚ)) *
          ModularCurve.laurentOfInt ℚ (PowerSeries.X * ModularCurve.dedekindEtaUnit) =
        MvPolynomial.aeval ![ModularCurve.jqNModC ℚ p, ModularCurve.jqModC ℚ] (MvPolynomial.map (Int.castRingHom ℚ) N) *
          ModularCurve.laurentOfInt ℚ ModularCurve.eisenstein4 ^ 2 * ModularCurve.laurentOfInt ℚ ModularCurve.eisenstein6 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨D, N, hD, hzD⟩ :=
    exists_mul_aeval_eq_of_mem_adjoin_pair (isIntegral_jqModC ℚ p) (xh_mem_adjoin p h b hb)
  obtain ⟨M, Dz, Nz, hM, hDz, hNz⟩ := exists_clear D N
  refine ⟨Nz, Dz, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (Polynomial.map (Int.castRingHom ℚ)) h0
    rw [hDz, Polynomial.map_zero] at h1
    refine mul_ne_zero (Polynomial.C_ne_zero.mpr (Int.cast_ne_zero.mpr hM)) ?_ h1
    intro hD0
    exact hD (by rw [hD0, map_zero])
  · have key : HahnSeries.ofPowerSeries ℤ ℚ ((numSeries b).map (Int.castRingHom ℚ)) *
        Polynomial.aeval (jqNModC ℚ p) D =
        MvPolynomial.aeval ![jqNModC ℚ p, jqModC ℚ] N *
          HahnSeries.ofPowerSeries ℤ ℚ (denSeries.map (Int.castRingHom ℚ)) := by
      rw [← div_eq_iff denSeries_map_ne_zero, ← hzD, xh, div_mul_eq_mul_div]
    have hnumL : HahnSeries.ofPowerSeries ℤ ℚ ((numSeries b).map (Int.castRingHom ℚ)) =
        HahnSeries.ofPowerSeries ℤ ℚ ((PowerSeries.mk b).map (Int.castRingHom ℚ)) *
          laurentOfInt ℚ (PowerSeries.X * dedekindEtaUnit) := by
      rw [numSeries, map_mul, map_mul]
      rfl
    have hdenL : HahnSeries.ofPowerSeries ℤ ℚ (denSeries.map (Int.castRingHom ℚ)) =
        laurentOfInt ℚ eisenstein4 ^ 2 * laurentOfInt ℚ eisenstein6 := by
      rw [denSeries, map_mul, map_pow, map_mul, map_pow]
      rfl
    rw [hnumL, hdenL] at key
    rw [hDz, hNz, map_mul (Polynomial.aeval (jqNModC ℚ p)), Polynomial.aeval_C,
      map_mul (MvPolynomial.aeval ![jqNModC ℚ p, jqModC ℚ]), MvPolynomial.aeval_C]
    linear_combination (algebraMap ℚ (LaurentSeries ℚ) (M : ℚ)) * key

end CMP.Present
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP"

end
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"

namespace CMP
namespace SmoothNormal

open Polynomial TensorProduct

universe v w w'

theorem isIntegrallyClosedIn_of_isPushout
    (R : Type u) (S : Type v) (K : Type w) (L : Type w')
    [CommRing R] [CommRing S] [CommRing K] [CommRing L]
    [Algebra R S] [Algebra R K] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Algebra.IsPushout R S K L] [Algebra.Smooth R S] [IsIntegrallyClosedIn R K] :
    IsIntegrallyClosedIn S L := by

  let e : S ⊗[R] K ≃ₐ[S] L := Algebra.IsPushout.equiv R S K L
  refine (AlgEquiv.isIntegrallyClosedIn e).mp ?_
  have hRK : Function.Injective (algebraMap R K) := IsIntegralClosure.algebraMap_injective R R K
  rw [isIntegrallyClosedIn_iff]
  refine ⟨?_, ?_⟩
  ·
    have h := Algebra.TensorProduct.includeLeft_injective (R := R) (S := R) (A := S) (B := K) hRK
    intro x y hxy
    apply h
    simpa [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeLeft_apply] using hxy
  · intro x hx
    obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S)
      (B := K)).2 ⟨x, hx⟩

    have key : ∀ z : S ⊗[R] integralClosure R K, ∃ s : S,
        algebraMap S (S ⊗[R] K) s = (TensorProduct.toIntegralClosure R S K z : S ⊗[R] K) := by
      intro z
      induction z with
      | zero => exact ⟨0, by simp⟩
      | add a b ha hb =>
        obtain ⟨s, hs⟩ := ha
        obtain ⟨t, ht⟩ := hb
        exact ⟨s + t, by simp [hs, ht, map_add]⟩
      | tmul s k =>
        obtain ⟨r, hr⟩ := (IsIntegralClosure.isIntegral_iff (A := R) (R := R) (B := K)).mp k.2
        refine ⟨r • s, ?_⟩
        have h1 : (TensorProduct.toIntegralClosure R S K (s ⊗ₜ[R] k) : S ⊗[R] K) = s ⊗ₜ (k : K) :=
          rfl
        rw [h1, ← hr, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply, Algebra.algebraMap_eq_smul_one r, ← TensorProduct.smul_tmul]
    obtain ⟨s, hs⟩ := key y
    exact ⟨s, by rw [hs, hy]⟩

theorem isIntegrallyClosedIn_of_isLocalization
    (R : Type u) (S : Type v) (Rₘ : Type w) (Sₘ : Type w')
    [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
    [Algebra R S] [Algebra R Rₘ] [Algebra S Sₘ] [Algebra Rₘ Sₘ] [Algebra R Sₘ]
    [IsScalarTower R S Sₘ] [IsScalarTower R Rₘ Sₘ]
    (M : Submonoid R) [IsLocalization M Rₘ]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
    [Algebra.Smooth R S] [IsIntegrallyClosedIn R Rₘ] :
    IsIntegrallyClosedIn S Sₘ :=
  haveI : Algebra.IsPushout R S Rₘ Sₘ :=
    Algebra.isPushout_of_isLocalization (S := M) (A := Rₘ) (T := S) (B := Sₘ)
  isIntegrallyClosedIn_of_isPushout R S Rₘ Sₘ

theorem isIntegrallyClosedIn_base_of_isLocalization
    (R : Type u) (Rₘ : Type w) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing Rₘ] [Algebra R Rₘ] (M : Submonoid R) (hM : M ≤ nonZeroDivisors R)
    [IsLocalization M Rₘ] : IsIntegrallyClosedIn R Rₘ := by

  have hg : ∀ m : M, IsUnit (algebraMap R (FractionRing R) (m : R)) := fun m =>
    IsLocalization.map_units (FractionRing R) (⟨(m : R), hM m.2⟩ : nonZeroDivisors R)
  let f : Rₘ →ₐ[R] FractionRing R :=
    { IsLocalization.lift (M := M) (S := Rₘ) (g := algebraMap R (FractionRing R)) hg with
      commutes' := fun r => IsLocalization.lift_eq (M := M) hg r }
  have hf : Function.Injective f := by
    show Function.Injective (IsLocalization.lift (M := M) (S := Rₘ) hg)
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective Rₘ hM).eq_iff]
    exact ((IsFractionRing.injective R (FractionRing R)).eq_iff).symm
  exact AlgHom.isIntegrallyClosedIn f hf inferInstance

theorem isIntegrallyClosedIn_of_isLocalization_of_le_nonZeroDivisors
    (R : Type u) (S : Type v) (Sₘ : Type w')
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [CommRing Sₘ]
    [Algebra R S] [Algebra S Sₘ] [Algebra R Sₘ] [IsScalarTower R S Sₘ]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R)
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ] [Algebra.Smooth R S] :
    IsIntegrallyClosedIn S Sₘ := by
  letI : Algebra (Localization M) Sₘ := localizationAlgebra M S
  haveI : IsScalarTower R (Localization M) Sₘ := isScalarTower_localizationAlgebra M S
  haveI := isIntegrallyClosedIn_base_of_isLocalization R (Localization M) M hM
  exact isIntegrallyClosedIn_of_isLocalization R S (Localization M) Sₘ M

theorem dvd_of_pow_add_sum_eq_zero
    {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (d : R) (hd : d ≠ 0) (t : S) (n : ℕ) (c : ℕ → R)
    (h : t ^ (n + 1) + ∑ i ∈ Finset.range (n + 1),
      algebraMap R S (c i) * algebraMap R S d ^ (n + 1 - i) * t ^ i = 0) :
    algebraMap R S d ∣ t := by
  classical
  set δ : S := algebraMap R S d with hδ
  let M : Submonoid R := Submonoid.powers d
  have hM : M ≤ nonZeroDivisors R :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hd)
  let Sₘ := Localization (Algebra.algebraMapSubmonoid S M)
  haveI hIC : IsIntegrallyClosedIn S Sₘ :=
    isIntegrallyClosedIn_of_isLocalization_of_le_nonZeroDivisors R S Sₘ M hM
  have hδM : δ ∈ Algebra.algebraMapSubmonoid S M := ⟨d, Submonoid.mem_powers d, rfl⟩

  set z : Sₘ := IsLocalization.mk' Sₘ t ⟨δ, hδM⟩ with hz_def
  have hz : z * algebraMap S Sₘ δ = algebraMap S Sₘ t := IsLocalization.mk'_spec Sₘ t ⟨δ, hδM⟩
  have hδu : IsUnit (algebraMap S Sₘ δ) := IsLocalization.map_units Sₘ ⟨δ, hδM⟩

  let q : S[X] := ∑ i ∈ Finset.range (n + 1), C (algebraMap R S (c i)) * X ^ i
  have hq : q.degree < (n + 1 : ℕ) := by
    refine (degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr ?_
    intro i hi
    refine (degree_C_mul_X_pow_le i _).trans_lt ?_
    exact_mod_cast Finset.mem_range.mp hi
  have hmonic : (X ^ (n + 1) + q).Monic := monic_X_pow_add hq
  have hroot : aeval z (X ^ (n + 1) + q) = 0 := by

    have hmap := congrArg (algebraMap S Sₘ) h
    rw [map_zero] at hmap
    have key : algebraMap S Sₘ (t ^ (n + 1) + ∑ i ∈ Finset.range (n + 1),
          algebraMap R S (c i) * δ ^ (n + 1 - i) * t ^ i) =
        algebraMap S Sₘ δ ^ (n + 1) * aeval z (X ^ (n + 1) + q) := by
      simp only [q, map_add, map_pow, map_sum, map_mul, aeval_X, aeval_C, ← hz]
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i ≤ n + 1 := (Finset.mem_range.mp hi).le
        have hsplit : algebraMap S Sₘ δ ^ (n + 1) =
            algebraMap S Sₘ δ ^ (n + 1 - i) * algebraMap S Sₘ δ ^ i := by
          rw [← pow_add, Nat.sub_add_cancel hi']
        rw [hsplit, mul_pow]
        ring
    rw [key] at hmap
    exact (hδu.pow (n + 1)).mul_right_eq_zero.mp hmap
  have hint : IsIntegral S z := ⟨X ^ (n + 1) + q, hmonic, by simpa [aeval_def] using hroot⟩
  obtain ⟨s, hs⟩ := (IsIntegralClosure.isIntegral_iff (A := S) (R := S) (B := Sₘ)).mp hint
  refine ⟨s, ?_⟩
  apply IsIntegralClosure.algebraMap_injective S S Sₘ
  rw [map_mul, hs, mul_comm, hz]

end CMP.SmoothNormal
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"

namespace CMP

section P8a

variable {p : ℕ} [Fact p.Prime]

local notation "ℤp" => Localization.Away ((p : ℕ) : ℤ)

theorem SI.congr_weight {k k' : ℤ} {s : UnivBasisRing p} (h : SI p k s) (hk : k = k') : SI p k' s :=
  hk ▸ h

theorem SI.zero (k : ℤ) : SI p k (0 : UnivBasisRing p) := by
  intro g hW hD; rw [map_zero, map_zero, mul_zero]

theorem BI.zero : BI p (0 : UnivBasisRing p) := by
  intro a ha ha' g hW hD; rw [map_zero, map_zero]

theorem SI.sum {ι : Type*} (s : Finset ι) (f : ι → UnivBasisRing p) (k : ℤ)
    (h : ∀ i ∈ s, SI p k (f i)) : SI p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact SI.zero k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem BI.sum {ι : Type*} (s : Finset ι) (f : ι → UnivBasisRing p)
    (h : ∀ i ∈ s, BI p (f i)) : BI p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact BI.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem SI.intCast_mul {k : ℤ} {s : UnivBasisRing p} (h : SI p k s) (m : ℤ) :
    SI p k ((m : UnivBasisRing p) * s) := by
  intro g hW hD; rw [map_mul, map_intCast, h g hW hD, map_mul, map_intCast]; ring

theorem BI.intCast_mul {s : UnivBasisRing p} (h : BI p s) (m : ℤ) : BI p ((m : UnivBasisRing p) * s) := by
  intro a ha ha' g hW hD; rw [map_mul, map_intCast, h a ha ha' g hW hD, map_mul, map_intCast]

theorem SI_ofBase_aeval_weighted (P : MvPolynomial (Fin 2) ℤ) (m : ℕ)
    (hP : P.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) m) :
    SI p (m : ℤ) (UnivBasisRing.ofBase p
      (MvPolynomial.aeval ![(univCurve p).c₄, -(univCurve p).c₆] P)) := by
  classical
  rw [map_aeval_int, comp_vec2, map_neg]
  have hc4 : UnivBasisRing.ofBase p (univCurve p).c₄ = (univCurveT p).c₄ := by
    rw [show univCurveT p = (univCurve p).map (UnivBasisRing.ofBase p) from rfl, WeierstrassCurve.map_c₄]
  have hc6 : UnivBasisRing.ofBase p (univCurve p).c₆ = (univCurveT p).c₆ := by
    rw [show univCurveT p = (univCurve p).map (UnivBasisRing.ofBase p) from rfl, WeierstrassCurve.map_c₆]
  rw [hc4, hc6, MvPolynomial.as_sum P, map_sum]
  refine SI.sum _ _ _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two,
    eq_intCast]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hw : d 0 * 4 + d 1 * 6 = m := by
    have := hP (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using this
  have h1 := (((SI_c₄ (p := p)).pow (d 0)).mul ((SI_c₆ (p := p)).neg.pow (d 1))).intCast_mul
    (MvPolynomial.coeff d P)
  refine h1.congr_weight ?_
  have := congrArg (fun x : ℕ => (x : ℤ)) hw
  push_cast at this ⊢
  linarith

theorem pow_add_sum_eq_zero_of_cusp (hp5 : 5 ≤ p) (n : ℕ) (k : ℤ)
    (t : UnivBasisRing p) (d : UnivBase p) (c : ℕ → UnivBase p)
    (ht : SI p k t) (htB : BI p t)
    (hd : SI p 0 (UnivBasisRing.ofBase p d))
    (hc : ∀ i ∈ Finset.range (n + 1), SI p ((n + 1 - i : ℕ) * k) (UnivBasisRing.ofBase p (c i)))
    (h0 : ∀ (hc : IsLevelPStructure (tateBase (cyclRing ℤp p) p) p
          (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]))
        (h' : IsUnit ((p : LaurentSeries (cyclRing ℤp p)) * (tateBase (cyclRing ℤp p) p).Δ)),
        UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) h'
          (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) hc
          (t ^ (n + 1) + ∑ i ∈ Finset.range (n + 1),
            UnivBasisRing.ofBase p (c i) * UnivBasisRing.ofBase p d ^ (n + 1 - i) * t ^ i) = 0) :
    t ^ (n + 1) + ∑ i ∈ Finset.range (n + 1),
      algebraMap (UnivBase p) (UnivBasisRing p) (c i) * algebraMap (UnivBase p) (UnivBasisRing p) d ^ (n + 1 - i) * t ^ i = 0 := by
  set E : UnivBasisRing p := t ^ (n + 1) + ∑ i ∈ Finset.range (n + 1),
      UnivBasisRing.ofBase p (c i) * UnivBasisRing.ofBase p d ^ (n + 1 - i) * t ^ i with hE
  have hSI : SI p (((n + 1 : ℕ) : ℤ) * k) E := by
    refine (ht.pow (n + 1)).add (SI.sum _ _ _ fun i hi => ?_)
    have hi' : i ≤ n + 1 := (Finset.mem_range.mp hi).le
    refine (((hc i hi).mul (hd.pow (n + 1 - i))).mul (ht.pow i)).congr_weight ?_
    rw [Nat.cast_sub hi']
    push_cast
    ring
  have hBI : BI p E :=
    (htB.pow (n + 1)).add (BI.sum _ _ fun i _ =>
      ((BI_ofBase (c i)).mul ((BI_ofBase d).pow (n + 1 - i))).mul (htB.pow i))
  exact ModularCurve.YonedaInv.eq_zero_of_transfer hp5 _ E hSI hBI h0

end P8a
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"

end CMP
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"

namespace CMP

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_ofPowerSeries~coeffMap_jqModC~coeffMap_jqNModC~IsCusp P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.ModularCurve ModularCurve.LevelP HahnSeries Polynomial"

section Division

variable {p : ℕ} [Fact p.Prime]

theorem pDelta_ne_zero' : pDelta p ≠ 0 := by
  intro h
  let v : Fin 5 → ℤ := ![0, 0, 0, -1, 0]
  have hv := congrArg (MvPolynomial.eval v) h
  rw [pDelta, map_mul, map_natCast, map_zero, ← WeierstrassCurve.map_Δ] at hv
  have hcurve : genericCurve.map (MvPolynomial.eval v) = ⟨0, 0, 0, -1, 0⟩ := by
    simp [genericCurve, WeierstrassCurve.map, v]
  rw [hcurve] at hv
  have hΔ : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℤ).Δ = 64 := by
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
  rw [hΔ] at hv
  have : (p : ℤ) = 0 := by omega
  exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)

theorem isDomain_univBase : IsDomain (UnivBase p) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (UnivBase p)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero (pDelta_ne_zero' (p := p))))

theorem flat_univBase_univBasisRing (hp2 : p ≠ 2) : Module.Flat (UnivBase p) (UnivBasisRing p) :=
  ModularCurve.LevelP.BasisRing.flat (univCurve p) p ((Fact.out : p.Prime).odd_of_ne_two hp2)
    (Fact.out : p.Prime).one_lt.ne' (isUnit_natCast_univBase p)

theorem ofBase_mem_nonZeroDivisors (hp2 : p ≠ 2) {d : UnivBase p} (hd : d ≠ 0) :
    UnivBasisRing.ofBase p d ∈ nonZeroDivisors (UnivBasisRing p) := by
  haveI := isDomain_univBase (p := p)
  haveI := flat_univBase_univBasisRing (p := p) hp2
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := UnivBasisRing p)
    (mem_nonZeroDivisors_of_ne_zero hd)
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply hreg
  change d • x = d • (0 : UnivBasisRing p)
  rw [smul_zero, Algebra.smul_def, mul_comm]
  exact hx

theorem vc_ofBase_mul_cancel (hp2 : p ≠ 2) {d : UnivBase p} (hd : d ≠ 0) {a b : VCRing p}
    (h : VCRing.ofUniv p (UnivBasisRing.ofBase p d) * a = VCRing.ofUniv p (UnivBasisRing.ofBase p d) * b) :
    a = b := by
  haveI : Module.Flat (UnivBasisRing p) (VCRing p) := (ModularCurve.LevelP.flat_univBasisRing_vcRing_borelRing p).2.1
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := VCRing p) (ofBase_mem_nonZeroDivisors hp2 hd)
  apply hreg
  change UnivBasisRing.ofBase p d • a = UnivBasisRing.ofBase p d • b
  rw [Algebra.smul_def, Algebra.smul_def]
  exact h

theorem borel_ofBase_mul_cancel (hp2 : p ≠ 2) {d : UnivBase p} (hd : d ≠ 0) (a0 : ℕ) {a b : BorelRing p a0}
    (h : BorelRing.ofUniv p a0 (UnivBasisRing.ofBase p d) * a =
      BorelRing.ofUniv p a0 (UnivBasisRing.ofBase p d) * b) : a = b := by
  haveI : Module.Flat (UnivBasisRing p) (BorelRing p a0) :=
    (ModularCurve.LevelP.flat_univBasisRing_vcRing_borelRing p).2.2 a0
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := BorelRing p a0)
    (ofBase_mem_nonZeroDivisors hp2 hd)
  apply hreg
  change UnivBasisRing.ofBase p d • a = UnivBasisRing.ofBase p d • b
  rw [Algebra.smul_def, Algebra.smul_def]
  exact h

theorem SI.of_ofBase_mul (hp2 : p ≠ 2) {k : ℤ} {d : UnivBase p} (hd : d ≠ 0)
    (hd0 : SI p 0 (UnivBasisRing.ofBase p d)) {s : UnivBasisRing p}
    (h : SI p k (UnivBasisRing.ofBase p d * s)) : SI p k s := by
  intro g hW hD
  have h1 := h g hW hD
  have h2 := hd0 g hW hD
  rw [zpow_zero, Units.val_one, one_mul] at h2
  rw [map_mul, map_mul, h2] at h1
  refine vc_ofBase_mul_cancel hp2 hd ?_
  rw [h1]; ring

theorem BI.of_ofBase_mul (hp2 : p ≠ 2) {d : UnivBase p} (hd : d ≠ 0) {s : UnivBasisRing p}
    (h : BI p (UnivBasisRing.ofBase p d * s)) : BI p s := by
  intro a ha ha' g hW hD
  have h1 := h a ha ha' g hW hD
  have h2 := BI_ofBase d a ha ha' g hW hD
  rw [map_mul, map_mul, h2] at h1
  exact borel_ofBase_mul_cancel hp2 hd a h1

end Division
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"

section Cancel

variable {p : ℕ} [Fact p.Prime]

local notation "ℤp" => Localization.Away ((p : ℕ) : ℤ)

theorem aevalPoly_eq_eval₂_int {A : Type*} [CommRing A] (i : Algebra ℤ A) (x : A) (P : Polynomial ℤ) :
    @Polynomial.aeval ℤ A _ _ i x P = P.eval₂ (Int.castRingHom A) x := by
  rw [@Polynomial.aeval_def ℤ A _ _ i]
  congr 1
  exact RingHom.ext_int _ _

theorem mul_cancel_eval₂_jqN_of_injective (R : Type*) [CommRing R] (K : Type*) [Field K] [CharZero K]
    (ι : R →+* K) (hι : Function.Injective ι) (D : Polynomial ℤ) (hD : D ≠ 0)
    {x y : LaurentSeries R}
    (h : D.eval₂ (Int.castRingHom _) (jqNModC R p) * x = D.eval₂ (Int.castRingHom _) (jqNModC R p) * y) :
    x = y := by
  apply coeffMap_injective' ι hι
  have h2 := congrArg (coeffMap ι) h
  rw [map_mul, map_mul, Polynomial.hom_eval₂, coeffMap_jqNModC] at h2
  have hφ : (coeffMap ι).comp (Int.castRingHom (LaurentSeries R)) = Int.castRingHom _ := RingHom.ext_int _ _
  rw [hφ] at h2
  refine mul_left_cancel₀ ?_ h2
  intro h0
  have hT := ModularCurve.transcendental_jqNModC K p
  rw [transcendental_iff] at hT
  have h3 : Polynomial.aeval (jqNModC K p) (D.map (Int.castRingHom K)) =
      Polynomial.eval₂ (Int.castRingHom _) (jqNModC K p) D := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have h4 := hT _ (h3.trans h0)
  rw [Polynomial.map_eq_zero_iff (RingHom.injective_int (Int.castRingHom K))] at h4
  exact hD h4

theorem mul_cancel_aeval_jqN_of_injective (R : Type*) [CommRing R] (K : Type*) [Field K] [CharZero K]
    (ι : R →+* K) (hι : Function.Injective ι) (D : Polynomial ℤ) (hD : D ≠ 0)
    {x y : LaurentSeries R}
    (h : Polynomial.aeval (jqNModC R p) D * x = Polynomial.aeval (jqNModC R p) D * y) : x = y := by
  rw [aevalPoly_eq_eval₂_int] at h
  exact mul_cancel_eval₂_jqN_of_injective R K ι hι D hD h

theorem p_ne_zero_rat : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

noncomputable def zpToRat : ℤp →+* ℚ :=
  IsLocalization.Away.lift ((p : ℕ) : ℤ) (g := Int.castRingHom ℚ)
    (by rw [eq_intCast, Int.cast_natCast]; exact IsUnit.mk0 _ p_ne_zero_rat)

theorem zpToRat_injective : Function.Injective (zpToRat (p := p)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers ((p : ℕ) : ℤ)) x
  have h := (IsLocalization.lift_mk'_spec (S := ℤp) _ a (0 : ℚ) s).mp hx
  rw [mul_zero, eq_intCast, Int.cast_eq_zero] at h
  simp [h]

noncomputable def zpToC : ℤp →+* ℂ := (Rat.castHom ℂ).comp zpToRat

theorem zpToC_injective : Function.Injective (zpToC (p := p)) :=
  (Rat.castHom ℂ).injective.comp zpToRat_injective

@[reducible] noncomputable def algebraZpC : Algebra ℤp ℂ := (zpToC (p := p)).toAlgebra

noncomputable def zetaC : ℂˣ :=
  ((Complex.isPrimitiveRoot_exp p (Fact.out : p.Prime).ne_zero).isUnit (Fact.out : p.Prime).ne_zero).unit

theorem zetaC_spec : IsPrimitiveRoot ((zetaC (p := p) : ℂˣ) : ℂ) p := by
  rw [zetaC, IsUnit.unit_spec]; exact Complex.isPrimitiveRoot_exp p (Fact.out : p.Prime).ne_zero

theorem sum_zetaC_pow : ∑ i ∈ Finset.range p, ((zetaC (p := p) : ℂˣ) : ℂ) ^ i = 0 :=
  zetaC_spec.geom_sum_eq_zero (Fact.out : p.Prime).one_lt

noncomputable def cyclToC : cyclRing ℤp p →+* ℂ :=
  letI := algebraZpC (p := p)
  cyclSpec ℂ zetaC sum_zetaC_pow

theorem cyclToC_mk (q : Polynomial ℤp) :
    cyclToC (p := p) (AdjoinRoot.mk _ q) =
      (q.map zpToRat).eval₂ (Rat.castHom ℂ) ((zetaC (p := p) : ℂˣ) : ℂ) := by
  letI := algebraZpC (p := p)
  rw [cyclToC, cyclSpec, AdjoinRoot.lift_mk, Polynomial.eval₂_map]
  rfl

theorem cyclToC_injective : Function.Injective (cyclToC (p := p)) := by
  have hpr : p.Prime := Fact.out
  haveI : Nontrivial ℤp := (IsLocalization.isDomain_of_le_nonZeroDivisors ℤp
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero
      (by exact_mod_cast hpr.ne_zero : ((p : ℕ) : ℤ) ≠ 0)))).toNontrivial
  have hmonic : (Polynomial.cyclotomic p ℤp).Monic := Polynomial.cyclotomic.monic p ℤp
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x

  set q' := q %ₘ Polynomial.cyclotomic p ℤp with hq'
  have hqq' : AdjoinRoot.mk (Polynomial.cyclotomic p ℤp) q = AdjoinRoot.mk _ q' := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div q (Polynomial.cyclotomic p ℤp)]
    rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
  rw [hqq'] at hx ⊢
  rw [cyclToC_mk] at hx

  set g : Polynomial ℚ := q'.map zpToRat with hg
  set ζ : ℂ := ((zetaC (p := p) : ℂˣ) : ℂ) with hζ
  have hΦζ : (Polynomial.cyclotomic p ℚ).eval₂ (Rat.castHom ℂ) ζ = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact zetaC_spec.isRoot_cyclotomic hpr.pos
  have hdeg : g.degree < (Polynomial.cyclotomic p ℚ).degree := by
    calc g.degree ≤ q'.degree := Polynomial.degree_map_le
      _ < (Polynomial.cyclotomic p ℤp).degree := Polynomial.degree_modByMonic_lt q hmonic
      _ ≤ (Polynomial.cyclotomic p ℤ).degree := by
          rw [← Polynomial.map_cyclotomic_int]; exact Polynomial.degree_map_le
      _ = (Polynomial.cyclotomic p ℚ).degree := by
          rw [Polynomial.degree_cyclotomic, Polynomial.degree_cyclotomic]

  have hg0 : g = 0 := by
    by_contra hne
    have hirr := Polynomial.cyclotomic.irreducible_rat hpr.pos
    have hcop : IsCoprime (Polynomial.cyclotomic p ℚ) g := by
      rw [hirr.coprime_iff_not_dvd]
      intro hdvd
      exact (not_le.mpr hdeg) (Polynomial.degree_le_of_dvd hdvd hne)
    obtain ⟨a, b, hab⟩ := hcop
    have := congrArg (Polynomial.eval₂ (Rat.castHom ℂ) ζ) hab
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, hΦζ, hx, mul_zero,
      mul_zero, zero_add, Polynomial.eval₂_one] at this
    exact zero_ne_one this
  have hq0 : q' = 0 := by
    apply Polynomial.map_injective (zpToRat (p := p)) zpToRat_injective
    rw [← hg, hg0, Polynomial.map_zero]
  rw [hq0, map_zero]

theorem mul_cancel_aeval_jqN (D : Polynomial ℤ) (hD : D ≠ 0)
    {x y : LaurentSeries (cyclRing ℤp p)}
    (h : Polynomial.aeval (jqNModC (cyclRing ℤp p) p) D * x =
      Polynomial.aeval (jqNModC (cyclRing ℤp p) p) D * y) : x = y := by
  rw [aevalPoly_eq_eval₂_int] at h
  exact mul_cancel_eval₂_jqN_of_injective (cyclRing ℤp p) ℂ cyclToC cyclToC_injective D hD h

end Cancel
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"

end CMP
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"

namespace CMP

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_ofPowerSeries~coeffMap_jqModC~coeffMap_jqNModC~IsCusp P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.ModularCurve ModularCurve.LevelP HahnSeries Polynomial"

section CuspRelation

variable {p : ℕ} [Fact p.Prime]

theorem cusp_relation_eq_zero (hp2 : p ≠ 2) (R : Type*) [CommRing R] (hpR : IsUnit (p : R)) (ζ : Rˣ)
    (hc : IsLevelPStructure (tateBase R p) p (cuspData R p ζ ![1, 0] ![0, 1]))
    (h' : IsUnit ((p : LaurentSeries R) * (tateBase R p).Δ))
    (b : ℕ → ℤ) (N : MvPolynomial (Fin 2) ℤ) (D : Polynomial ℤ) (c : ℤ) (P : ℕ → MvPolynomial (Fin 2) ℤ)
    (hP0 : P 0 = MvPolynomial.C c)
    (hχ : ∑ r ∈ Finset.range (p + 2), (-1) ^ r *
        MvPolynomial.aeval ![qExpand R p (E4L R), qExpand R p (E6L R)] (P r) * Bq R b ^ (p + 1 - r) = 0)
    (hξ : PresentId R p N D b) :
    UnivBasisRing.classify p (tateBase R p) h' (cuspData R p ζ ![1, 0] ![0, 1]) hc
      (((c : UnivBasisRing p) * cand p N) ^ (p + 1) +
        ∑ i ∈ Finset.range (p + 1),
          UnivBasisRing.ofBase p ((-1) ^ (p + 1 - i) * (c : UnivBase p) ^ (p - i) *
              MvPolynomial.aeval ![(univCurve p).c₄, -(univCurve p).c₆] (P (p + 1 - i))) *
          UnivBasisRing.ofBase p (Polynomial.aeval (jU p) D) ^ (p + 1 - i) *
            ((c : UnivBasisRing p) * cand p N) ^ i) = 0 := by
  set cl := UnivBasisRing.classify p (tateBase R p) h' (cuspData R p ζ ![1, 0] ![0, 1]) hc with hcl
  set δ : LaurentSeries R := Polynomial.aeval (jqNModC R p) D with hδ
  set Q : ℕ → LaurentSeries R := fun r =>
    MvPolynomial.aeval ![qExpand R p (E4L R), qExpand R p (E6L R)] (P r) with hQ
  set B : LaurentSeries R := Bq R b with hB

  have hx : δ * B * ΔL R = MvPolynomial.aeval ![jqNModC R p, jqModC R] N * E4L R ^ 2 * E6L R := by
    have h0 : PresentId R p N D b := hξ
    delta PresentId at h0
    rw [aevalPoly_int_irrel (Ring.toIntAlgebra _) inferInstance,
      aeval_int_irrel (Ring.toIntAlgebra _) inferInstance] at h0
    exact h0
  have hcand : cl (cand p N) = δ * B := by
    rw [hcl, cl_cand R hpR _ hc h' hp2]
    calc MvPolynomial.aeval ![jqNModC R p, jqModC R] N * (E4L R ^ 2 * E6L R * Ring.inverse (ΔL R))
        = (MvPolynomial.aeval ![jqNModC R p, jqModC R] N * E4L R ^ 2 * E6L R) * Ring.inverse (ΔL R) := by
          ring
      _ = δ * B * (ΔL R * Ring.inverse (ΔL R)) := by rw [← hx]; ring
      _ = δ * B := by rw [Ring.mul_inverse_cancel _ (isUnit_ΔL R), mul_one]
  have hcoef : ∀ r : ℕ, cl (UnivBasisRing.ofBase p
      (MvPolynomial.aeval ![(univCurve p).c₄, -(univCurve p).c₆] (P r))) = Q r := by
    intro r
    rw [ofBase_aeval_c₄c₆, hcl, cl_aeval_c₄c₆ R _ hc h']
  have hd : cl (UnivBasisRing.ofBase p (Polynomial.aeval (jU p) D)) = δ := by
    rw [ofBase_aeval_jU, hcl, cl_aeval_jT R _ hc h']

  rw [map_add, map_sum]
  simp only [map_mul, map_pow, map_neg, map_one, map_intCast, hcoef, hd, hcand]

  have hS : ∑ r ∈ Finset.range (p + 1), (-1) ^ (r + 1) * Q (r + 1) * B ^ (p + 1 - (r + 1)) +
      (c : LaurentSeries R) * B ^ (p + 1) = 0 := by
    have h1 := hχ
    rw [Finset.sum_range_succ', hP0, MvPolynomial.aeval_C, eq_intCast (algebraMap ℤ (LaurentSeries R)) c,
      pow_zero, one_mul, Nat.sub_zero] at h1
    exact h1

  have hsum : ∑ i ∈ Finset.range (p + 1),
        (-1) ^ (p + 1 - i) * (c : LaurentSeries R) ^ (p - i) * Q (p + 1 - i) * δ ^ (p + 1 - i) *
          ((c : LaurentSeries R) * (δ * B)) ^ i =
      ∑ r ∈ Finset.range (p + 1),
        (c : LaurentSeries R) ^ p * δ ^ (p + 1) * ((-1) ^ (r + 1) * Q (r + 1) * B ^ (p + 1 - (r + 1))) := by
    refine (Finset.sum_range_reflect _ (p + 1)).symm.trans (Finset.sum_congr rfl fun r hr => ?_)
    have hr' : r < p + 1 := Finset.mem_range.mp hr
    have e1 : p + 1 - (p + 1 - 1 - r) = r + 1 := by omega
    have e2 : p - (p + 1 - 1 - r) = r := by omega
    have e3 : p + 1 - (r + 1) = p - r := by omega
    have e4 : p + 1 - 1 - r = p - r := by omega
    rw [e1, e2, e3, e4]
    have ec : (c : LaurentSeries R) ^ p = (c : LaurentSeries R) ^ r * (c : LaurentSeries R) ^ (p - r) := by
      rw [← _root_.pow_add]; congr 1; omega
    have eδ : δ ^ (p + 1) = δ ^ (r + 1) * δ ^ (p - r) := by
      rw [← _root_.pow_add]; congr 1; omega
    rw [ec, eδ, mul_pow, mul_pow]
    ring
  rw [hsum, ← Finset.mul_sum]
  have final : ((c : LaurentSeries R) * (δ * B)) ^ (p + 1) +
      (c : LaurentSeries R) ^ p * δ ^ (p + 1) *
        ∑ r ∈ Finset.range (p + 1), (-1) ^ (r + 1) * Q (r + 1) * B ^ (p + 1 - (r + 1)) =
      (c : LaurentSeries R) ^ p * δ ^ (p + 1) *
        (∑ r ∈ Finset.range (p + 1), (-1) ^ (r + 1) * Q (r + 1) * B ^ (p + 1 - (r + 1)) +
          (c : LaurentSeries R) * B ^ (p + 1)) := by
    ring
  rw [final, hS, mul_zero]

end CuspRelation
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"

end CMP
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"

namespace CMP

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_ofPowerSeries~coeffMap_jqModC~coeffMap_jqNModC~IsCusp P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.ModularCurve ModularCurve.LevelP HahnSeries"

section Final

variable {p : ℕ} [Fact p.Prime]

local notation "ℤp" => Localization.Away ((p : ℕ) : ℤ)

theorem SI.intCast_mul' {k : ℤ} {s : UnivBasisRing p} (h : SI p k s) (c : ℤ) : SI p k ((c : UnivBasisRing p) * s) := by
  intro g hW hD; rw [map_mul, map_intCast, h g hW hD, map_mul, map_intCast]; ring

theorem BI.intCast_mul' {s : UnivBasisRing p} (h : BI p s) (c : ℤ) : BI p ((c : UnivBasisRing p) * s) := by
  intro a ha ha' g hW hD; rw [map_mul, map_intCast, h a ha ha' g hW hD, map_mul, map_intCast]

theorem SI_aevalPoly_zero {s : UnivBasisRing p} (hs : SI p 0 s) (D : Polynomial ℤ) :
    SI p 0 (Polynomial.aeval s D) := by
  rw [SI.zero_iff_invariant] at hs ⊢
  intro g hW hD
  rw [map_aevalPoly_int, map_aevalPoly_int, hs g hW hD]

theorem nontrivial_cyclRing1 : Nontrivial (cyclRing ℤp p) := by
  have hpz : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI : IsDomain ℤp := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hpz)
  let pb := AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic p ℤp)
  haveI : Module.Free ℤp (cyclRing ℤp p) := Module.Free.of_basis pb.basis
  apply Module.nontrivial_of_finrank_pos (R := ℤp)
  rw [pb.finrank, AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_cyclotomic]
  have := (Fact.out : p.Prime).two_le
  have h : Nat.totient p = p - 1 := Nat.totient_prime (Fact.out)
  omega

variable (p) in

noncomputable def cfU (c : ℤ) (P : ℕ → MvPolynomial (Fin 2) ℤ) (i : ℕ) : UnivBase p :=
  (-1) ^ (p + 1 - i) * (c : UnivBase p) ^ (p - i) * MvPolynomial.aeval ![(univCurve p).c₄, -(univCurve p).c₆] (P (p + 1 - i))

theorem SI_cfU (c : ℤ) (P : ℕ → MvPolynomial (Fin 2) ℤ)
    (hPh : ∀ r : ℕ, (P r).IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) (2 * r)) :
    ∀ i ∈ Finset.range (p + 1), SI p ((p + 1 - i : ℕ) * 2) (UnivBasisRing.ofBase p (cfU p c P i)) := by
  intro i hi
  have h1 := SI_ofBase_aeval_weighted (p := p) (P (p + 1 - i)) (2 * (p + 1 - i)) (hPh _)
  have h2 : SI p 0 (UnivBasisRing.ofBase p ((-1) ^ (p + 1 - i) * (c : UnivBase p) ^ (p - i))) := by
    rw [SI.zero_iff_invariant]
    intro g hW hD
    simp only [map_mul, map_pow, map_neg, map_one, map_intCast]
  have h3 := h2.mul h1
  rw [← map_mul, zero_add] at h3
  have hk : (((2 * (p + 1 - i) : ℕ) : ℤ)) = ((p + 1 - i : ℕ) : ℤ) * 2 := by push_cast; ring
  rw [hk] at h3
  exact h3

theorem cusp_psi (hp5 : 5 ≤ p) (N : MvPolynomial (Fin 2) ℤ) (D : Polynomial ℤ) (hD : D ≠ 0) (c : ℤ) (b : ℕ → ℤ)
    (hξ : PresentId (cyclRing ℤp p) p N D b) (ψ : UnivBasisRing p)
    (hψ : (c : UnivBasisRing p) * cand p N = UnivBasisRing.ofBase p (Polynomial.aeval (jU p) D) * ψ) :
    UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) isUnit_p_mul_Δ_tateBase_cycl1
      (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) (isLevelPStructure_cusp1 hp5) ψ =
      (c : LaurentSeries _) * Bq _ b := by
  have hp2 : p ≠ 2 := by have := (Fact.out : p.Prime).two_le; omega
  have key : ∀ A : LaurentSeries (cyclRing ℤp p),
      A = @Polynomial.aeval ℤ _ _ _ (Ring.toIntAlgebra _) (jqNModC (cyclRing ℤp p) p) D →
      A * UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) isUnit_p_mul_Δ_tateBase_cycl1
          (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) (isLevelPStructure_cusp1 hp5) ψ =
        A * ((c : LaurentSeries _) * Bq _ b) := by
    intro A hA
    have hdU := cl_aeval_jT (cyclRing ℤp p) (cyclZeta ℤp p) (isLevelPStructure_cusp1 hp5)
      isUnit_p_mul_Δ_tateBase_cycl1 D
    rw [← ofBase_aeval_jU, aevalPoly_int_irrel _ (Ring.toIntAlgebra _) (jqNModC (cyclRing ℤp p) p) D, ← hA] at hdU
    rw [PresentId, ← hA] at hξ
    have hu := isUnit_ΔL (cyclRing ℤp p)
    have hN : @MvPolynomial.aeval ℤ _ (Fin 2) _ _ (Ring.toIntAlgebra _)
          ![jqNModC (cyclRing ℤp p) p, jqModC (cyclRing ℤp p)] N *
        (E4L (cyclRing ℤp p) ^ 2 * E6L (cyclRing ℤp p) * Ring.inverse (ΔL (cyclRing ℤp p))) = A * Bq _ b := by
      calc _ = (@MvPolynomial.aeval ℤ _ (Fin 2) _ _ (Ring.toIntAlgebra _)
              ![jqNModC (cyclRing ℤp p) p, jqModC (cyclRing ℤp p)] N *
              E4L (cyclRing ℤp p) ^ 2 * E6L (cyclRing ℤp p)) * Ring.inverse (ΔL (cyclRing ℤp p)) := by ring
        _ = (A * Bq _ b * ΔL _) * Ring.inverse (ΔL (cyclRing ℤp p)) := by rw [hξ]
        _ = A * Bq _ b := by rw [mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]
    calc A * _ = UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) isUnit_p_mul_Δ_tateBase_cycl1
            (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) (isLevelPStructure_cusp1 hp5)
            (UnivBasisRing.ofBase p (Polynomial.aeval (jU p) D) * ψ) := by rw [map_mul, hdU]
      _ = UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) isUnit_p_mul_Δ_tateBase_cycl1
            (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) (isLevelPStructure_cusp1 hp5)
            ((c : UnivBasisRing p) * cand p N) := by rw [hψ]
      _ = (c : LaurentSeries _) * (@MvPolynomial.aeval ℤ _ (Fin 2) _ _ (Ring.toIntAlgebra _)
              ![jqNModC (cyclRing ℤp p) p, jqModC (cyclRing ℤp p)] N *
            (E4L (cyclRing ℤp p) ^ 2 * E6L (cyclRing ℤp p) * Ring.inverse (ΔL (cyclRing ℤp p)))) := by
          rw [map_mul, map_intCast, cl_cand _ isUnit_p_cycl _ _ _ hp2, aeval_int_irrel _ (Ring.toIntAlgebra _)]
      _ = (c : LaurentSeries _) * (A * Bq _ b) := by rw [hN]
      _ = A * ((c : LaurentSeries _) * Bq _ b) := by ring
  exact mul_cancel_aeval_jqN D hD (key _ (aevalPoly_int_irrel _ _ (jqNModC (cyclRing ℤp p) p) D))

theorem exists_psi_proof (hp5 : 5 ≤ p) (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n) :
    ∃ (m : ℕ) (ψ : UnivBasisRing p), m ≠ 0 ∧ SI p 2 ψ ∧ BI p ψ ∧
      ∀ (hc : IsLevelPStructure (tateBase (cyclRing ℤp p) p) p
          (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]))
        (h' : IsUnit ((p : LaurentSeries (cyclRing ℤp p)) * (tateBase (cyclRing ℤp p) p).Δ)),
        UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) h'
          (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) hc ψ = (m : LaurentSeries _) * Bq _ b := by
  have hpr : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  haveI := nontrivial_cyclRing1 (p := p)

  obtain ⟨N, D, hD, hξQ⟩ := CMP.Present.exists_presentation h b hb
  obtain ⟨c, P, hc0, hP0, hPh, hχ⟩ :=
    ModularForm.exists_mvPolynomial_levelOne_relation_qExpansion_gamma0_of_weight_two p h b hb
  have hξ : PresentId (cyclRing ℤp p) p N D b := presentId_of_rat hξQ _

  have hdU : Polynomial.aeval (jU p) D ≠ 0 := by
    intro h0
    have h1 := cl_aeval_jT (cyclRing ℤp p) (cyclZeta ℤp p) (isLevelPStructure_cusp1 hp5) isUnit_p_mul_Δ_tateBase_cycl1 D
    rw [← ofBase_aeval_jU, h0, map_zero, map_zero,
      aevalPoly_int_irrel _ (Ring.toIntAlgebra _) (jqNModC (cyclRing ℤp p) p) D] at h1
    have : (1 : LaurentSeries (cyclRing ℤp p)) = 0 := mul_cancel_aeval_jqN D hD (by
      rw [aevalPoly_int_irrel _ (Ring.toIntAlgebra _) (jqNModC (cyclRing ℤp p) p) D, ← h1, zero_mul, zero_mul])
    exact one_ne_zero this

  have ht : SI p 2 ((c : UnivBasisRing p) * cand p N) := (SI_cand hp2 N).intCast_mul' c
  have htB : BI p ((c : UnivBasisRing p) * cand p N) := (BI_cand hp2 N).intCast_mul' c
  have hd0 : SI p 0 (UnivBasisRing.ofBase p (Polynomial.aeval (jU p) D)) := by
    rw [ofBase_aeval_jU]; exact SI_aevalPoly_zero SI_jT D

  have h0 := fun hc h' => cusp_relation_eq_zero hp2 (cyclRing ℤp p) isUnit_p_cycl (cyclZeta ℤp p) hc h' b N D c P hP0
    (hχ (cyclRing ℤp p)) hξ
  have hrel := pow_add_sum_eq_zero_of_cusp hp5 p 2 ((c : UnivBasisRing p) * cand p N) (Polynomial.aeval (jU p) D)
    (cfU p c P) ht htB hd0 (SI_cfU c P hPh) h0

  haveI := ModularCurve.LevelP.BasisRing.etale (univCurve p) (hpr.odd_of_ne_two hp2) (isUnit_natCast_mul_Δ_univCurve p)
  obtain ⟨hdom, hic⟩ := ModularCurve.LevelP.isDomain_and_isIntegrallyClosed_univBase p hpr.ne_zero
  obtain ⟨ψ, hψ⟩ := CMP.SmoothNormal.dvd_of_pow_add_sum_eq_zero (Polynomial.aeval (jU p) D) hdU _ p (cfU p c P) hrel

  have hψ' : (c : UnivBasisRing p) * cand p N = UnivBasisRing.ofBase p (Polynomial.aeval (jU p) D) * ψ := hψ
  have hψSI : SI p 2 ψ := SI.of_ofBase_mul hp2 hdU hd0 (hψ' ▸ ht)
  have hψBI : BI p ψ := BI.of_ofBase_mul hp2 hdU (hψ' ▸ htB)
  have hcusp := cusp_psi hp5 N D hD c b hξ ψ hψ'

  obtain ⟨n, hn | hn⟩ : ∃ n : ℕ, c = n ∨ c = -n := ⟨c.natAbs, Int.natAbs_eq c⟩
  · subst hn
    refine ⟨n, ψ, by exact_mod_cast hc0, hψSI, hψBI, fun hc h' => ?_⟩
    rw [Int.cast_natCast] at hcusp
    exact hcusp
  · subst hn
    refine ⟨n, -ψ, by simpa using hc0, hψSI.neg, hψBI.neg, fun hc h' => ?_⟩
    rw [Int.cast_neg, Int.cast_natCast, neg_mul] at hcusp
    rw [map_neg, neg_eq_iff_eq_neg]
    exact hcusp

end Final
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"

end CMP
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"

namespace CMP

variable {p : ℕ} [Fact p.Prime]

local notation "ℤp" => Localization.Away ((p : ℕ) : ℤ)

theorem exists_psi (hp5 : 5 ≤ p) (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n) :
    ∃ (m : ℕ) (ψ : UnivBasisRing p), m ≠ 0 ∧ SI p 2 ψ ∧ BI p ψ ∧
      ∀ (hc : IsLevelPStructure (tateBase (cyclRing ℤp p) p) p
          (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]))
        (h' : IsUnit ((p : LaurentSeries (cyclRing ℤp p)) * (tateBase (cyclRing ℤp p) p).Δ)),
        UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) h'
          (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) hc ψ = (m : LaurentSeries _) * Bq _ b :=
  exists_psi_proof hp5 h b hb

theorem descent (hp5 : 5 ≤ p) (b : ℕ → ℤ) (m : ℕ) (hm : m ≠ 0) (ψ : UnivBasisRing p)
    (hSI : SI p 2 ψ) (hBI : BI p ψ)
    (hcusp : ∀ (hc : IsLevelPStructure (tateBase (cyclRing ℤp p) p) p
          (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]))
        (h' : IsUnit ((p : LaurentSeries (cyclRing ℤp p)) * (tateBase (cyclRing ℤp p) p).Δ)),
        UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) h'
          (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) hc ψ = (m : LaurentSeries _) * Bq _ b) :
    ∃ s : UnivBasisRing p, SI p 2 s ∧ BI p s ∧
      ∀ (hc : IsLevelPStructure (tateBase (cyclRing ℤp p) p) p
          (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]))
        (h' : IsUnit ((p : LaurentSeries (cyclRing ℤp p)) * (tateBase (cyclRing ℤp p) p).Δ)),
        UnivBasisRing.classify p (tateBase (cyclRing ℤp p) p) h'
          (cuspData (cyclRing ℤp p) p (cyclZeta ℤp p) ![1, 0] ![0, 1]) hc s = Bq _ b := by
  obtain ⟨s, h1, h2, h3⟩ := descent_proof hp5 b m hm ψ hSI hBI (hcusp _ _)
  exact ⟨s, h1, h2, fun hc h' => h3⟩

theorem exists_cmpElt (hp5 : 5 ≤ p)
    (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n) :
    ∃ s : UnivBasisRing p, SI p 2 s ∧ BI p s ∧
      (∀ (R : Type) [CommRing R] [Algebra ℤp R] (ζ : Rˣ),
        ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0 →
        ∀ (hc : IsLevelPStructure (tateBase R p) p (cuspData R p ζ ![1, 0] ![0, 1]))
          (h' : IsUnit ((p : LaurentSeries R) * (tateBase R p).Δ)),
        UnivBasisRing.classify p (tateBase R p) h' (cuspData R p ζ ![1, 0] ![0, 1]) hc s = Bq R b) := by
  obtain ⟨m, ψ, hm, hSI, hBI, hcusp⟩ := exists_psi hp5 h b hb
  obtain ⟨s, hSI', hBI', hcusp'⟩ := descent hp5 b m hm ψ hSI hBI hcusp
  exact ⟨s, hSI', hBI', fun R _ _ ζ hζ hc h' => classify_cusp_eq_of_univ hp5 s b hcusp' R ζ hζ hc h'⟩

end CMP
p2m_reactivate "P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.CMP.Present"

theorem solution
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n) :
    ∃ φ : ModularCurve.KatzGamma0Form (Localization.Away (p : ℤ)) p 2,
      ∀ (R : Type) [CommRing R] [Algebra (Localization.Away (p : ℤ)) R] (ζ : Rˣ),
        ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0 →
        ∀ hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase R p) p
            (ModularCurve.cuspData R p ζ ![1, 0] ![0, 1]),
        φ.toKatzLevelPForm.toFun (ModularCurve.tateBase R p) (ModularCurve.isUnit_Δ_tateBase R p) _ hc
          = HahnSeries.ofPowerSeries ℤ R ((PowerSeries.mk b).map (Int.castRingHom R)) := by
  have hp2 : p ≠ 2 := by omega
  have hp : IsUnit ((p : ℕ) : Localization.Away (p : ℤ)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : ℤ)) (p : ℤ)
    simpa using this
  obtain ⟨s, hSI, hBI, hCUSP⟩ := CMP.exists_cmpElt hp5 h b hb
  obtain ⟨φ, -, hφ⟩ := CMP.P9 hp2 hp 2 s hSI hBI
  refine ⟨φ, fun R _ _ ζ hζ hc => ?_⟩
  have h' : IsUnit ((p : LaurentSeries R) * (tateBase R p).Δ) := by
    refine IsUnit.mul ?_ (isUnit_Δ_tateBase R p)
    simpa using (hp.map (algebraMap (Localization.Away (p : ℤ)) (LaurentSeries R)))
  rw [hφ (tateBase R p) (isUnit_Δ_tateBase R p) h' _ hc]
  exact hCUSP R ζ hζ hc h'

end S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le
end P2MW
export P2MW.S_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le (solution)
