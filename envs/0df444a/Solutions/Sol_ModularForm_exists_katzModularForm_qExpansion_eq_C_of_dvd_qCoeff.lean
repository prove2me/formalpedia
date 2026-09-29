-- Prove2me | solution 1 for ModularForm.exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b0232e60-01af-5fc8-8fb1-635042bc0163

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_KatzBaseChange
import Theorems.Thm_ModularForm_dvd_succ_mul_qCoeff_zero_of_dvd_qCoeff
import Theorems.Thm_KatzModularForm_exists_qExpansion_eq_C_of_dvd
import Theorems.Thm_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le
import Theorems.Thm_ModularCurve_KatzGamma0Form_exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_even_of_five_le
import Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le
import Theorems.Thm_KatzModularForm_toFun_tateBase_eq_qExpand_coeffMap_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff
p2m_attr_erase "instance" "ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing WeierstrassCurve.Generic.isElliptic_curve instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring"
p2m_attr_erase "instance" "AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.LevelP.instAlgebraTorusQRingTorusRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingTorusQRingTorusRing ModularCurve.LevelP.instAwayTorusQRingTorusDenomTorusRing ModularCurve.LevelP.instCommRingTorusRing ModularCurve.LevelP.instAlgebraUnivBasisRingTorusRing"
p2m_attr_erase "simp" "ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP"
p2m_attr_erase "simp" "ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP ModularCurve.LevelP.sClassify_tmul ModularCurve.LevelP.sLift_tmul WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.LevelPData.quotientBySndLine_swap ModularCurve.LevelP.smulX_one ModularCurve.LevelP.quotientByLine_a₃ ModularCurve.LevelP.quotientByLine_a₂ ModularCurve.LevelP.quotientByLine_a₁ ModularCurve.LevelPData.quotientByFstLine_swap ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def TateCurve.tateTorsionPoint_zero_zero ModularCurve.LevelP.TorusQRing.lift_yQ ModularCurve.LevelP.TorusQRing.lift_yP ModularCurve.LevelP.TorusQRing.lift_xQ ModularCurve.LevelP.TorusRing.lift_ofUniv ModularCurve.LevelP.TorusQRing.lift_xP ModularCurve.LevelP.TorusQRing.lift_ofUniv ModularCurve.LevelP.TorusRing.lift_algebraMap"

set_option autoImplicit false

open Polynomial

namespace KatzGlue

theorem algebraMap_cyclRing_injective (K : Type) [CommRing K] (p : ℕ) [hp : Fact p.Prime] :
    Function.Injective (algebraMap K (ModularCurve.cyclRing K p)) := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact Function.injective_of_subsingleton _
  · refine (injective_iff_map_eq_zero _).mpr fun r hr => ?_
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at hr
    by_contra hr0
    have hlt : (C r).natDegree < (cyclotomic p K).natDegree := by
      rw [natDegree_C, natDegree_cyclotomic]
      exact Nat.totient_pos.mpr hp.out.pos
    exact (cyclotomic.monic p K).not_dvd_of_natDegree_lt (C_ne_zero.mpr hr0) hlt hr

theorem coeffMap_injective {R S : Type} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (ModularCurve.coeffMap f) := by
  intro x y h
  ext k
  exact hf (by simpa only [ModularCurve.coeffMap_coeff] using congrArg (fun s => HahnSeries.coeff s k) h)

theorem coeffMap_C {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    ModularCurve.coeffMap f (HahnSeries.C r) = HahnSeries.C (f r) := by
  rw [HahnSeries.C_apply, ModularCurve.coeffMap_single, HahnSeries.C_apply]

theorem qTwist_C {R : Type} [CommRing R] (u : Rˣ) (r : R) :
    ModularCurve.qTwist u (HahnSeries.C r) = HahnSeries.C r := by
  rw [HahnSeries.C_apply, ModularCurve.qTwist_single, zpow_zero, Units.val_one, one_mul]

theorem map_mk_eq_C_of_dvd (m : ℕ) (R : Type) [CommRing R] [Algebra (ZMod m) R] (b : ℕ → ℤ)
    (hdvd : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ b n) :
    (PowerSeries.mk b).map (Int.castRingHom R)
      = PowerSeries.C (algebraMap (ZMod m) R ((b 0 : ℤ) : ZMod m)) := by
  ext n
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_C, eq_intCast]
  split_ifs with hn
  · subst hn; rw [map_intCast]
  · obtain ⟨d, hd⟩ := hdvd n hn
    rw [hd, ← map_intCast (algebraMap (ZMod m) R), Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, map_zero]

theorem div_gcd_dvd_of_dvd_mul (a k : ℕ) (hk : 0 < k) (c : ℤ) (h : (a : ℤ) ∣ k * c) :
    ((a / Nat.gcd a k : ℕ) : ℤ) ∣ c := by
  obtain ⟨g, a', k', hg, hcop, rfl, rfl⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_right a hk)
  rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul, Nat.mul_div_cancel _ hg]
  have h' : (a' : ℤ) * g ∣ (k' * c) * g := by
    have : ((a' * g : ℕ) : ℤ) ∣ ((k' * g : ℕ) : ℤ) * c := h
    push_cast at this
    rwa [mul_right_comm] at this
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  exact (Nat.isCoprime_iff_coprime.mpr hcop).dvd_of_dvd_mul_left ((mul_dvd_mul_iff_right hg0).mp h')

end KatzGlue

p2m_open "ModularCurve~coeffMap_injective" in
theorem solution (p : ℕ) [Fact p.Prime]
    (m : ℕ) (hm : p.Coprime m) (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n)
    (hdvd : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ b n) :
    ∃ F : KatzModularForm (ZMod m) 2, F.qExpansion = HahnSeries.C ((b 0 : ℤ) : ZMod m) := by
  by_cases hp23 : p = 2 ∨ p = 3
  ·
    have hrel := ModularForm.dvd_succ_mul_qCoeff_zero_of_dvd_qCoeff p m hm.symm h b hb hdvd
    refine KatzModularForm.exists_qExpansion_eq_C_of_dvd m (b 0) ?_
    rcases hp23 with rfl | rfl
    · have h3 : ((m : ℕ) : ℤ) ∣ (3 : ℕ) * b 0 := by convert hrel using 2 <;> norm_num
      have hg : Nat.gcd m 12 = Nat.gcd m 3 := by
        have h4 : Nat.Coprime 4 m := by simpa using hm.pow_left 2
        simpa using h4.gcd_mul_right_cancel_right 3
      rw [hg]; exact KatzGlue.div_gcd_dvd_of_dvd_mul m 3 (by norm_num) (b 0) h3
    · have h4 : ((m : ℕ) : ℤ) ∣ (4 : ℕ) * b 0 := by convert hrel using 2 <;> norm_num
      have hg : Nat.gcd m 12 = Nat.gcd m 4 := by
        simpa using hm.gcd_mul_right_cancel_right 4
      rw [hg]; exact KatzGlue.div_gcd_dvd_of_dvd_mul m 4 (by norm_num) (b 0) h4
  ·
    obtain ⟨hp2, hp3⟩ := not_or.mp hp23
    have hp5 : 5 ≤ p := by
      have h2 := (Fact.out : p.Prime).two_le
      have h4 : p ≠ 4 := by rintro rfl; exact absurd (Fact.out : Nat.Prime 4) (by decide)
      omega
    have hpK : IsUnit ((p : ℕ) : ZMod m) := (ZMod.isUnit_iff_coprime p m).mpr hm

    obtain ⟨φ, hφ⟩ := ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le hp5 h b hb

    letI : Algebra (Localization.Away (p : ℤ)) (ZMod m) :=
      (Localization.awayLift (Int.castRingHom (ZMod m)) (p : ℤ) (by simpa using hpK)).toAlgebra
    haveI hST := IsScalarTower.of_algebraMap_eq (R := Localization.Away (p : ℤ)) (S := ZMod m)
      (A := LaurentSeries (cyclRing (ZMod m) p)) fun r => by
        rw [ModularCurve.algebraMap_laurentSeries_apply (Localization.Away (p : ℤ)) r,
          ModularCurve.algebraMap_laurentSeries_apply (ZMod m),
          ← IsScalarTower.algebraMap_apply (Localization.Away (p : ℤ)) (ZMod m) (cyclRing (ZMod m) p) r]

    have hpR : IsUnit ((p : ℕ) : cyclRing (ZMod m) p) := by
      simpa using hpK.map (algebraMap (ZMod m) (cyclRing (ZMod m) p))
    have hc : IsLevelPStructure (tateBase (cyclRing (ZMod m) p) p) p
        (cuspData (cyclRing (ZMod m) p) p (cyclZeta (ZMod m) p) ![1, 0] ![0, 1]) :=
      ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le hp5 hpR (cyclZeta (ZMod m) p)
        (sum_cyclZeta_pow_eq_zero (ZMod m) p) 1 one_ne_zero

    have hval : (φ.baseChange (ZMod m)).toKatzLevelPForm.toFun (tateBase (cyclRing (ZMod m) p) p)
          (isUnit_Δ_tateBase (cyclRing (ZMod m) p) p) _ hc
        = HahnSeries.C (algebraMap (ZMod m) (cyclRing (ZMod m) p) ((b 0 : ℤ) : ZMod m)) := by
      rw [KatzGamma0Form.baseChange_toKatzLevelPForm, KatzLevelPForm.baseChange_toFun,
        hφ (cyclRing (ZMod m) p) (cyclZeta (ZMod m) p) (sum_cyclZeta_pow_eq_zero (ZMod m) p) hc,
        KatzGlue.map_mk_eq_C_of_dvd m (cyclRing (ZMod m) p) b hdvd, HahnSeries.ofPowerSeries_C]

    have hσ : qTwist (cyclZeta (ZMod m) p)
        ((φ.baseChange (ZMod m)).toFun (tateBase (cyclRing (ZMod m) p) p)
          (isUnit_Δ_tateBase (cyclRing (ZMod m) p) p) _ hc)
        = (φ.baseChange (ZMod m)).toFun (tateBase (cyclRing (ZMod m) p) p)
          (isUnit_Δ_tateBase (cyclRing (ZMod m) p) p) _ hc := by
      show qTwist _ ((φ.baseChange (ZMod m)).toKatzLevelPForm.toFun _ _ _ hc)
        = (φ.baseChange (ZMod m)).toKatzLevelPForm.toFun _ _ _ hc
      rw [hval, KatzGlue.qTwist_C]
    obtain ⟨g, hg⟩ :=
      ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_even_of_five_le
        hp5 hpK even_two (φ.baseChange (ZMod m)) hc hσ

    refine ⟨g, ?_⟩
    have h1 : g.toFun (tateBase (cyclRing (ZMod m) p) p) (isUnit_Δ_tateBase (cyclRing (ZMod m) p) p)
        = HahnSeries.C (algebraMap (ZMod m) (cyclRing (ZMod m) p) ((b 0 : ℤ) : ZMod m)) := by
      have := congrArg (fun F : KatzLevelPForm (ZMod m) p 2 =>
        F.toFun (tateBase (cyclRing (ZMod m) p) p) (isUnit_Δ_tateBase (cyclRing (ZMod m) p) p) _ hc) hg
      simpa only [KatzModularForm.pullbackLevelP_toFun, hval] using this
    have h2 := KatzModularForm.toFun_tateBase_eq_qExpand_coeffMap_qExpansion g (cyclRing (ZMod m) p) p
    apply KatzGlue.coeffMap_injective (KatzGlue.algebraMap_cyclRing_injective (ZMod m) p)
    refine qExpand_injective p ?_
    rw [← h2, h1, KatzGlue.coeffMap_C, qExpand_C]

end S_ModularForm_exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff
end P2MW
export P2MW.S_ModularForm_exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff (solution)
