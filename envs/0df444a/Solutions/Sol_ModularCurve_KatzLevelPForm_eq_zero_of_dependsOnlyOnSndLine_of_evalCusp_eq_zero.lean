-- Prove2me | solution 1 for ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/61bc5b82-3414-5c79-a8e4-88dac2fcfe5d

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field
import Theorems.Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_forall_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.Generic.isElliptic_curve instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing"
p2m_attr_erase "instance" "ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Universal.halveX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint"
p2m_attr_erase "simp" "ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

noncomputable section

p2m_open "WeierstrassCurve~cusp"

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData IsLevelPStructure KatzLevelPForm KatzLevelPForm.ext KatzLevelPForm.toFun cuspData algebraMap_laurentSeries_apply isUnit_Δ_tateBase tateBase"
namespace KatzLevelPForm
p2m_export "ModularCurve.KatzLevelPForm" "ext zero_toFun DependsOnlyOnSndLine toFun map_toFun toFun_variableChange eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_forall_field"
namespace QExpRingReduction
p2m_open "ModularCurve.KatzLevelPForm ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.ModularCurve"

variable {R₀ : Type u} [CommRing R₀] {p : ℕ} {k : ℤ}

theorem toFun_congr_inst (G : KatzLevelPForm R₀ p k) {A : Type u} [CommRing A]
    (i₁ i₂ : Algebra R₀ A) (h : i₁ = i₂) (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D : LevelPData A) (hD : IsLevelPStructure W p D) :
    @KatzLevelPForm.toFun R₀ _ p k G A _ i₁ W hW D hD =
      @KatzLevelPForm.toFun R₀ _ p k G A _ i₂ W hW D hD := by
  subst h
  rfl

theorem map_toFun' (G : KatzLevelPForm R₀ p k) {A B : Type u} [CommRing A] [Algebra R₀ A]
    [CommRing B] [Algebra R₀ B] (f : A →ₐ[R₀] B) (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D : LevelPData A) (hD : IsLevelPStructure W p D) :
    f (G.toFun W hW D hD) = G.toFun (W.map (f : A →+* B)) (KatzModularForm.isUnit_Δ_map _ hW)
      (D.map (f : A →+* B)) (hD.map _) :=
  (G.map_toFun f W hW _ D hD _).symm

theorem eq_zero_of_faithfullyFlat (R : Type u) [CommRing R] [Algebra R₀ R]
    [Module.FaithfullyFlat R₀ R] (G : KatzLevelPForm R₀ p k)
    (h : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R₀ A] [Algebra R A] [IsScalarTower R₀ R A]
      (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A) (hD : IsLevelPStructure W p D),
      G.toFun W hW D hD = 0) :
    G = 0 := by
  refine KatzLevelPForm.ext fun A _ _ W hW D hD => ?_
  let f : A →ₐ[R₀] TensorProduct R₀ R A := Algebra.TensorProduct.includeRight
  have hf : Function.Injective f := by
    intro a b hab
    exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R₀) (B := R) A hab
  let f' : A →+* TensorProduct R₀ R A := f
  have key : f (G.toFun W hW D hD) =
      G.toFun (W.map f') (KatzModularForm.isUnit_Δ_map _ hW) (D.map f') (hD.map _) :=
    map_toFun' G f W hW D hD
  have h2 := h (W.map f') (KatzModularForm.isUnit_Δ_map _ hW) (D.map f') (hD.map _)
  rw [h2] at key
  rw [zero_toFun]
  exact hf (by rw [key, map_zero])

section Restrict

variable (R : Type u) [CommRing R] [Algebra R₀ R]

@[reducible] def compAlgebra (A : Type u) [CommRing A] [Algebra R A] : Algebra R₀ A :=
  ((algebraMap R A).comp (algebraMap R₀ R)).toAlgebra

theorem compAlgebra_isScalarTower (A : Type u) [CommRing A] [Algebra R A] :
    letI := compAlgebra (R₀ := R₀) R A
    IsScalarTower R₀ R A :=
  letI := compAlgebra (R₀ := R₀) R A
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem compAlgebra_eq (A : Type u) [CommRing A] [Algebra R A] [i : Algebra R₀ A]
    [IsScalarTower R₀ R A] : compAlgebra (R₀ := R₀) R A = i := by
  refine Algebra.algebra_ext _ _ fun r => ?_
  exact (IsScalarTower.algebraMap_apply R₀ R A r).symm

def restrict (G : KatzLevelPForm R₀ p k) : KatzLevelPForm R p k where
  toFun A _ _ W hW D hD :=
    letI := compAlgebra (R₀ := R₀) R A
    G.toFun W hW D hD
  map_toFun := by
    intro A B _ _ _ _ f W hW hW' D hD hD'
    letI := compAlgebra (R₀ := R₀) R A
    letI := compAlgebra (R₀ := R₀) R B
    haveI := compAlgebra_isScalarTower (R₀ := R₀) R A
    haveI := compAlgebra_isScalarTower (R₀ := R₀) R B
    exact G.map_toFun (f.restrictScalars R₀) W hW hW' D hD hD'
  toFun_variableChange := by
    intro A _ _ C W hW hW' D hD hD'
    letI := compAlgebra (R₀ := R₀) R A
    exact G.toFun_variableChange C W hW hW' D hD hD'

theorem restrict_toFun (G : KatzLevelPForm R₀ p k) {A : Type u} [CommRing A] [Algebra R A]
    [Algebra R₀ A] [IsScalarTower R₀ R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D : LevelPData A) (hD : IsLevelPStructure W p D) :
    (restrict R G).toFun W hW D hD = G.toFun W hW D hD := by
  show @KatzLevelPForm.toFun R₀ _ p k G A _ (compAlgebra (R₀ := R₀) R A) W hW D hD = _
  exact toFun_congr_inst G _ _ (compAlgebra_eq (R₀ := R₀) R A) W hW D hD

theorem dependsOnlyOnSndLine_restrict {G : KatzLevelPForm R₀ p k} (hG : G.DependsOnlyOnSndLine) :
    (restrict R G).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  letI := compAlgebra (R₀ := R₀) R A
  exact hG W hW D D' hD hD' hQ

theorem eq_zero_of_restrict_eq_zero [Module.FaithfullyFlat R₀ R] (G : KatzLevelPForm R₀ p k)
    (h : restrict R G = 0) : G = 0 := by
  refine eq_zero_of_faithfullyFlat R G fun A _ _ _ _ W hW D hD => ?_
  rw [← restrict_toFun R G W hW D hD, h, zero_toFun]

scoped instance instIsScalarTowerLaurentSeries :
    @IsScalarTower R₀ R (LaurentSeries R) Algebra.toSMul
      (HahnSeries.powerSeriesAlgebra ℤ R (S := R)).toSMul
      (HahnSeries.powerSeriesAlgebra ℤ R (S := R₀)).toSMul :=
  @IsScalarTower.of_algebraMap_eq R₀ R (LaurentSeries R) _ _ _ _
    (HahnSeries.powerSeriesAlgebra ℤ R (S := R)) (HahnSeries.powerSeriesAlgebra ℤ R (S := R₀)) fun r => by
    rw [algebraMap_laurentSeries_apply R₀ (R := R) r,
      algebraMap_laurentSeries_apply R (R := R) (algebraMap R₀ R r), Algebra.algebraMap_self,
      RingHom.id_apply]

end Restrict

end ModularCurve.KatzLevelPForm.QExpRingReduction
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.ModularCurve.KatzLevelPForm P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.ModularCurve.KatzLevelPForm.QExpRingReduction"
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.ModularCurve.KatzLevelPForm"
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.ModularCurve.KatzLevelPForm P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.ModularCurve.KatzLevelPForm.QExpRingReduction"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.ModularCurve _root_.ModularCurve.KatzLevelPForm _root_.P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.ModularCurve.KatzLevelPForm ModularCurve.KatzLevelPForm.QExpRingReduction in
theorem solution
    {R₀ : Type u} [CommRing R₀] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R₀))
    (R : Type u) [CommRing R] [Algebra R₀ R] [Module.FaithfullyFlat R₀ R]
    (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) {k : ℤ}
    (hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase R p) p (ModularCurve.cuspData R p ζ ![1, 0] ![0, 1]))
    (G : ModularCurve.KatzLevelPForm R₀ p k) (hG : G.DependsOnlyOnSndLine)
    (h0 : G.toFun (ModularCurve.tateBase R p) (ModularCurve.isUnit_Δ_tateBase R p) _ hc = 0) : G = 0 := by

  refine eq_zero_of_restrict_eq_zero R G ?_
  have hpR : IsUnit (p : R) := by simpa using hp.map (algebraMap R₀ R)
  have h0R : (restrict R G).toFun (ModularCurve.tateBase R p) (ModularCurve.isUnit_Δ_tateBase R p)
      _ hc = 0 := by
    rw [restrict_toFun]
    exact h0

  exact eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_forall_field hp2 hpR ζ hζ hc
    (restrict R G) (dependsOnlyOnSndLine_restrict R hG) h0R
    fun K _ hpK ξ hcK H hH hH0 =>
      eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field hp2 hpK ξ hcK H hH hH0

end S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero
end P2MW
export P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero (solution)
