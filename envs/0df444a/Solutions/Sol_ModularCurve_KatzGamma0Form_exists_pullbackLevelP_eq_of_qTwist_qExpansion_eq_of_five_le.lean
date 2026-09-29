-- Prove2me | solution 1 for ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/78780a9f-35b6-57cf-a20f-b09cc86a81ab

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_isLevelPStructure_cuspData
import Theorems.Thm_ModularCurve_cuspData_map_qTwist
import Theorems.Thm_ModularCurve_inLine_cuspData_smul_of_five_le
import Theorems.Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_forall_evalCusp_eq_zero
import Theorems.Thm_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_KatzGamma0Form_exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Generic.isElliptic_curve AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing"
p2m_attr_erase "instance" "ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing ModularCurve.LevelP.instAlgebraTorusQRingTorusRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingTorusQRingTorusRing ModularCurve.LevelP.instAwayTorusQRingTorusDenomTorusRing ModularCurve.LevelP.instCommRingTorusRing ModularCurve.LevelP.instAlgebraUnivBasisRingTorusRing"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint"
p2m_attr_erase "simp" "ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP ModularCurve.LevelP.TorusQRing.lift_yQ ModularCurve.LevelP.TorusQRing.lift_yP ModularCurve.LevelP.TorusQRing.lift_xQ ModularCurve.LevelP.TorusRing.lift_ofUniv ModularCurve.LevelP.TorusQRing.lift_xP ModularCurve.LevelP.TorusQRing.lift_ofUniv ModularCurve.LevelP.TorusRing.lift_algebraMap"

set_option autoImplicit false

universe u

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData IsLevelPStructure KatzLevelPForm KatzLevelPForm.sub_toFun KatzLevelPForm.swap_toFun KatzLevelPForm.swapInvariant_iff_swap_eq KatzGamma0Form cuspData cuspData_swap cuspShift cuspShift_zero cuspShift_one qTwistAlgHom qTwistAlgHom_apply coe_qTwistAlgHom tateBase_map_qTwist isUnit_Δ_tateBase cyclRing cyclZeta cyclZeta_pow_eq_one sum_cyclZeta_pow_eq_zero tateBase qTwist isLevelPStructure_cuspData cuspData_map_qTwist inLine_cuspData_smul_of_five_le KatzLevelPForm.eq_zero_of_dependsOnlyOnLines_of_forall_evalCusp_eq_zero KatzLevelPForm.existsUnique_pullbackLevelP_eq_of_swapInvariant"
p2m_open "ModularCurve"

p2m_open "ModularCurve.KatzLevelPForm P2MW.S_ModularCurve_KatzGamma0Form_exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le.ModularCurve.KatzLevelPForm"

section Cycl

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]

theorem cyclRing_faithfullyFlat (hp2 : p ≠ 2) : Module.FaithfullyFlat R (cyclRing R p) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton (cyclRing R p) := (algebraMap R (cyclRing R p)).codomain_trivial
    rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
    exact ⟨inferInstance, fun I hI => absurd (Subsingleton.elim I ⊤) hI⟩
  · let pb := AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic p R)
    haveI : Module.Free R (cyclRing R p) := Module.Free.of_basis pb.basis
    haveI : Nontrivial (cyclRing R p) := by
      apply Module.nontrivial_of_finrank_pos (R := R)
      rw [pb.finrank, AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_cyclotomic]
      have := (Fact.out : p.Prime).two_le
      have h : Nat.totient p = p - 1 := Nat.totient_prime (Fact.out)
      omega
    infer_instance

end Cycl

section Values

variable {R₀ : Type u} [CommRing R₀] {p : ℕ} [Fact p.Prime] {k : ℤ} (F : KatzLevelPForm R₀ p k)
  (R : Type u) [CommRing R] [Algebra R₀ R] (ζ : Rˣ)

namespace KatzLevelPForm p2m_export "ModularCurve.KatzLevelPForm" "ext sub_toFun swap swap_toFun SwapInvariant swapInvariant_iff_swap_eq toFun map_toFun eq_zero_of_dependsOnlyOnLines_of_forall_evalCusp_eq_zero existsUnique_pullbackLevelP_eq_of_swapInvariant" end KatzLevelPForm
namespace KatzLevelPForm
p2m_open_scoped "ModularCurve.KatzLevelPForm" in
private theorem _root_.ModularCurve.KatzLevelPForm.toFun_congr_all {W W' : WeierstrassCurve (LaurentSeries R)} (hWW' : W = W') (hW : IsUnit W.Δ)
    (hW' : IsUnit W'.Δ) {D D' : LevelPData (LaurentSeries R)} (h : D = D') (hD : IsLevelPStructure W p D)
    (hD' : IsLevelPStructure W' p D') : F.toFun W hW D hD = F.toFun W' hW' D' hD' := by
  subst hWW' h; rfl

end KatzLevelPForm
p2m_export "ModularCurve" "KatzLevelPForm.toFun_congr_all"
namespace KatzLevelPForm
p2m_open_scoped "ModularCurve.KatzLevelPForm" in
private theorem _root_.ModularCurve.KatzLevelPForm.toFun_congr_data {W : WeierstrassCurve (LaurentSeries R)} (hW : IsUnit W.Δ)
    {D D' : LevelPData (LaurentSeries R)} (h : D = D') (hD : IsLevelPStructure W p D)
    (hD' : IsLevelPStructure W p D') : F.toFun W hW D hD = F.toFun W hW D' hD' := by
  subst h; rfl

end KatzLevelPForm
p2m_export "ModularCurve" "KatzLevelPForm.toFun_congr_data"
namespace KatzLevelPForm
p2m_open_scoped "ModularCurve.KatzLevelPForm" in

private theorem _root_.ModularCurve.KatzLevelPForm.toFun_cuspShift (hζp : ζ ^ p = 1) (v w : Fin 2 → ZMod p)
    (h : IsLevelPStructure (tateBase R p) p (cuspData R p ζ v w))
    (h' : IsLevelPStructure (tateBase R p) p (cuspData R p ζ (cuspShift p v) (cuspShift p w))) :
    F.toFun (tateBase R p) (isUnit_Δ_tateBase R p) (cuspData R p ζ (cuspShift p v) (cuspShift p w)) h' =
      qTwist ζ (F.toFun (tateBase R p) (isUnit_Δ_tateBase R p) (cuspData R p ζ v w) h) := by
  have hc : (tateBase R p).map ((qTwistAlgHom R₀ ζ : LaurentSeries R →ₐ[R₀] LaurentSeries R) :
      LaurentSeries R →+* LaurentSeries R) = tateBase R p := by
    rw [coe_qTwistAlgHom, tateBase_map_qTwist p ζ hζp]
  have hd : (cuspData R p ζ v w).map ((qTwistAlgHom R₀ ζ : LaurentSeries R →ₐ[R₀] LaurentSeries R) :
      LaurentSeries R →+* LaurentSeries R) = cuspData R p ζ (cuspShift p v) (cuspShift p w) := by
    rw [coe_qTwistAlgHom, cuspData_map_qTwist ζ hζp]
  have hW' : IsUnit ((tateBase R p).map ((qTwistAlgHom R₀ ζ : LaurentSeries R →ₐ[R₀] LaurentSeries R) :
      LaurentSeries R →+* LaurentSeries R)).Δ := by rw [hc]; exact isUnit_Δ_tateBase R p
  have hD' : IsLevelPStructure ((tateBase R p).map ((qTwistAlgHom R₀ ζ : LaurentSeries R →ₐ[R₀] LaurentSeries R) :
      LaurentSeries R →+* LaurentSeries R)) p ((cuspData R p ζ v w).map
      ((qTwistAlgHom R₀ ζ : LaurentSeries R →ₐ[R₀] LaurentSeries R) : LaurentSeries R →+* LaurentSeries R)) := by
    rw [hc, hd]; exact h'
  have key := F.map_toFun (qTwistAlgHom R₀ ζ) (tateBase R p) (isUnit_Δ_tateBase R p) hW'
    (cuspData R p ζ v w) h hD'
  rw [qTwistAlgHom_apply] at key
  rw [← key]
  exact F.toFun_congr_all R hc.symm (isUnit_Δ_tateBase R p) hW' hd.symm h' hD'

end KatzLevelPForm
p2m_export "ModularCurve" "KatzLevelPForm.toFun_cuspShift"

theorem det_cuspShift (v w : Fin 2 → ZMod p) :
    cuspShift p v 0 * cuspShift p w 1 - cuspShift p v 1 * cuspShift p w 0 = v 0 * w 1 - v 1 * w 0 := by
  simp only [cuspShift_zero, cuspShift_one]; ring

theorem det_cuspShift_iterate (n : ℕ) (v w : Fin 2 → ZMod p) :
    ((cuspShift p)^[n] v) 0 * ((cuspShift p)^[n] w) 1 - ((cuspShift p)^[n] v) 1 * ((cuspShift p)^[n] w) 0 =
      v 0 * w 1 - v 1 * w 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', det_cuspShift, ih]

namespace KatzLevelPForm
p2m_open_scoped "ModularCurve.KatzLevelPForm" in

private theorem _root_.ModularCurve.KatzLevelPForm.toFun_cuspShift_iterate (hζp : ζ ^ p = 1)
    (hall : ∀ v w : Fin 2 → ZMod p, v 0 * w 1 - v 1 * w 0 ≠ 0 →
      IsLevelPStructure (tateBase R p) p (cuspData R p ζ v w))
    (n : ℕ) (v w : Fin 2 → ZMod p) (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0)
    (h : IsLevelPStructure (tateBase R p) p (cuspData R p ζ v w))
    (h' : IsLevelPStructure (tateBase R p) p
      (cuspData R p ζ ((cuspShift p)^[n] v) ((cuspShift p)^[n] w))) :
    F.toFun (tateBase R p) (isUnit_Δ_tateBase R p) (cuspData R p ζ ((cuspShift p)^[n] v) ((cuspShift p)^[n] w)) h' =
      (qTwist ζ)^[n] (F.toFun (tateBase R p) (isUnit_Δ_tateBase R p) (cuspData R p ζ v w) h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : IsLevelPStructure (tateBase R p) p
        (cuspData R p ζ ((cuspShift p)^[n] v) ((cuspShift p)^[n] w)) :=
      hall _ _ (by rw [det_cuspShift_iterate]; exact hvw)
    have hidx : cuspData R p ζ ((cuspShift p)^[n+1] v) ((cuspShift p)^[n+1] w) =
        cuspData R p ζ (cuspShift p ((cuspShift p)^[n] v)) (cuspShift p ((cuspShift p)^[n] w)) := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have step := F.toFun_cuspShift R ζ hζp ((cuspShift p)^[n] v) ((cuspShift p)^[n] w) hn (hidx ▸ h')
    rw [F.toFun_congr_data R (isUnit_Δ_tateBase R p) hidx h' (hidx ▸ h'), step,
      Function.iterate_succ_apply' (⇑(qTwist ζ)) n, ih hn]

end KatzLevelPForm
p2m_export "ModularCurve" "KatzLevelPForm.toFun_cuspShift_iterate"
end Values

section Indices

variable (p : ℕ) [Fact p.Prime]

theorem cuspShift_iterate_toric (n : ℕ) : (cuspShift p)^[n] ![1, 0] = ![1, 0] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    ext i; fin_cases i <;> simp [cuspShift]

theorem cuspShift_iterate_qPoint (n : ℕ) : (cuspShift p)^[n] ![0, 1] = ![(n : ZMod p), 1] := by
  induction n with
  | zero => ext i; fin_cases i <;> simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    ext i; fin_cases i <;> simp [cuspShift, Nat.cast_succ]

theorem smul_eq_of_ne_zero (w : Fin 2 → ZMod p) (hw : w 1 ≠ 0) :
    (w 1)⁻¹ • w = ![w 0 * (w 1)⁻¹, 1] := by
  ext i; fin_cases i
  · simp [mul_comm]
  · simp [inv_mul_cancel₀ hw]

end Indices

section L59

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hp : IsUnit (p : R)) {k : ℤ}

theorem qTwist_iterate_eq_self {S : Type u} [CommRing S] (ζ : Sˣ) (e : LaurentSeries S)
    (he : qTwist ζ e = e) (n : ℕ) : (qTwist ζ)^[n] e = e := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, he]

namespace KatzGamma0Form p2m_export "ModularCurve.KatzGamma0Form" "ext dependsOnlyOnSndLine toKatzLevelPForm" end KatzGamma0Form
p2m_open_scoped "ModularCurve.KatzGamma0Form" in
include hp5 hp in

theorem KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le'
    (φ : KatzGamma0Form R p k)
    (hc : IsLevelPStructure (tateBase (cyclRing R p) p) p
      (cuspData (cyclRing R p) p (cyclZeta R p) ![1, 0] ![0, 1]))
    (hσ : qTwist (cyclZeta R p)
        (φ.toFun (tateBase (cyclRing R p) p) (isUnit_Δ_tateBase (cyclRing R p) p) _ hc)
      = φ.toFun (tateBase (cyclRing R p) p) (isUnit_Δ_tateBase (cyclRing R p) p) _ hc) :
    ∃ g : KatzModularForm R k, g.pullbackLevelP p = φ.toKatzLevelPForm := by
  have hp2 : p ≠ 2 := by omega

  have hζsum : ∑ i ∈ Finset.range p, ((cyclZeta R p : (cyclRing R p)ˣ) : cyclRing R p) ^ i = 0 :=
    sum_cyclZeta_pow_eq_zero R p
  have hζp : cyclZeta R p ^ p = 1 := cyclZeta_pow_eq_one R p
  have hp1 : IsUnit (p : cyclRing R p) := by simpa using hp.map (algebraMap R (cyclRing R p))
  haveI := cyclRing_faithfullyFlat R p hp2
  have hcAll : ∀ v w : Fin 2 → ZMod p, v 0 * w 1 - v 1 * w 0 ≠ 0 →
      IsLevelPStructure (tateBase (cyclRing R p) p) p (cuspData (cyclRing R p) p (cyclZeta R p) v w) :=
    fun v w hvw => isLevelPStructure_cuspData hp5 hp1 (cyclZeta R p) hζsum v w hvw
  have he : qTwist (cyclZeta R p) (φ.toKatzLevelPForm.toFun (tateBase (cyclRing R p) p)
      (isUnit_Δ_tateBase (cyclRing R p) p) _ hc) = φ.toKatzLevelPForm.toFun (tateBase (cyclRing R p) p)
      (isUnit_Δ_tateBase (cyclRing R p) p) _ hc := hσ

  have step2 : ∀ (v w : Fin 2 → ZMod p) (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0), w 1 ≠ 0 →
      φ.toKatzLevelPForm.toFun (tateBase (cyclRing R p) p) (isUnit_Δ_tateBase (cyclRing R p) p) _ (hcAll v w hvw) =
        φ.toKatzLevelPForm.toFun (tateBase (cyclRing R p) p) (isUnit_Δ_tateBase (cyclRing R p) p) _ hc := by
    intro v w hvw hw

    have hw0 : w ≠ 0 := fun h => hw (by rw [h]; rfl)
    set c : ZMod p := w 0 * (w 1)⁻¹ with hc_def
    have hbasis : (![1, 0] : Fin 2 → ZMod p) 0 * (![c, 1] : Fin 2 → ZMod p) 1 -
        (![1, 0] : Fin 2 → ZMod p) 1 * (![c, 1] : Fin 2 → ZMod p) 0 ≠ 0 := by simp
    have hline := inLine_cuspData_smul_of_five_le hp5 hp1 (cyclZeta R p) hζsum v ![1, 0] w hw (w 1)⁻¹ (inv_ne_zero hw)
    rw [smul_eq_of_ne_zero p w hw] at hline
    have e1 := φ.dependsOnlyOnSndLine (tateBase (cyclRing R p) p) (isUnit_Δ_tateBase (cyclRing R p) p)
      (cuspData (cyclRing R p) p (cyclZeta R p) v w) (cuspData (cyclRing R p) p (cyclZeta R p) ![1, 0] ![c, 1])
      (hcAll v w hvw) (hcAll _ _ hbasis) hline
    rw [← e1]

    have hn : ((c.val : ℕ) : ZMod p) = c := ZMod.natCast_zmod_val c
    have hidx : cuspData (cyclRing R p) p (cyclZeta R p) ![1, 0] ![c, 1] =
        cuspData (cyclRing R p) p (cyclZeta R p) ((cuspShift p)^[c.val] ![1, 0]) ((cuspShift p)^[c.val] ![0, 1]) := by
      rw [cuspShift_iterate_toric, cuspShift_iterate_qPoint, hn]
    have hbasis' : IsLevelPStructure (tateBase (cyclRing R p) p) p
        (cuspData (cyclRing R p) p (cyclZeta R p) ((cuspShift p)^[c.val] ![1, 0]) ((cuspShift p)^[c.val] ![0, 1])) :=
      hidx ▸ hcAll _ _ hbasis
    rw [φ.toKatzLevelPForm.toFun_congr_data (cyclRing R p) (isUnit_Δ_tateBase (cyclRing R p) p) hidx (hcAll _ _ hbasis) hbasis',
      φ.toKatzLevelPForm.toFun_cuspShift_iterate (cyclRing R p) (cyclZeta R p) hζp hcAll c.val ![1, 0] ![0, 1]
        (by simp) hc hbasis']
    exact qTwist_iterate_eq_self (cyclZeta R p) _ he c.val

  have step3 : ∀ (v w : Fin 2 → ZMod p) (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0), v 1 ≠ 0 → w 1 ≠ 0 →
      (φ.toKatzLevelPForm.swap - φ.toKatzLevelPForm).toFun (tateBase (cyclRing R p) p)
        (isUnit_Δ_tateBase (cyclRing R p) p) _ (hcAll v w hvw) = 0 := by
    intro v w hvw hv hw
    have hwv : w 0 * v 1 - w 1 * v 0 ≠ 0 := by
      intro h; apply hvw; linear_combination -h
    rw [KatzLevelPForm.sub_toFun, KatzLevelPForm.swap_toFun, sub_eq_zero]
    rw [step2 v w hvw hw]

    exact (φ.toKatzLevelPForm.toFun_congr_data (cyclRing R p) (isUnit_Δ_tateBase (cyclRing R p) p) (cuspData_swap (cyclRing R p) p (cyclZeta R p) v w)
      (hcAll v w hvw).swap (hcAll w v hwv)).trans (step2 w v hwv hv)

  have hD : φ.toKatzLevelPForm.swap - φ.toKatzLevelPForm = 0 :=
    KatzLevelPForm.eq_zero_of_dependsOnlyOnLines_of_forall_evalCusp_eq_zero hp2 hp (cyclRing R p)
      (cyclZeta R p) hζsum hcAll _ (φ.dependsOnlyOnSndLine.dependsOnlyOnLines_swap_sub) step3

  have h2 : φ.toKatzLevelPForm.SwapInvariant := by
    rw [KatzLevelPForm.swapInvariant_iff_swap_eq]
    exact sub_eq_zero.mp hD
  obtain ⟨g, hg, -⟩ := KatzLevelPForm.existsUnique_pullbackLevelP_eq_of_swapInvariant hp2 hp
    φ.toKatzLevelPForm φ.dependsOnlyOnSndLine h2
  exact ⟨g, hg⟩

end L59

end ModularCurve

end

theorem solution
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hp : IsUnit (p : R)) {k : ℤ}
    (φ : ModularCurve.KatzGamma0Form R p k)
    (hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase (ModularCurve.cyclRing R p) p) p
      (ModularCurve.cuspData (ModularCurve.cyclRing R p) p (ModularCurve.cyclZeta R p) ![1, 0] ![0, 1]))
    (hσ : ModularCurve.qTwist (ModularCurve.cyclZeta R p)
        (φ.toFun (ModularCurve.tateBase (ModularCurve.cyclRing R p) p)
          (ModularCurve.isUnit_Δ_tateBase (ModularCurve.cyclRing R p) p) _ hc)
      = φ.toFun (ModularCurve.tateBase (ModularCurve.cyclRing R p) p)
          (ModularCurve.isUnit_Δ_tateBase (ModularCurve.cyclRing R p) p) _ hc) :
    ∃ g : KatzModularForm R k, g.pullbackLevelP p = φ.toKatzLevelPForm :=
  ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le' hp5 hp φ hc hσ

end S_ModularCurve_KatzGamma0Form_exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le
end P2MW
export P2MW.S_ModularCurve_KatzGamma0Form_exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le (solution)
