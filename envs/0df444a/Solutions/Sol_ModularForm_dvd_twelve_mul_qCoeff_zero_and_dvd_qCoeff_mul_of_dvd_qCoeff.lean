-- Prove2me | solution 1 for ModularForm.dvd_twelve_mul_qCoeff_zero_and_dvd_qCoeff_mul_of_dvd_qCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/40c762b1-0b35-50c9-8b47-7e6da405230e

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_KatzBaseChange
import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Theorems.Thm_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff
import Theorems.Thm_ModularCurve_eisensteinTwoCoeff_mul_level
import Theorems.Thm_ModularForm_sturm_bound_Gamma0
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le
import Theorems.Thm_ModularCurve_KatzGamma0Form_exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_even_of_five_le
import Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le
import Theorems.Thm_KatzModularForm_toFun_tateBase_eq_qExpand_coeffMap_qExpansion
import Theorems.Thm_KatzModularForm_exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_dvd_twelve_mul_qCoeff_zero_and_dvd_qCoeff_mul_of_dvd_qCoeff
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing WeierstrassCurve.Generic.isElliptic_curve instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.LevelP.instAlgebraTorusQRingTorusRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingTorusQRingTorusRing ModularCurve.LevelP.instAwayTorusQRingTorusDenomTorusRing ModularCurve.LevelP.instCommRingTorusRing ModularCurve.LevelP.instAlgebraUnivBasisRingTorusRing"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ProjectiveLine.map_mk ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap"
p2m_attr_erase "simp" "ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP ModularCurve.LevelP.sClassify_tmul ModularCurve.LevelP.sLift_tmul WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.LevelPData.quotientBySndLine_swap ModularCurve.LevelP.smulX_one ModularCurve.LevelP.quotientByLine_a₃ ModularCurve.LevelP.quotientByLine_a₂ ModularCurve.LevelP.quotientByLine_a₁ ModularCurve.LevelPData.quotientByFstLine_swap ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def TateCurve.tateTorsionPoint_zero_zero ModularCurve.LevelP.TorusQRing.lift_yQ ModularCurve.LevelP.TorusQRing.lift_yP ModularCurve.LevelP.TorusQRing.lift_xQ ModularCurve.LevelP.TorusRing.lift_ofUniv ModularCurve.LevelP.TorusQRing.lift_xP ModularCurve.LevelP.TorusQRing.lift_ofUniv ModularCurve.LevelP.TorusRing.lift_algebraMap"

set_option autoImplicit false

open Polynomial

namespace KatzA1

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

theorem b₂_tateLaurent {R : Type*} [CommRing R] : (ModularCurve.tateLaurent R).b₂ = 1 := by
  rw [ModularCurve.tateLaurent, WeierstrassCurve.map_b₂]
  simp [WeierstrassCurve.b₂, ModularCurve.tatePowerSeries]

theorem dedekindPsi_prime (p : ℕ) [Fact p.Prime] : ModularCurve.dedekindPsi p = p + 1 := by
  have hp : p.Prime := Fact.out
  have h1 : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
    rw [Finset.mem_singleton]; exact hp.one_lt.ne
  rw [ModularCurve.dedekindPsi, hp.divisors, Finset.filter_insert, if_pos squarefree_one,
    Finset.filter_singleton, if_pos hp.prime.squarefree, Finset.sum_insert h1, Finset.sum_singleton,
    Nat.div_one, Nat.div_self hp.pos, add_comm]

noncomputable def descend (M p : ℕ) (b : ℕ → ℤ) : PowerSeries (ZMod M) :=
  PowerSeries.mk fun n => ((b (p * n) : ℤ) : ZMod M)

@[scoped simp] theorem coeff_descend (M p : ℕ) (b : ℕ → ℤ) (n : ℕ) :
    PowerSeries.coeff n (descend M p b) = ((b (p * n) : ℤ) : ZMod M) := by
  rw [descend, PowerSeries.coeff_mk]

theorem ofPowerSeries_map_eq_qExpand (M : ℕ) (p : ℕ) [NeZero p] (R : Type) [CommRing R]
    [Algebra (ZMod M) R] (b : ℕ → ℤ) (hdvd : ∀ n : ℕ, ¬ p ∣ n → (M : ℤ) ∣ b n) :
    HahnSeries.ofPowerSeries ℤ R ((PowerSeries.mk b).map (Int.castRingHom R))
      = ModularCurve.qExpand R p (ModularCurve.coeffMap (algebraMap (ZMod M) R)
          (HahnSeries.ofPowerSeries ℤ (ZMod M) (descend M p b))) := by
  ext k
  rcases lt_or_ge k 0 with hk | hk
  ·
    rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk]
    by_cases hpk : (p : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hpk
      have hm : m < 0 := by
        by_contra hm
        have h0 : (0 : ℤ) ≤ (p : ℤ) * m := mul_nonneg (Int.natCast_nonneg p) (not_lt.mp hm)
        exact absurd hk (not_lt.mpr h0)
      rw [ModularCurve.qExpand_coeff_mul, ModularCurve.coeffMap_coeff,
        ModularCurve.ofPowerSeries_coeff_of_neg _ hm, map_zero]
    · rw [ModularCurve.qExpand_coeff_of_not_dvd p _ hpk]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      rw [Nat.cast_mul, ModularCurve.qExpand_coeff_mul, ModularCurve.coeffMap_coeff,
        HahnSeries.ofPowerSeries_apply_coeff, coeff_descend, map_intCast]
    · have hpn' : ¬ (p : ℤ) ∣ (n : ℤ) := by rwa [Int.natCast_dvd_natCast]
      rw [ModularCurve.qExpand_coeff_of_not_dvd p _ hpn']
      obtain ⟨d, hd⟩ := hdvd n hpn
      rw [hd, ← map_intCast (algebraMap (ZMod M) R), Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
        zero_mul, map_zero]

set_option maxHeartbeats 1600000 in
open UpperHalfPlane in

theorem of_le_three (p : ℕ) [Fact p.Prime] (hp3 : p ≤ 3) (M : ℕ) (hM : Nat.Coprime M p)
    (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n)
    (hdvd : ∀ n : ℕ, ¬ p ∣ n → (M : ℤ) ∣ b n) :
    (M : ℤ) ∣ 12 * b 0 ∧ ∀ n : ℕ, n ≠ 0 → (M : ℤ) ∣ b (p * n) := by
  have hprime : p.Prime := Fact.out

  obtain ⟨E, hE⟩ := ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff p
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 p : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
      Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]
    exact AddSubgroup.mem_zmultiples 1
  have hcs : ∀ (c : ℂ) (f : ModularForm (CongruenceSubgroup.Gamma0 p) 2), (⇑(c • f) : ℍ → ℂ) = c • ⇑f :=
    fun c f => by ext z; rfl

  have hlin : ∀ (a c : ℂ) (n : ℕ), ModularFormClass.qCoeff (⇑(a • E + c • h)) n
      = a * ModularFormClass.qCoeff (⇑E) n + c * ModularFormClass.qCoeff (⇑h) n := by
    intro a c n
    have haE := ModularFormClass.analyticAt_cuspFunction_zero (a • E) one_pos hΓ
    have hch := ModularFormClass.analyticAt_cuspFunction_zero (c • h) one_pos hΓ
    have hE' := ModularFormClass.analyticAt_cuspFunction_zero E one_pos hΓ
    have hh' := ModularFormClass.analyticAt_cuspFunction_zero h one_pos hΓ
    unfold ModularFormClass.qCoeff
    rw [ModularForm.coe_add, qExpansion_add haE hch, hcs a E, hcs c h, qExpansion_smul hE',
      qExpansion_smul hh', map_add, map_smul, map_smul]
    simp only [smul_eq_mul]

  have hg0 : ((b 0 : ℤ) : ℂ) • E + (-((ModularCurve.eisensteinTwoCoeff p 0 : ℤ) : ℂ)) • h = 0 := by
    refine ModularForm.sturm_bound_Gamma0 p _ fun n hn => ?_
    have hD : (2 * ((CongruenceSubgroup.Gamma0 p).index : ℤ)).toNat / 12 = 0 := by
      rw [ModularCurve.Gamma0_index p, dedekindPsi_prime p]
      apply Nat.div_eq_of_lt
      omega
    rw [hD, Nat.le_zero] at hn
    subst hn
    show ModularFormClass.qCoeff _ 0 = 0
    rw [hlin, hE 0, ← hb 0]
    ring

  have hrel : ∀ n : ℕ, ModularCurve.eisensteinTwoCoeff p 0 * b n = b 0 * ModularCurve.eisensteinTwoCoeff p n := by
    intro n
    have h0 : ModularFormClass.qCoeff (⇑(0 : ModularForm (CongruenceSubgroup.Gamma0 p) 2)) n = 0 := by
      have := hlin 0 0 n
      simp only [zero_smul, add_zero, zero_mul] at this
      exact this
    have h1 := hlin ((b 0 : ℤ) : ℂ) (-((ModularCurve.eisensteinTwoCoeff p 0 : ℤ) : ℂ)) n
    rw [hg0, h0, hE n, ← hb n] at h1
    have h2 : ((ModularCurve.eisensteinTwoCoeff p 0 * b n : ℤ) : ℂ)
        = ((b 0 * ModularCurve.eisensteinTwoCoeff p n : ℤ) : ℂ) := by
      push_cast
      linear_combination h1
    exact_mod_cast h2
  have he0 : ModularCurve.eisensteinTwoCoeff p 0 ≠ 0 := by
    rw [ModularCurve.eisensteinTwoCoeff_zero]
    have := hprime.two_le
    omega

  have hbp : ∀ n : ℕ, b (p * n) = b n := fun n => by
    apply mul_left_cancel₀ he0
    rw [hrel, hrel, mul_comm p n, ModularCurve.eisensteinTwoCoeff_mul_level]

  have hall : ∀ n : ℕ, n ≠ 0 → (M : ℤ) ∣ b n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      have hm : m ≠ 0 := by rintro rfl; exact hn (mul_zero p)
      rw [hbp]
      exact ih m (lt_mul_left (Nat.pos_of_ne_zero hm) hprime.one_lt) hm
    · exact hdvd n hpn
  refine ⟨?_, fun n hn => hall _ (Nat.mul_ne_zero hprime.ne_zero hn)⟩

  have hb1 : (M : ℤ) ∣ b 1 := hdvd 1 fun h1 => hprime.one_lt.ne' (Nat.dvd_one.mp h1)
  have h24 := hrel 1
  have hp23 : p = 2 ∨ p = 3 := by have := hprime.two_le; omega
  rcases hp23 with rfl | rfl
  ·
    have he : ModularCurve.eisensteinTwoCoeff 2 0 = 1 ∧ ModularCurve.eisensteinTwoCoeff 2 1 = 24 := by decide
    rw [he.1, he.2, one_mul] at h24
    have hM2 : IsCoprime (M : ℤ) 2 := by exact_mod_cast Nat.isCoprime_iff_coprime.mpr hM
    refine hM2.dvd_of_dvd_mul_left ?_
    rw [show (2 : ℤ) * (12 * b 0) = b 1 by rw [h24]; ring]
    exact hb1
  ·
    have he : ModularCurve.eisensteinTwoCoeff 3 0 = 2 ∧ ModularCurve.eisensteinTwoCoeff 3 1 = 24 := by decide
    rw [he.1, he.2] at h24
    rw [show (12 : ℤ) * b 0 = b 1 by linarith]
    exact hb1

set_option maxHeartbeats 1600000 in
p2m_open "ModularCurve~dedekindPsi_prime~coeffMap_injective" in

theorem of_five_le (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (M : ℕ) (hM : Nat.Coprime M p)
    (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n)
    (hdvd : ∀ n : ℕ, ¬ p ∣ n → (M : ℤ) ∣ b n) :
    (M : ℤ) ∣ 12 * b 0 ∧ ∀ n : ℕ, n ≠ 0 → (M : ℤ) ∣ b (p * n) := by
  have hpK : IsUnit ((p : ℕ) : ZMod M) := (ZMod.isUnit_iff_coprime p M).mpr hM.symm

  obtain ⟨φ, hφ⟩ := ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le hp5 h b hb

  letI : Algebra (Localization.Away (p : ℤ)) (ZMod M) :=
    (Localization.awayLift (Int.castRingHom (ZMod M)) (p : ℤ) (by simpa using hpK)).toAlgebra
  haveI hST := IsScalarTower.of_algebraMap_eq (R := Localization.Away (p : ℤ)) (S := ZMod M)
    (A := LaurentSeries (cyclRing (ZMod M) p)) fun r => by
      rw [ModularCurve.algebraMap_laurentSeries_apply (Localization.Away (p : ℤ)) r,
        ModularCurve.algebraMap_laurentSeries_apply (ZMod M),
        ← IsScalarTower.algebraMap_apply (Localization.Away (p : ℤ)) (ZMod M) (cyclRing (ZMod M) p) r]

  have hpR : IsUnit ((p : ℕ) : cyclRing (ZMod M) p) := by
    simpa using hpK.map (algebraMap (ZMod M) (cyclRing (ZMod M) p))
  have hc : IsLevelPStructure (tateBase (cyclRing (ZMod M) p) p) p
      (cuspData (cyclRing (ZMod M) p) p (cyclZeta (ZMod M) p) ![1, 0] ![0, 1]) :=
    ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le hp5 hpR (cyclZeta (ZMod M) p)
      (sum_cyclZeta_pow_eq_zero (ZMod M) p) 1 one_ne_zero

  have hval : (φ.baseChange (ZMod M)).toKatzLevelPForm.toFun (tateBase (cyclRing (ZMod M) p) p)
        (isUnit_Δ_tateBase (cyclRing (ZMod M) p) p) _ hc
      = qExpand (cyclRing (ZMod M) p) p (coeffMap (algebraMap (ZMod M) (cyclRing (ZMod M) p))
          (HahnSeries.ofPowerSeries ℤ (ZMod M) (KatzA1.descend M p b))) := by
    rw [KatzGamma0Form.baseChange_toKatzLevelPForm, KatzLevelPForm.baseChange_toFun,
      hφ (cyclRing (ZMod M) p) (cyclZeta (ZMod M) p) (sum_cyclZeta_pow_eq_zero (ZMod M) p) hc,
      KatzA1.ofPowerSeries_map_eq_qExpand M p (cyclRing (ZMod M) p) b hdvd]

  have hσ : qTwist (cyclZeta (ZMod M) p)
      ((φ.baseChange (ZMod M)).toFun (tateBase (cyclRing (ZMod M) p) p)
        (isUnit_Δ_tateBase (cyclRing (ZMod M) p) p) _ hc)
      = (φ.baseChange (ZMod M)).toFun (tateBase (cyclRing (ZMod M) p) p)
        (isUnit_Δ_tateBase (cyclRing (ZMod M) p) p) _ hc := by
    show qTwist _ ((φ.baseChange (ZMod M)).toKatzLevelPForm.toFun _ _ _ hc)
      = (φ.baseChange (ZMod M)).toKatzLevelPForm.toFun _ _ _ hc
    rw [hval]
    exact qTwist_qExpand_of_pow_eq_one p (cyclZeta (ZMod M) p) (cyclZeta_pow_eq_one (ZMod M) p) _
  obtain ⟨g, hg⟩ :=
    ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_even_of_five_le
      hp5 hpK even_two (φ.baseChange (ZMod M)) hc hσ

  have h1 : g.toFun (tateBase (cyclRing (ZMod M) p) p) (isUnit_Δ_tateBase (cyclRing (ZMod M) p) p)
      = qExpand (cyclRing (ZMod M) p) p (coeffMap (algebraMap (ZMod M) (cyclRing (ZMod M) p))
          (HahnSeries.ofPowerSeries ℤ (ZMod M) (KatzA1.descend M p b))) := by
    have := congrArg (fun F : KatzLevelPForm (ZMod M) p 2 =>
      F.toFun (tateBase (cyclRing (ZMod M) p) p) (isUnit_Δ_tateBase (cyclRing (ZMod M) p) p) _ hc) hg
    simpa only [KatzModularForm.pullbackLevelP_toFun, hval] using this
  have h2 := KatzModularForm.toFun_tateBase_eq_qExpand_coeffMap_qExpansion g (cyclRing (ZMod M) p) p
  have hq : g.qExpansion = HahnSeries.ofPowerSeries ℤ (ZMod M) (KatzA1.descend M p b) := by
    apply KatzA1.coeffMap_injective (KatzA1.algebraMap_cyclRing_injective (ZMod M) p)
    refine qExpand_injective p ?_
    rw [← h2, h1]

  obtain ⟨c, h12, hF⟩ :=
    KatzModularForm.exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two M g
      (KatzA1.descend M p b) hq
  have hC : HahnSeries.ofPowerSeries ℤ (ZMod M) (KatzA1.descend M p b) = HahnSeries.C c := by
    rw [← hq, KatzModularForm.qExpansion, hF, KatzA1.b₂_tateLaurent, mul_one,
      ModularCurve.algebraMap_laurentSeries_apply, Algebra.algebraMap_self_apply]
  have hgc : KatzA1.descend M p b = PowerSeries.C c :=
    HahnSeries.ofPowerSeries_injective (by rw [hC, HahnSeries.ofPowerSeries_C])
  have hcoef : ∀ n : ℕ, ((b (p * n) : ℤ) : ZMod M) = if n = 0 then c else 0 := fun n => by
    have := PowerSeries.ext_iff.mp hgc n
    rwa [KatzA1.coeff_descend, PowerSeries.coeff_C] at this
  refine ⟨?_, fun n hn => ?_⟩
  · have h0 := hcoef 0
    rw [mul_zero, if_pos rfl] at h0
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h0]
    exact_mod_cast h12
  · have hn' := hcoef n
    rw [if_neg hn] at hn'
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn'

end KatzA1
p2m_reactivate "P2MW.S_ModularForm_dvd_twelve_mul_qCoeff_zero_and_dvd_qCoeff_mul_of_dvd_qCoeff.KatzA1"

theorem solution (p : ℕ)
    [Fact p.Prime] (M : ℕ) (hM : Nat.Coprime M p) (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (b : ℕ → ℤ) (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n)
    (hdvd : ∀ n : ℕ, ¬ p ∣ n → (M : ℤ) ∣ b n) :
    (M : ℤ) ∣ 12 * b 0 ∧ ∀ n : ℕ, n ≠ 0 → (M : ℤ) ∣ b (p * n) := by
  by_cases hp3 : p ≤ 3
  · exact KatzA1.of_le_three p hp3 M hM h b hb hdvd
  · have hp5 : 5 ≤ p := by
      have h4 : p ≠ 4 := by rintro rfl; exact absurd (Fact.out : Nat.Prime 4) (by decide)
      omega
    exact KatzA1.of_five_le p hp5 M hM h b hb hdvd

end S_ModularForm_dvd_twelve_mul_qCoeff_zero_and_dvd_qCoeff_mul_of_dvd_qCoeff
end P2MW
export P2MW.S_ModularForm_dvd_twelve_mul_qCoeff_zero_and_dvd_qCoeff_mul_of_dvd_qCoeff (solution)
