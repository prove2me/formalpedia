-- Prove2me | solution 1 for ModularCurve.cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/8378ba39-3252-5403-aeff-a3644c3c10d2

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two
import Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_two_eq
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import Theorems.Thm_WeierstrassCurve_map_veluQuotient_image
import Theorems.Thm_ModularCurve_j_map_qExpand_tateLaurent
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_ModularCurve_exists_variableChange_veluQuotient_tateLaurent_eq_and_vcXInv_veluX_toricPoint_eq_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples.ModularCurve WeierstrassCurve~map_veluU~map_veluT~map_veluGy~map_veluGx"

universe u v

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "toricPoint tateLaurent jqNModC qExpand qExpand_one_apply qExpand_congr j_map_qExpand_tateLaurent exists_variableChange_veluQuotient_tateLaurent_eq_and_vcXInv_veluX_toricPoint_eq_of_isPrimitiveRoot exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot"
namespace TateDE107
p2m_open "ModularCurve"

section Maps

variable {F F' : Type*} [Field F] [Field F'] (f : F →+* F')

theorem vcXInv_map (C : VariableChange F) (x : F) :
    Affine.vcXInv (C.map f) (f x) = f (Affine.vcXInv C x) := by
  simp [Affine.vcXInv, VariableChange.map, map_sub, map_mul, map_pow]

theorem vcYInv_map (C : VariableChange F) (x y : F) :
    Affine.vcYInv (C.map f) (f x) (f y) = f (Affine.vcYInv C x y) := by
  simp [Affine.vcYInv, VariableChange.map, map_sub, map_mul, map_pow]

theorem map_veluGx (W : WeierstrassCurve F) (x y : F) :
    (W.map f).veluGx (f x) (f y) = f (W.veluGx x y) := by
  simp [veluGx, map_ofNat]

theorem map_veluGy (W : WeierstrassCurve F) (x y : F) :
    (W.map f).veluGy (f x) (f y) = f (W.veluGy x y) := by
  simp [veluGy, map_ofNat]

theorem map_veluT (W : WeierstrassCurve F) (x y : F) :
    (W.map f).veluT (f x) (f y) = f (W.veluT x y) := by
  simp [veluT, map_veluGx, map_veluGy, map_ofNat]

theorem map_veluU (W : WeierstrassCurve F) (x y : F) :
    (W.map f).veluU (f x) (f y) = f (W.veluU x y) := by
  simp [veluU, map_veluGy]

theorem map_veluX [DecidableEq F'] (W : WeierstrassCurve F) (S : Finset (F × F)) (x : F) :
    (W.map f).veluX (S.image (Prod.map f f)) (f x) = f (W.veluX S x) := by
  have hinj : Set.InjOn (Prod.map f f) S := (Prod.map_injective.mpr ⟨f.injective, f.injective⟩).injOn
  rw [veluX, veluX, Finset.sum_image hinj, map_add, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun Q _ => ?_)
  simp [map_div₀, map_veluT, map_veluU]

theorem map_veluY [DecidableEq F'] (W : WeierstrassCurve F) (S : Finset (F × F)) (x y : F) :
    (W.map f).veluY (S.image (Prod.map f f)) (f x) (f y) = f (W.veluY S x y) := by
  have hinj : Set.InjOn (Prod.map f f) S := (Prod.map_injective.mpr ⟨f.injective, f.injective⟩).injOn
  rw [veluY, veluY, Finset.sum_image hinj, map_sub, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun Q _ => ?_)
  simp [map_div₀, map_veluT, map_veluU, map_veluGx, map_veluGy, map_ofNat]

theorem map_velu2X (W : WeierstrassCurve F) (x₀ y₀ x : F) :
    (W.map f).velu2X (f x₀) (f y₀) (f x) = f (W.velu2X x₀ y₀ x) := by
  simp [velu2X, map_div₀, map_veluGx]

theorem map_velu2Y (W : WeierstrassCurve F) (x₀ y₀ x y : F) :
    (W.map f).velu2Y (f x₀) (f y₀) (f x) (f y) = f (W.velu2Y x₀ y₀ x y) := by
  simp [velu2Y, map_div₀, map_veluGx]

theorem map_veluQuotient2 (W : WeierstrassCurve F) (x₀ y₀ : F) :
    (W.map f).veluQuotient2 (f x₀) (f y₀) = (W.veluQuotient2 x₀ y₀).map f := by
  ext <;> simp [veluQuotient2, map_veluGx, map_ofNat]

theorem c₄_cube_div_Δ (E : WeierstrassCurve F) [E.IsElliptic] : E.c₄ ^ 3 / E.Δ = E.j := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', div_eq_mul_inv, mul_comm]

end Maps

section VCHom

variable {F : Type*} [Field F] [DecidableEq F] (C : VariableChange F) (W : WeierstrassCurve F)

def vcInvHom : W.toAffine.Point →+ (C • W).toAffine.Point where
  toFun := Affine.Point.vcInvFun C W
  map_zero' := rfl
  map_add' := Affine.Point.vcInvFun_add C W

theorem vcInvHom_apply (P : W.toAffine.Point) : vcInvHom C W P = Affine.Point.vcInvFun C W P := rfl

theorem vcInvHom_injective : Function.Injective (vcInvHom C W) :=
  (Affine.Point.vcFun_rightInverse (C := C) (W := W)).injective

theorem vcFun_vcInvHom (P : W.toAffine.Point) : Affine.Point.vcFun C W (vcInvHom C W P) = P :=
  Affine.Point.vcFun_rightInverse (C := C) (W := W) P

theorem vcInvHom_vcFun (P : (C • W).toAffine.Point) : vcInvHom C W (Affine.Point.vcFun C W P) = P :=
  Affine.Point.vcFun_leftInverse (C := C) (W := W) P

theorem mem_map_vcInvHom_iff (G : AddSubgroup W.toAffine.Point) (P : (C • W).toAffine.Point) :
    P ∈ G.map (vcInvHom C W) ↔ Affine.Point.vcFun C W P ∈ G := by
  constructor
  · rintro ⟨R, hR, rfl⟩
    rwa [vcFun_vcInvHom]
  · intro h
    exact ⟨_, h, vcInvHom_vcFun C W P⟩

theorem vcInvHom_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    ∃ h', vcInvHom C W (.some x y h) = .some (Affine.vcXInv C x) (Affine.vcYInv C x y) h' :=
  ⟨_, rfl⟩

end VCHom

section Cyclic

variable {G : Type*} [AddCommGroup G]

theorem addOrderOf_eq_of_nsmul_eq_zero_iff {P : G} {M : ℕ} (hP0 : ∀ n : ℕ, n • P = 0 ↔ M ∣ n) :
    addOrderOf P = M := by
  apply Nat.dvd_antisymm
  · exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr ((hP0 M).mpr dvd_rfl)
  · exact (hP0 _).mp (addOrderOf_nsmul_eq_zero P)

theorem dvd_of_nsmul_mem_zmultiples_nsmul {P : G} {M a b : ℕ} (hP0 : ∀ n : ℕ, n • P = 0 ↔ M ∣ n)
    (hM : M = a * b) (hb : b ≠ 0) {n : ℕ} (hn : n • P ∈ AddSubgroup.zmultiples (a • P)) : a ∣ n := by
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hn
  have h1 : (b * n) • P = 0 := by
    rw [mul_nsmul', ← hz, smul_comm, ← mul_nsmul', mul_comm b a, ← hM, (hP0 M).mpr dvd_rfl, smul_zero]
  have h2 : a * b ∣ b * n := hM ▸ (hP0 _).mp h1
  rw [mul_comm a b] at h2
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hb) h2

theorem exists_point_eq_some {F : Type*} [Field F] {W : Affine F} {Pt : W.Point} {a b x y : F}
    {h : W.Nonsingular a b} (he : Pt = .some a b h) (hx : a = x) (hy : b = y) :
    ∃ h', Pt = .some x y h' := by
  subst hx hy; exact ⟨h, he⟩

end Cyclic

section Tate

variable (K : Type u) [Field K] (L : Type v) [Field L] [DecidableEq L] [Algebra (LaurentSeries K) L]

abbrev T (m : ℕ) [NeZero m] : WeierstrassCurve L :=
  ((tateLaurent K).map (qExpand K m)).map (algebraMap (LaurentSeries K) L)

def Claim (d : ℕ) : Prop :=
  ∀ (m : ℕ) [NeZero m] [NeZero d] (V : WeierstrassCurve L) (_ : V = T K L m)
    (M : ℕ) (_ : M ≠ 0) (_ : d ∣ M) (ζ : K) (_ : IsPrimitiveRoot ζ M)
    (P : V.toAffine.Point) (_ : ∀ n : ℕ, n • P = 0 ↔ M ∣ n)
    (_ : ∀ n : ℕ, ¬ M ∣ n →
      ∃ h : V.toAffine.Nonsingular (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2),
        n • P = .some (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2) h),
    V.cyclicQuotientJ (AddSubgroup.zmultiples ((M / d) • P)) d =
      algebraMap (LaurentSeries K) L (jqNModC K (m * d))

variable {K L}

theorem jqNModC_congr {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) : jqNModC K a = jqNModC K b := by
  unfold jqNModC; exact qExpand_congr h _

theorem claim_one : Claim K L 1 := by
  intro m _ _ V hV M hM _ ζ _ P _ _
  subst hV
  haveI : (T K L m).IsElliptic := by unfold T; infer_instance
  rw [cyclicQuotientJ_one, c₄_cube_div_Δ, WeierstrassCurve.map_j, j_map_qExpand_tateLaurent, jqNModC_congr (mul_one m)]

theorem engine {d : ℕ} [NeZero d] (IH : ∀ d' < d, Claim K L d')
    (m : ℕ) [NeZero m] (M : ℕ) (hM : M ≠ 0) (hML : (M : L) ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ M)
    (P : (T K L m).toAffine.Point) (hP0 : ∀ n : ℕ, n • P = 0 ↔ M ∣ n)
    (hP : ∀ n : ℕ, ¬ M ∣ n →
      ∃ h : (T K L m).toAffine.Nonsingular (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2),
        n • P = .some (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2) h)
    (ℓ a b : ℕ) (hℓ : ℓ.Prime) (hda : d = ℓ * a) (hMb : M = d * b)
    (W₁ : WeierstrassCurve L) (φ : (T K L m).toAffine.Point →+ W₁.toAffine.Point)
    (hφQ : φ ((M / ℓ) • P) = 0)
    (gX : L → L) (gY : L → L → L)
    (hφ : ∀ n : ℕ, ¬ M / ℓ ∣ n →
      ∀ h : (T K L m).toAffine.Nonsingular (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2),
        ∃ h', φ (.some _ _ h) =
          .some (gX (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1))
            (gY (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
              (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2)) h')
    (C : VariableChange L) [NeZero (m * ℓ)] (hC : C • W₁ = T K L (m * ℓ))
    (hcoord : ∀ n : ℕ, ¬ M / ℓ ∣ n →
      Affine.vcXInv C (gX (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)) =
          algebraMap (LaurentSeries K) L (toricPoint K (m * ℓ) ((ζ ^ ℓ) ^ n)).1 ∧
        Affine.vcYInv C (gX (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1))
            (gY (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
              (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2)) =
          algebraMap (LaurentSeries K) L (toricPoint K (m * ℓ) ((ζ ^ ℓ) ^ n)).2)
    (hstep : (T K L m).cyclicQuotientJ (AddSubgroup.zmultiples ((M / d) • P)) d =
      W₁.cyclicQuotientJ ((AddSubgroup.zmultiples ((M / d) • P)).map φ) (d / ℓ)) :
    (T K L m).cyclicQuotientJ (AddSubgroup.zmultiples ((M / d) • P)) d =
      algebraMap (LaurentSeries K) L (jqNModC K (m * d)) := by

  have hℓ0 : 0 < ℓ := hℓ.pos
  have hd0 : d ≠ 0 := NeZero.ne d
  have ha0 : a ≠ 0 := by rintro rfl; simp at hda; exact hd0 hda
  have hb0 : b ≠ 0 := by rintro rfl; simp at hMb; exact hM hMb
  have hdl : d / ℓ = a := by rw [hda, Nat.mul_div_cancel_left _ hℓ0]
  have hMl : M / ℓ = a * b := by rw [hMb, hda, mul_assoc, Nat.mul_div_cancel_left _ hℓ0]
  have hMd : M / d = b := by rw [hMb, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  have hMlMd : M / ℓ / (d / ℓ) = M / d := by
    rw [hMl, hdl, hMd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha0)]
  have hℓM : ℓ ∣ M := ⟨a * b, by rw [hMb, hda, mul_assoc]⟩
  have hMl0 : M / ℓ ≠ 0 := by rw [hMl]; exact mul_ne_zero ha0 hb0
  haveI : NeZero (d / ℓ) := ⟨by rw [hdl]; exact ha0⟩
  have hlt : d / ℓ < d := Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hℓ.one_lt

  set ψ := vcInvHom C W₁ with hψ
  set P₁ : (C • W₁).toAffine.Point := ψ (φ P) with hP₁

  have hφker : ∀ n : ℕ, φ (n • P) = 0 ↔ M / ℓ ∣ n := by
    intro n
    constructor
    · intro h0
      by_contra hn
      obtain ⟨h, hnP⟩ := hP n (fun hMn => hn ((Nat.div_dvd_of_dvd hℓM).trans hMn))
      obtain ⟨h', hφ'⟩ := hφ n hn h
      rw [hnP, hφ'] at h0
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ h0
    · rintro ⟨k, rfl⟩
      rw [mul_comm, mul_nsmul', map_nsmul, hφQ, smul_zero]
  have hP0₁ : ∀ n : ℕ, n • P₁ = 0 ↔ M / ℓ ∣ n := by
    intro n
    rw [hP₁, ← map_nsmul, ← map_nsmul, map_eq_zero_iff ψ (vcInvHom_injective C W₁)]
    exact hφker n
  have hP₁' : ∀ n : ℕ, ¬ M / ℓ ∣ n →
      ∃ h : (C • W₁).toAffine.Nonsingular (algebraMap (LaurentSeries K) L (toricPoint K (m * ℓ) ((ζ ^ ℓ) ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K (m * ℓ) ((ζ ^ ℓ) ^ n)).2),
        n • P₁ = .some (algebraMap (LaurentSeries K) L (toricPoint K (m * ℓ) ((ζ ^ ℓ) ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K (m * ℓ) ((ζ ^ ℓ) ^ n)).2) h := by
    intro n hn
    obtain ⟨h, hnP⟩ := hP n (fun hMn => hn ((Nat.div_dvd_of_dvd hℓM).trans hMn))
    obtain ⟨h', hφ'⟩ := hφ n hn h
    obtain ⟨h'', hψ'⟩ := vcInvHom_some C W₁ h'
    obtain ⟨hx, hy⟩ := hcoord n hn
    exact exists_point_eq_some (h := h'') (by rw [hP₁, ← map_nsmul, ← map_nsmul, hnP, hφ', hψ, hψ']) hx hy

  have h65 := WeierstrassCurve.cyclicQuotientJ_variableChange_eq C W₁
    ((AddSubgroup.zmultiples ((M / d) • P)).map φ)
    (((AddSubgroup.zmultiples ((M / d) • P)).map φ).map ψ)
    (mem_map_vcInvHom_iff C W₁ _) (d / ℓ) (by
      intro h0; apply hML
      rw [hdl] at h0
      rw [hMb, hda, Nat.cast_mul, Nat.cast_mul, h0, mul_zero, zero_mul])
  have hH : ((AddSubgroup.zmultiples ((M / d) • P)).map φ).map ψ =
      AddSubgroup.zmultiples ((M / ℓ / (d / ℓ)) • P₁) := by
    rw [AddMonoidHom.map_zmultiples, AddMonoidHom.map_zmultiples, ← map_nsmul, ← map_nsmul, hMlMd]
  rw [hstep, ← h65, hH]
  have key := IH (d / ℓ) hlt (m * ℓ) (C • W₁) hC (M / ℓ) hMl0
    (by rw [hMl, hdl]; exact Dvd.intro b rfl) (ζ ^ ℓ) (hζ.pow_of_dvd hℓ.ne_zero hℓM) P₁ hP0₁ hP₁'
  haveI : NeZero (m * ℓ * (d / ℓ)) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  rw [key, jqNModC_congr (show m * ℓ * (d / ℓ) = m * d by rw [hdl, hda, mul_assoc])]

theorem cyclicQuotientJ_congr_sigma {F : Type*} [Field F] [DecidableEq F] {W W' : WeierstrassCurve F}
    {G : AddSubgroup W.toAffine.Point} {G' : AddSubgroup W'.toAffine.Point}
    (h : (⟨W, G⟩ : Σ V : WeierstrassCurve F, AddSubgroup V.toAffine.Point) = ⟨W', G'⟩) (n : ℕ) :
    W.cyclicQuotientJ G n = W'.cyclicQuotientJ G' n := by
  cases h; rfl

scoped instance isElliptic_T (m : ℕ) [NeZero m] : (T K L m).IsElliptic := by
  unfold T; infer_instance

omit [DecidableEq L] in

theorem natCast_ne_zero_of_isPrimitiveRoot {M : ℕ} (hM : M ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ M) {k : ℕ} (hk : k ∣ M) :
    (k : L) ≠ 0 := by
  haveI : NeZero M := ⟨hM⟩
  have hMK : (M : K) ≠ 0 := (hζ.neZero').out
  obtain ⟨c, rfl⟩ := hk
  rw [Nat.cast_mul] at hMK
  have hkK : (k : K) ≠ 0 := left_ne_zero_of_mul hMK
  have := ((algebraMap (LaurentSeries K) L).comp (algebraMap K (LaurentSeries K))).injective.ne hkK
  simpa using this

theorem oddOrderSummingSet_eq_image (m : ℕ) [NeZero m] (M : ℕ) (ζ : K)
    (P : (T K L m).toAffine.Point)
    (hP : ∀ n : ℕ, ¬ M ∣ n →
      ∃ h : (T K L m).toAffine.Nonsingular (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2),
        n • P = .some (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2) h)
    (ℓ c : ℕ) (hℓ : ℓ.Prime) (hMl : M = ℓ * c) (hc : c ≠ 0)
    (S : Finset (LaurentSeries K × LaurentSeries K))
    (hS : ∀ x, x ∈ S ↔ ∃ k ∈ Finset.Icc 1 (ℓ / 2), toricPoint K m ((ζ ^ c) ^ k) = x) :
    (T K L m).oddOrderSummingSet (c • P) (ℓ / 2) =
      S.image (Prod.map (algebraMap (LaurentSeries K) L) (algebraMap (LaurentSeries K) L)) := by
  ext x
  rw [WeierstrassCurve.mem_oddOrderSummingSet, Finset.mem_image]
  constructor
  · rintro ⟨k, hk1, hk2, rfl⟩
    have hkl : ¬ M ∣ k * c := by
      rw [hMl]
      intro hdvd
      have h1 : ℓ ∣ k := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hc) hdvd
      have h2 := Nat.le_of_dvd (by omega) h1
      have h3 := Nat.div_lt_self hℓ.pos (by norm_num : 1 < 2)
      omega
    obtain ⟨h, hk⟩ := hP (k * c) hkl
    refine ⟨toricPoint K m ((ζ ^ c) ^ k), (hS _).mpr ⟨k, Finset.mem_Icc.mpr ⟨hk1, hk2⟩, rfl⟩, ?_⟩
    rw [← mul_nsmul', hk, Affine.Point.coordsOrZero_some, ← pow_mul, mul_comm c k]
    rfl
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk, rfl⟩ := (hS y).mp hy
    rw [Finset.mem_Icc] at hk
    have hkl : ¬ M ∣ k * c := by
      rw [hMl]
      intro hdvd
      have h1 : ℓ ∣ k := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hc) hdvd
      have h2 := Nat.le_of_dvd (by omega) h1
      have h3 := Nat.div_lt_self hℓ.pos (by norm_num : 1 < 2)
      omega
    obtain ⟨h, hk'⟩ := hP (k * c) hkl
    refine ⟨k, hk.1, hk.2, ?_⟩
    rw [← mul_nsmul', hk', Affine.Point.coordsOrZero_some, ← pow_mul, mul_comm c k]
    rfl

theorem claim_step_odd {d : ℕ} [NeZero d] (IH : ∀ d' < d, Claim K L d')
    (m : ℕ) [NeZero m] (M : ℕ) (hM : M ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ M)
    (P : (T K L m).toAffine.Point) (hP0 : ∀ n : ℕ, n • P = 0 ↔ M ∣ n)
    (hP : ∀ n : ℕ, ¬ M ∣ n →
      ∃ h : (T K L m).toAffine.Nonsingular (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2),
        n • P = .some (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2) h)
    (ℓ a b : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hda : d = ℓ * a) (hMb : M = d * b)
    (hstep : (T K L m).cyclicQuotientJ (AddSubgroup.zmultiples ((M / d) • P)) d =
      ((T K L m).stepCurve (AddSubgroup.zmultiples ((M / d) • P)) ℓ).cyclicQuotientJ
        ((T K L m).stepSubgroup (AddSubgroup.zmultiples ((M / d) • P)) ℓ) (d / ℓ)) :
    (T K L m).cyclicQuotientJ (AddSubgroup.zmultiples ((M / d) • P)) d =
      algebraMap (LaurentSeries K) L (jqNModC K (m * d)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero M := ⟨hM⟩
  haveI : NeZero (m * ℓ) := ⟨mul_ne_zero (NeZero.ne m) hℓ.ne_zero⟩
  set ι := algebraMap (LaurentSeries K) L with hι
  set E : WeierstrassCurve (LaurentSeries K) := (tateLaurent K).map (qExpand K m) with hE
  have hℓ0 : 0 < ℓ := hℓ.pos
  have hd0 : d ≠ 0 := NeZero.ne d
  have ha0 : a ≠ 0 := by rintro rfl; simp at hda; exact hd0 hda
  have hb0 : b ≠ 0 := by rintro rfl; simp at hMb; exact hM hMb
  have hMl : M / ℓ = a * b := by rw [hMb, hda, mul_assoc, Nat.mul_div_cancel_left _ hℓ0]
  have hMd : M / d = b := by rw [hMb, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  have hMfac : M = ℓ * (M / ℓ) := by rw [hMl, hMb, hda, mul_assoc]
  have hMfac' : M = (M / ℓ) * ℓ := by rw [mul_comm, ← hMfac]
  have hMl0 : M / ℓ ≠ 0 := by rw [hMl]; exact mul_ne_zero ha0 hb0
  have hordP : addOrderOf P = M := addOrderOf_eq_of_nsmul_eq_zero_iff hP0
  have hdvd_of_mem : ∀ n : ℕ, n • P ∈ AddSubgroup.zmultiples ((M / ℓ) • P) → M / ℓ ∣ n := fun n hn =>
    dvd_of_nsmul_mem_zmultiples_nsmul hP0 hMfac' hℓ.ne_zero hn

  set Q : (T K L m).toAffine.Point := (M / ℓ) • P with hQ
  set ζℓ : K := ζ ^ (M / ℓ) with hζℓ
  have hζℓ' : IsPrimitiveRoot ζℓ ℓ := hζ.pow (Nat.pos_of_ne_zero hM) hMfac'
  have hQord : addOrderOf Q = ℓ := by
    rw [hQ, addOrderOf_nsmul_of_dvd hMl0 (by rw [hordP]; exact ⟨ℓ, hMfac'⟩), hordP, Nat.div_div_self ⟨_, hMfac⟩ hM]
  have hℓL : (ℓ : L) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot hM hζ ⟨_, hMfac⟩
  have hML : (M : L) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot hM hζ dvd_rfl
  have hQH : Q ∈ AddSubgroup.zmultiples ((M / d) • P) := by
    rw [hQ, hMl, hMd, mul_nsmul']
    exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) a

  obtain ⟨φ, hφker, hφ⟩ :=
    WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet (T K L m) hℓ hℓ2 hℓL Q hQord
  haveI : IsAddCyclic (AddSubgroup.zmultiples ((M / d) • P)) := inferInstance
  haveI : Finite (AddSubgroup.zmultiples ((M / d) • P)) := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_zmultiples, hMd, addOrderOf_nsmul_of_dvd hb0 (by rw [hordP]; exact ⟨d, by rw [hMb, mul_comm]⟩), hordP, hMb,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)]
    exact hd0
  have hsig := WeierstrassCurve.stepCurve_stepSubgroup_eq_of_prime_ne_two (T K L m) hℓ hℓ2
    (AddSubgroup.zmultiples ((M / d) • P)) Q hQH hQord φ hφker hφ
  have hstep' := hstep.trans (cyclicQuotientJ_congr_sigma hsig (d / ℓ))

  classical
  set S : Finset (LaurentSeries K × LaurentSeries K) :=
    (Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K m (ζℓ ^ k) with hSdef
  have hS : (T K L m).oddOrderSummingSet Q (ℓ / 2) = S.image (Prod.map ι ι) :=
    oddOrderSummingSet_eq_image m M ζ P hP ℓ (M / ℓ) hℓ hMfac hMl0 S (fun x => by rw [hSdef, Finset.mem_image])
  have hcard : (S.image (Prod.map ι ι)).card = S.card :=
    Finset.card_image_of_injective _ (Prod.map_injective.mpr ⟨ι.injective, ι.injective⟩)
  have hW₁ : (T K L m).veluQuotient ((T K L m).oddOrderSummingSet Q (ℓ / 2)) = (E.veluQuotient S).map ι := by
    rw [hS]; exact WeierstrassCurve.map_veluQuotient_image E ι S hcard

  obtain ⟨C, hCE, hpts⟩ :=
    ModularCurve.exists_variableChange_veluQuotient_tateLaurent_eq_and_vcXInv_veluX_toricPoint_eq_of_isPrimitiveRoot
      K M ζ hζ ℓ hℓ2 ⟨_, hMfac⟩ m
  have hC : (C.map ι) • (T K L m).veluQuotient ((T K L m).oddOrderSummingSet Q (ℓ / 2)) = T K L (m * ℓ) := by
    rw [hW₁, WeierstrassCurve.map_variableChange, hCE]
  refine engine IH m M hM hML ζ hζ P hP0 hP ℓ a b hℓ hda hMb _ φ ?_ ((T K L m).veluX ((T K L m).oddOrderSummingSet Q (ℓ / 2)))
    ((T K L m).veluY ((T K L m).oddOrderSummingSet Q (ℓ / 2))) ?_ (C.map ι) hC ?_ hstep'
  ·
    rw [← AddMonoidHom.mem_ker, hφker]; exact AddSubgroup.mem_zmultiples Q
  ·
    intro n hn h
    refine hφ _ _ h ?_
    intro hmem
    obtain ⟨h', hnP⟩ := hP n (fun hMn => hn ((Nat.div_dvd_of_dvd ⟨_, hMfac⟩).trans hMn))
    rw [← hnP] at hmem
    exact hn (hdvd_of_mem n hmem)
  ·
    intro n hn
    have hcℓ : (ζ ^ n) ^ ℓ ≠ 1 := by
      rw [← pow_mul, Ne, hζ.pow_eq_one_iff_dvd, hMfac']
      intro hdvd
      exact hn (Nat.dvd_of_mul_dvd_mul_right hℓ0 hdvd)
    obtain ⟨hx, hy⟩ := hpts n hcℓ
    rw [hS, show T K L m = E.map ι from rfl, map_veluX, map_veluY, vcXInv_map, vcYInv_map, hx, hy, ← pow_mul, ← pow_mul,
      mul_comm n ℓ]
    exact ⟨rfl, rfl⟩

theorem claim_step_two {d : ℕ} [NeZero d] (IH : ∀ d' < d, Claim K L d')
    (m : ℕ) [NeZero m] (M : ℕ) (hM : M ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ M)
    (P : (T K L m).toAffine.Point) (hP0 : ∀ n : ℕ, n • P = 0 ↔ M ∣ n)
    (hP : ∀ n : ℕ, ¬ M ∣ n →
      ∃ h : (T K L m).toAffine.Nonsingular (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2),
        n • P = .some (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K m (ζ ^ n)).2) h)
    (a b : ℕ) (hda : d = 2 * a) (hMb : M = d * b)
    (hstep : (T K L m).cyclicQuotientJ (AddSubgroup.zmultiples ((M / d) • P)) d =
      ((T K L m).stepCurve (AddSubgroup.zmultiples ((M / d) • P)) 2).cyclicQuotientJ
        ((T K L m).stepSubgroup (AddSubgroup.zmultiples ((M / d) • P)) 2) (d / 2)) :
    (T K L m).cyclicQuotientJ (AddSubgroup.zmultiples ((M / d) • P)) d =
      algebraMap (LaurentSeries K) L (jqNModC K (m * d)) := by
  haveI : NeZero M := ⟨hM⟩
  haveI : NeZero (m * 2) := ⟨mul_ne_zero (NeZero.ne m) two_ne_zero⟩
  set ι := algebraMap (LaurentSeries K) L with hι
  set E : WeierstrassCurve (LaurentSeries K) := (tateLaurent K).map (qExpand K m) with hE
  have hd0 : d ≠ 0 := NeZero.ne d
  have ha0 : a ≠ 0 := by rintro rfl; simp at hda; exact hd0 hda
  have hb0 : b ≠ 0 := by rintro rfl; simp at hMb; exact hM hMb
  have hMl : M / 2 = a * b := by rw [hMb, hda, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  have hMd : M / d = b := by rw [hMb, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  have hMfac : M = 2 * (M / 2) := by rw [hMl, hMb, hda, mul_assoc]
  have hMfac' : M = (M / 2) * 2 := by rw [mul_comm, ← hMfac]
  have hMl0 : M / 2 ≠ 0 := by rw [hMl]; exact mul_ne_zero ha0 hb0
  have hordP : addOrderOf P = M := addOrderOf_eq_of_nsmul_eq_zero_iff hP0
  have hdvd_of_mem : ∀ n : ℕ, n • P ∈ AddSubgroup.zmultiples ((M / 2) • P) → M / 2 ∣ n := fun n hn =>
    dvd_of_nsmul_mem_zmultiples_nsmul hP0 hMfac' two_ne_zero hn
  have h2L : (2 : L) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_isPrimitiveRoot (L := L) hM hζ ⟨_, hMfac⟩
  have hML : (M : L) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot hM hζ dvd_rfl

  have hζ2 : ζ ^ (M / 2) = -1 := (hζ.pow (Nat.pos_of_ne_zero hM) hMfac').eq_neg_one_of_two_right
  have hM2 : ¬ M ∣ M / 2 := fun h => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hMl0) h; omega
  obtain ⟨hns, hQ⟩ : ∃ h : (T K L m).toAffine.Nonsingular (ι (toricPoint K m (-1)).1) (ι (toricPoint K m (-1)).2),
      (M / 2) • P = .some (ι (toricPoint K m (-1)).1) (ι (toricPoint K m (-1)).2) h := by
    rw [← hζ2]; exact hP _ hM2
  set x₀ := ι (toricPoint K m (-1)).1 with hx₀
  set y₀ := ι (toricPoint K m (-1)).2 with hy₀
  have hQQ : (2 : ℕ) • ((M / 2) • P) = 0 := by rw [← mul_nsmul', ← hMfac, (hP0 M).mpr dvd_rfl]
  have hnegY : (T K L m).toAffine.negY x₀ y₀ = y₀ := by
    have h1 : -((M / 2) • P) = (M / 2) • P := by
      rw [neg_eq_iff_add_eq_zero, ← two_nsmul]; exact hQQ
    rw [hQ, Affine.Point.neg_some] at h1
    exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h1 |>.2
  have hgy : (T K L m).veluGy x₀ y₀ = 0 := WeierstrassCurve.veluGy_eq_zero_of_negY_eq _ hnegY

  obtain ⟨C, hCE, hpts⟩ :=
    ModularCurve.exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot
      K M ζ hζ ⟨_, hMfac⟩ m
  have hW₁ : (T K L m).veluQuotient2 x₀ y₀ = (E.veluQuotient2 (toricPoint K m (-1)).1 (toricPoint K m (-1)).2).map ι := by
    rw [hx₀, hy₀, show T K L m = E.map ι from rfl, map_veluQuotient2]
  have hC : (C.map ι) • (T K L m).veluQuotient2 x₀ y₀ = T K L (m * 2) := by
    rw [hW₁, WeierstrassCurve.map_variableChange, hCE]
  have hΔ : ((T K L m).veluQuotient2 x₀ y₀).Δ ≠ 0 := by
    intro h0
    have h1 : (T K L (m * 2)).Δ = 0 := by
      rw [← hC, WeierstrassCurve.variableChange_Δ, h0, mul_zero]
    exact (T K L (m * 2)).isUnit_Δ.ne_zero h1

  obtain ⟨φ, hφ⟩ := WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2 (T K L m) h2L hns.1 hgy hΔ
  haveI : IsAddCyclic (AddSubgroup.zmultiples ((M / d) • P)) := inferInstance
  haveI : Finite (AddSubgroup.zmultiples ((M / d) • P)) := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_zmultiples, hMd, addOrderOf_nsmul_of_dvd hb0 (by rw [hordP]; exact ⟨d, by rw [hMb, mul_comm]⟩), hordP, hMb,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)]
    exact hd0
  have hQH : (.some x₀ y₀ hns : (T K L m).toAffine.Point) ∈ AddSubgroup.zmultiples ((M / d) • P) := by
    rw [← hQ, hMl, hMd, mul_nsmul']
    exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) a
  have hsig := WeierstrassCurve.stepCurve_stepSubgroup_two_eq (T K L m) h2L
    (AddSubgroup.zmultiples ((M / d) • P)) hns hQH hgy hΔ φ hφ
  have hstep' := hstep.trans (cyclicQuotientJ_congr_sigma hsig (d / 2))

  have hxne : ∀ n : ℕ, ¬ M / 2 ∣ n → ∀ {y : L} (h : (T K L m).toAffine.Nonsingular (ι (toricPoint K m (ζ ^ n)).1) y),
      n • P = .some _ _ h → ι (toricPoint K m (ζ ^ n)).1 ≠ x₀ := by
    intro n hn y h hnP hx
    apply hn (hdvd_of_mem n _)
    have hy : y = y₀ := by
      by_cases hyy : y = (T K L m).toAffine.negY x₀ y₀
      · rw [hyy, hnegY]
      · exact Affine.Y_eq_of_Y_ne h.1 hns.1 hx hyy
    have : n • P = (M / 2) • P := by
      rw [hnP, hQ]; exact Affine.Point.some.injEq _ _ _ _ _ _ |>.mpr ⟨hx, hy⟩
    rw [this]; exact AddSubgroup.mem_zmultiples _
  refine engine IH m M hM hML ζ hζ P hP0 hP 2 a b Nat.prime_two hda hMb _ φ ?_ ((T K L m).velu2X x₀ y₀)
    ((T K L m).velu2Y x₀ y₀) ?_ (C.map ι) hC ?_ hstep'
  ·
    rw [hQ, hφ, WeierstrassCurve.veluPointMap2_some_of_eq _ _ _ _ hns rfl]; rfl
  ·
    intro n hn h
    obtain ⟨h', hnP⟩ := hP n (fun hMn => hn ((Nat.div_dvd_of_dvd ⟨_, hMfac⟩).trans hMn))
    have hx := hxne n hn h' hnP
    exact ⟨_, by rw [hφ, WeierstrassCurve.veluPointMap2_some_of_ne _ _ _ _ h hx]⟩
  ·
    intro n hn
    have hc2 : (ζ ^ n) ^ 2 ≠ 1 := by
      rw [← pow_mul, Ne, hζ.pow_eq_one_iff_dvd, hMfac']
      intro hdvd
      exact hn (Nat.dvd_of_mul_dvd_mul_right two_pos hdvd)
    obtain ⟨hx, hy⟩ := hpts n hc2
    rw [hx₀, hy₀, show T K L m = E.map ι from rfl, map_velu2X, map_velu2Y, vcXInv_map, vcYInv_map, hx, hy, ← pow_mul,
      ← pow_mul, mul_comm n 2]
    exact ⟨rfl, rfl⟩

theorem claim_all (d : ℕ) : Claim K L d := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro m _ _ V hV M hM hdM ζ hζ P hP0 hP
  subst hV
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · obtain rfl : d = 1 := by have := NeZero.ne d; omega
    exact claim_one m _ rfl M hM hdM ζ hζ P hP0 hP
  · have hℓ : d.minFac.Prime := Nat.minFac_prime (by omega)
    obtain ⟨a, hda⟩ := Nat.minFac_dvd d
    obtain ⟨b, hMb⟩ := hdM
    have hstep := WeierstrassCurve.cyclicQuotientJ_eq_of_two_le (T K L m) (AddSubgroup.zmultiples ((M / d) • P)) hd2
    rcases eq_or_ne d.minFac 2 with hℓ2 | hℓ2
    · rw [hℓ2] at hda hstep
      exact claim_step_two IH m M hM ζ hζ P hP0 hP a b hda hMb hstep
    · exact claim_step_odd IH m M hM ζ hζ P hP0 hP d.minFac a b hℓ hℓ2 hda hMb hstep

theorem main (N : ℕ) [NeZero N] (ζ : K) (hζ : IsPrimitiveRoot ζ N)
    (P : ((tateLaurent K).baseChange L).toAffine.Point)
    (hP0 : ∀ n : ℕ, n • P = 0 ↔ N ∣ n)
    (hP : ∀ n : ℕ, ¬ N ∣ n →
      ∃ h : ((tateLaurent K).baseChange L).toAffine.Nonsingular
          (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).2),
        n • P = WeierstrassCurve.Affine.Point.some
          (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).2) h)
    (d : ℕ) [NeZero d] (hd : d ∣ N)
    (H' : AddSubgroup ((tateLaurent K).baseChange L).toAffine.Point)
    (hH' : IsAddCyclic H' ∧ Nat.card H' = d) (hle : H' ≤ AddSubgroup.zmultiples P) :
    ((tateLaurent K).baseChange L).cyclicQuotientJ H' d = algebraMap (LaurentSeries K) L (jqNModC K d) := by
  have hT1 : (tateLaurent K).baseChange L = T K L 1 := by
    show (tateLaurent K).map _ = ((tateLaurent K).map (qExpand K 1)).map _
    congr 1
    ext <;> simp [qExpand_one_apply]
  have hN : N ≠ 0 := NeZero.ne N
  have hd0 : d ≠ 0 := NeZero.ne d
  have hordP : addOrderOf P = N := addOrderOf_eq_of_nsmul_eq_zero_iff hP0
  obtain ⟨e, he⟩ := hd
  have he0 : e ≠ 0 := by rintro rfl; simp at he; exact hN he
  have hNd : N / d = e := by rw [he, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]

  have hcard : Nat.card (AddSubgroup.zmultiples ((N / d) • P)) = d := by
    rw [Nat.card_zmultiples, hNd, addOrderOf_nsmul_of_dvd he0 (by rw [hordP]; exact ⟨d, by rw [he, mul_comm]⟩), hordP, he,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero he0)]
  haveI : Finite (AddSubgroup.zmultiples ((N / d) • P)) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hd0)
  have hle' : H' ≤ AddSubgroup.zmultiples ((N / d) • P) := by
    intro x hx
    have hdx : d • x = 0 := by
      have h1 := card_nsmul_eq_zero' (G := H') (x := ⟨x, hx⟩)
      rw [hH'.2] at h1
      exact congrArg Subtype.val h1
    obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hle hx)
    have h2 : ((d : ℤ) * z) • P = 0 := by rw [mul_zsmul, natCast_zsmul]; exact hdx
    have h3 : ((N : ℕ) : ℤ) ∣ (d : ℤ) * z := by
      rw [← hordP]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr h2
    rw [he, Nat.cast_mul] at h3
    obtain ⟨w, hw⟩ := (mul_dvd_mul_iff_left (by exact_mod_cast hd0 : (d : ℤ) ≠ 0)).mp h3
    rw [hNd]
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨w, ?_⟩
    rw [hw, mul_comm, mul_zsmul, natCast_zsmul]
  have hHeq : H' = AddSubgroup.zmultiples ((N / d) • P) :=
    AddSubgroup.eq_of_le_of_card_ge hle' (by rw [hcard, hH'.2])
  rw [hHeq]
  have key := claim_all (K := K) (L := L) d 1 ((tateLaurent K).baseChange L) hT1 N hN ⟨e, he⟩ ζ hζ P hP0 hP
  rwa [jqNModC_congr (one_mul d)] at key

end Tate

end ModularCurve.TateDE107
p2m_reactivate "P2MW.S_ModularCurve_cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples.ModularCurve P2MW.S_ModularCurve_cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples.ModularCurve.TateDE107"
p2m_reactivate "P2MW.S_ModularCurve_cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples.ModularCurve"

open ModularCurve.TateDE107 in

theorem solution
    (K : Type u) [Field K] (L : Type v) [Field L] [DecidableEq L] [Algebra (LaurentSeries K) L]
    (N : ℕ) [NeZero N] (ζ : K) (hζ : IsPrimitiveRoot ζ N)
    (P : ((tateLaurent K).baseChange L).toAffine.Point)
    (hP0 : ∀ n : ℕ, n • P = 0 ↔ N ∣ n)
    (hP : ∀ n : ℕ, ¬ N ∣ n →
      ∃ h : ((tateLaurent K).baseChange L).toAffine.Nonsingular
          (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).2),
        n • P = WeierstrassCurve.Affine.Point.some
          (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).1)
          (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).2) h)
    (d : ℕ) [NeZero d] (hd : d ∣ N)
    (H' : AddSubgroup ((tateLaurent K).baseChange L).toAffine.Point)
    (hH' : IsAddCyclic H' ∧ Nat.card H' = d) (hle : H' ≤ AddSubgroup.zmultiples P) :
    ((tateLaurent K).baseChange L).cyclicQuotientJ H' d = algebraMap (LaurentSeries K) L (jqNModC K d) :=
  main N ζ hζ P hP0 hP d hd H' hH' hle

end
p2m_reactivate "P2MW.S_ModularCurve_cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples.ModularCurve P2MW.S_ModularCurve_cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples.ModularCurve.TateDE107"

end S_ModularCurve_cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples
end P2MW
export P2MW.S_ModularCurve_cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples (solution)
