-- Prove2me | solution 1 for ModularCurve.twelve_mul_natCard_evalAt_mem_ssJSet_le_sub_one_mul_index_gamma1_x1FunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d4a02040-8856-5150-8aa2-73f943cb8e61

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq
import Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
import Theorems.Thm_ModularCurve_isRational_place_x1FunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_ord_sub_algebraMap_eq_jWidthChar_of_place_x1FunctionFieldC
import Theorems.Thm_ModularCurve_finrank_adjoin_x1FunctionFieldC_eq_index_gamma1_sup_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_exists_separable_thetaL_jqModC_pow_mul_aeval_eq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_twelve_mul_natCard_evalAt_mem_ssJSet_le_sub_one_mul_index_gamma1_x1FunctionFieldC
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply"
p2m_attr_erase "simp" "TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve ModularCurve Polynomial
open scoped MatrixGroups

namespace SsCountAux

section Ord

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_algebraMap {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem' : algebraMap K F c⁻¹ ∈ v.toValuationSubring := v.algebraMap_mem' c⁻¹
  let u : v.toValuationSubringˣ :=
    ⟨⟨algebraMap K F c, hmem⟩, ⟨algebraMap K F c⁻¹, hmem'⟩,
      Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  exact v.ord_coe_unit u

theorem ord_neg (f : F) : v.ord (-f) = v.ord f := by
  simp only [Place.ord, Valuation.map_neg]

theorem min_ord_le_ord_add {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  simp only [Place.ord]
  have h := v.adicValuation.map_add f g
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hfg' := v.adicValuation_ne_zero hfg
  rcases le_max_iff.mp h with h1 | h1
  · have : WithZero.log (v.adicValuation (f + g)) ≤ WithZero.log (v.adicValuation f) :=
      (WithZero.log_le_log hfg' hf').mpr h1
    omega
  · have : WithZero.log (v.adicValuation (f + g)) ≤ WithZero.log (v.adicValuation g) :=
      (WithZero.log_le_log hfg' hg').mpr h1
    omega

theorem ord_add_eq_of_lt {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by
  simp only [Place.ord] at h ⊢
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← WithZero.log_lt_log hg' hf']
    omega
  rw [Valuation.map_add_eq_of_lt_left _ hlt]

theorem ord_multiset_prod (s : Multiset F) (hs : ∀ f ∈ s, f ≠ 0) :
    v.ord s.prod = (s.map v.ord).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ f ∈ s, f ≠ 0 := fun f hf => hs f (Multiset.mem_cons_of_mem hf)
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => hs' 0 h0 rfl
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, v.ord_mul ha hprod, ih hs']

end Ord

section OrdPoly

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_pow' (f : F) (n : ℕ) : v.ord (f ^ n) = (n : ℤ) * v.ord f := by
  rw [← zpow_natCast]; exact v.ord_zpow f n

theorem ord_sub_algebraMap_eq_zero {J : F} (hJc : ∀ r : K, J - algebraMap K F r ≠ 0)
    {j₀ : K} (hj₀ : 1 ≤ v.ord (J - algebraMap K F j₀)) {r : K} (hr : r ≠ j₀) :
    v.ord (J - algebraMap K F r) = 0 := by
  have hsplit : J - algebraMap K F r = algebraMap K F (j₀ - r) + (J - algebraMap K F j₀) := by
    rw [map_sub, sub_add_sub_cancel']
  have hne : algebraMap K F (j₀ - r) ≠ 0 := (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr hr.symm)
  have hc0 : v.ord (algebraMap K F (j₀ - r)) = 0 := ord_algebraMap v (sub_ne_zero.mpr hr.symm)
  have hlt : v.ord (algebraMap K F (j₀ - r)) < v.ord (J - algebraMap K F j₀) := by rw [hc0]; omega
  rw [hsplit, ord_add_eq_of_lt v hne (hJc j₀) hlt, hc0]

theorem ord_aeval_eq_zero [IsAlgClosed K] {J : F} (hJc : ∀ r : K, J - algebraMap K F r ≠ 0)
    {j₀ : K} (hj₀ : 1 ≤ v.ord (J - algebraMap K F j₀)) {Q : K[X]} (hQ : Q.Monic)
    (hev : Q.eval j₀ ≠ 0) : v.ord (aeval J Q) = 0 := by
  classical
  have hQroots : Q = (Q.roots.map fun r => X - C r).prod := by
    conv_lhs => rw [Splits.eq_prod_roots (IsAlgClosed.splits Q), hQ.leadingCoeff, map_one, one_mul]
  have haeval : aeval J Q = (Q.roots.map fun r => J - algebraMap K F r).prod := by
    conv_lhs => rw [hQroots]
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simp [Function.comp]
  have hfac_ne : ∀ g ∈ (Q.roots.map fun r => J - algebraMap K F r), g ≠ 0 := by
    intro g hg
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hg
    exact hJc r
  rw [haeval, ord_multiset_prod v _ hfac_ne, Multiset.map_map]
  refine Multiset.sum_eq_zero fun z hz => ?_
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
  have hrj : r ≠ j₀ := by
    rintro rfl
    exact hev (Polynomial.IsRoot.def.mp ((mem_roots hQ.ne_zero).mp hr))
  exact ord_sub_algebraMap_eq_zero v hJc hj₀ hrj

end OrdPoly

end SsCountAux

open SsCountAux

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
    (jbar : ↥(ModularCurve.x1FunctionFieldC Ω M)) (hjbar : (jbar : LaurentSeries Ω) = ModularCurve.jqModC Ω) :
    12 * Nat.card {v : AlgebraicCurve.Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M) //
          (jbar : ↥(ModularCurve.x1FunctionFieldC Ω M)) ∈ v.toValuationSubring ∧
            v.evalAt jbar ∈ ModularCurve.ssJSet p Ω} ≤
      (p - 1) * (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨t, ht, htr, hfd, -⟩ :=
    ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC p M hM hpM Ω
  have htJ : t = jbar := Subtype.ext (ht.trans hjbar.symm)
  subst htJ
  have hμ := ModularCurve.finrank_adjoin_x1FunctionFieldC_eq_index_gamma1_sup_of_isAlgClosed p M hM hpM Ω t hjbar
  haveI := hfd

  have hrat : ∀ v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M), v.IsRational := fun v =>
    ModularCurve.isRational_place_x1FunctionFieldC_of_isAlgClosed p M hM hpM Ω v

  have hjr : ∀ r : Ω, jqModC Ω - algebraMap Ω (LaurentSeries Ω) r ≠ 0 := fun r h0 =>
    X_sub_C_ne_zero r (transcendental_iff.mp (transcendental_jqModC Ω) (X - C r)
      (by rw [map_sub, aeval_X, aeval_C]; exact h0))
  have hJc : ∀ a : Ω, t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a ≠ 0 := by
    intro a h0
    have h1 := congrArg (fun z : ↥(ModularCurve.x1FunctionFieldC Ω M) => (z : LaurentSeries Ω)) h0
    simp only [AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero] at h1
    apply hjr a
    rw [← hjbar]
    exact h1

  have fib : ∀ a : Ω, ∃ S : Finset (Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M)),
      (∀ v, v ∈ S ↔ 0 < v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a)) ∧
      ∑ v ∈ S, v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) = ((CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index : ℤ) := fun a => by
    obtain ⟨S, hS, hsum⟩ := AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed Ω t htr hfd a
    exact ⟨S, hS, by rw [hsum, hμ]⟩
  choose F hF hFsum using fib

  have haff : ∀ (a : Ω) (v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M)), 0 < v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) → 0 ≤ v.ord t := by
    intro a v hva
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [map_zero, sub_zero] at hva; omega
    · have h1 : 1 ≤ v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) := hva
      have h := ord_sub_algebraMap_eq_zero v hJc h1 (r := 0) (Ne.symm ha0)
      rw [map_zero, sub_zero] at h; omega

  have hfr : ∀ (a : Ω) (v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M)), 0 < v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) →
      v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) = (ModularCurve.jWidthChar p a : ℤ) := by
    intro a v hva
    exact ModularCurve.ord_sub_algebraMap_eq_jWidthChar_of_place_x1FunctionFieldC p Ω M hM hpM t hjbar v (haff a v hva) a hva
  have hfibeq : ∀ a : Ω, ModularCurve.jWidthChar p a * (F a).card = (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
    intro a
    have h1 : ∑ v ∈ F a, v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) = ∑ v ∈ F a, (ModularCurve.jWidthChar p a : ℤ) :=
      Finset.sum_congr rfl (fun v hv => hfr a v ((hF a v).mp hv))
    have h2 := hFsum a
    rw [h1, Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : (((F a).card * ModularCurve.jWidthChar p a : ℕ) : ℤ) = ((CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index : ℤ) := by push_cast; exact h2
    have h4 : (F a).card * ModularCurve.jWidthChar p a = (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by exact_mod_cast h3
    rw [mul_comm] at h4; exact h4

  have hdisj : ∀ a b : Ω, a ≠ b → Disjoint (F a) (F b) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro v hva hvb
    rw [hF] at hva hvb
    have h1 : 1 ≤ v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) := hva
    have := ord_sub_algebraMap_eq_zero v hJc h1 (Ne.symm hab)
    omega

  set T : Finset Ω := (ModularCurve.ssJSet_finite p Ω).toFinset with hTdef
  have hTmem : ∀ a, a ∈ T ↔ a ∈ ssJSet p Ω := fun a => by rw [hTdef, Set.Finite.mem_toFinset]
  set U : Finset (Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M)) := T.biUnion F with hUdef
  have hUmem : ∀ v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M),
      ((t : ↥(ModularCurve.x1FunctionFieldC Ω M)) ∈ v.toValuationSubring ∧ v.evalAt t ∈ ssJSet p Ω) ↔ v ∈ U := by
    intro v
    rw [hUdef, Finset.mem_biUnion]
    constructor
    · rintro ⟨hmem, hss⟩
      refine ⟨v.evalAt t, (hTmem _).mpr hss, ?_⟩
      rw [hF]
      exact (AlgebraicCurve.Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos v (hrat v) t (v.evalAt t)
        (sub_ne_zero.mp (hJc _))).mp ⟨hmem, rfl⟩
    · rintro ⟨a, haT, hva⟩
      rw [hF] at hva
      obtain ⟨hmem, hev⟩ := (AlgebraicCurve.Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos v (hrat v) t a
        (sub_ne_zero.mp (hJc _))).mpr hva
      exact ⟨hmem, hev ▸ (hTmem a).mp haT⟩
  have hcardU : Nat.card {v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M) //
      (t : ↥(ModularCurve.x1FunctionFieldC Ω M)) ∈ v.toValuationSubring ∧ v.evalAt t ∈ ssJSet p Ω} = U.card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hUmem), Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcardU]
  have hUsum : U.card = ∑ a ∈ T, (F a).card := by
    rw [hUdef, Finset.card_biUnion]
    intro a _ b _ hab
    exact hdisj a b hab
  set μ := (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index with hμdef
  by_cases hp5 : 5 ≤ p
  ·
    obtain ⟨m, e₄, e₆, S, hS⟩ := ModularCurve.exists_separable_thetaL_jqModC_pow_mul_aeval_eq p hp5 Ω
    have hbr := ModularCurve.mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq p hp5 Ω m e₄ e₆ S hS
    obtain ⟨hm, he₄, he₆, hSmonic, hSsep, hSdeg, hS0, hS1728, -⟩ := hS
    have h1728 : (1728 : Ω) ≠ 0 := by
      intro h
      have h2 : ((2 : ℕ) : Ω) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff Ω p]; intro hd; have := Nat.le_of_dvd two_pos hd; omega
      have h3 : ((3 : ℕ) : Ω) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff Ω p]; intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
      have : (1728 : Ω) = ((2 : ℕ) : Ω) ^ 6 * ((3 : ℕ) : Ω) ^ 3 := by push_cast; norm_num
      rw [this] at h
      exact (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)) h

    have hWC : ∀ a : Ω, ModularCurve.jWidthChar p a = ModularCurve.jWidth a := fun a => jWidthChar_of_five_le hp5 a

    set Sr : Finset Ω := S.roots.toFinset with hSrdef
    have hSrcard : Sr.card = m := by
      rw [hSrdef, Multiset.toFinset_card_of_nodup (nodup_roots hSsep), ← hSdeg]
      exact (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits S))
    have hSr_mem : ∀ a ∈ Sr, S.eval a = 0 ∧ a ≠ 0 ∧ a ≠ 1728 := by
      intro a ha
      rw [hSrdef, Multiset.mem_toFinset, mem_roots hSmonic.ne_zero] at ha
      refine ⟨ha, ?_, ?_⟩
      · rintro rfl; exact hS0 ha
      · rintro rfl; exact hS1728 ha

    set R0 : Finset Ω := if e₄ = 1 then {0} else ∅ with hR0
    set R1 : Finset Ω := if e₆ = 1 then {1728} else ∅ with hR1
    have hTsub : T ⊆ Sr ∪ R0 ∪ R1 := by
      intro a ha
      have hev := (hbr a).mp ((hTmem a).mp ha)
      rw [eval_mul, eval_mul, eval_pow, eval_pow, eval_X, eval_sub, eval_X, eval_C] at hev
      rcases mul_eq_zero.mp hev with h12 | h3
      · rcases mul_eq_zero.mp h12 with h1 | h2
        ·
          have he : e₄ ≠ 0 := by rintro rfl; rw [pow_zero] at h1; exact one_ne_zero h1
          have he1 : e₄ = 1 := by omega
          have ha0 : a = 0 := pow_eq_zero_iff he |>.mp h1
          apply Finset.mem_union_left; apply Finset.mem_union_right
          rw [hR0, if_pos he1, Finset.mem_singleton]; exact ha0
        · have he : e₆ ≠ 0 := by rintro rfl; rw [pow_zero] at h2; exact one_ne_zero h2
          have he1 : e₆ = 1 := by omega
          have ha0 : a = 1728 := sub_eq_zero.mp (pow_eq_zero_iff he |>.mp h2)
          apply Finset.mem_union_right
          rw [hR1, if_pos he1, Finset.mem_singleton]; exact ha0
      · apply Finset.mem_union_left; apply Finset.mem_union_left
        rw [hSrdef, Multiset.mem_toFinset, mem_roots hSmonic.ne_zero]; exact h3

    have hSr_eq : ∀ a ∈ Sr, (F a).card = μ := by
      intro a ha
      have h := hfibeq a
      rw [hWC, jWidth_of_ne (hSr_mem a ha).2.1 (hSr_mem a ha).2.2, one_mul] at h
      exact h
    have h0_eq : 3 * (F 0).card = μ := by
      have h := hfibeq 0; rwa [hWC, jWidth_of_eq_zero rfl] at h
    have h1728_eq : 2 * (F 1728).card = μ := by
      have h := hfibeq 1728; rwa [hWC, jWidth_of_eq_1728 rfl h1728] at h

    have hsumSr : ∑ a ∈ Sr, (F a).card = m * μ := by
      rw [Finset.sum_congr rfl hSr_eq, Finset.sum_const, smul_eq_mul, hSrcard]
    have hsum0 : 12 * ∑ a ∈ R0, (F a).card = 4 * e₄ * μ := by
      rw [hR0]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he₄ with h4 | h4
      · simp [h4]
      · simp only [h4, if_true, Finset.sum_singleton]; omega
    have hsum1 : 12 * ∑ a ∈ R1, (F a).card = 6 * e₆ * μ := by
      rw [hR1]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he₆ with h6 | h6
      · simp [h6]
      · simp only [h6, if_true, Finset.sum_singleton]; omega
    have hle : ∑ a ∈ T, (F a).card ≤ ∑ a ∈ Sr ∪ R0 ∪ R1, (F a).card :=
      Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun _ _ _ => Nat.zero_le _)
    have h0_notin : (0 : Ω) ∉ Sr := fun h => (hSr_mem 0 h).2.1 rfl
    have h1728_notin : (1728 : Ω) ∉ Sr := fun h => (hSr_mem 1728 h).2.2 rfl
    have hd1 : Disjoint Sr R0 := by
      rw [hR0]; split_ifs
      · exact Finset.disjoint_singleton_right.mpr h0_notin
      · exact Finset.disjoint_empty_right _
    have hd2 : Disjoint (Sr ∪ R0) R1 := by
      rw [hR1]; split_ifs
      · rw [Finset.disjoint_singleton_right, Finset.mem_union, not_or]
        refine ⟨h1728_notin, ?_⟩
        rw [hR0]; split_ifs
        · rw [Finset.mem_singleton]; exact h1728
        · exact Finset.notMem_empty _
      · exact Finset.disjoint_empty_right _
    have hun : ∑ a ∈ Sr ∪ R0 ∪ R1, (F a).card ≤ ∑ a ∈ Sr, (F a).card + ∑ a ∈ R0, (F a).card + ∑ a ∈ R1, (F a).card := by
      rw [Finset.sum_union hd2, Finset.sum_union hd1]
    rw [hUsum]
    have hm' : 12 * m + 4 * e₄ + 6 * e₆ = p - 1 := hm
    calc 12 * ∑ a ∈ T, (F a).card ≤ 12 * (∑ a ∈ Sr, (F a).card + ∑ a ∈ R0, (F a).card + ∑ a ∈ R1, (F a).card) := by
          apply Nat.mul_le_mul_left; exact hle.trans hun
      _ = (12 * m + 4 * e₄ + 6 * e₆) * μ := by rw [mul_add, mul_add, hsumSr, hsum0, hsum1]; ring
      _ = (p - 1) * μ := by rw [hm']
  ·
    push_neg at hp5
    have h2 := hp.two_le
    have hp23 : p = 2 ∨ p = 3 := by
      have h4 : p ≠ 4 := by intro h; rw [h] at hp; norm_num at hp
      omega

    have hT0 : T ⊆ {0} := by
      intro a ha
      rw [Finset.mem_singleton]
      have ha' := (hTmem a).mp ha
      have hpow := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet p ha'
      rcases hp23 with rfl | rfl
      · exact ModularCurve.eq_zero_of_mem_ssJSet_two a ha' hpow
      · exact ModularCurve.eq_zero_of_mem_ssJSet_three a ha' hpow
    have hle : ∑ a ∈ T, (F a).card ≤ (F 0).card := by
      calc ∑ a ∈ T, (F a).card ≤ ∑ a ∈ ({0} : Finset Ω), (F a).card :=
            Finset.sum_le_sum_of_subset_of_nonneg hT0 (fun _ _ _ => Nat.zero_le _)
        _ = (F 0).card := Finset.sum_singleton _ _
    have h0 := hfibeq 0
    rw [hUsum]
    rcases hp23 with rfl | rfl
    · rw [jWidthChar_two_of_eq_zero rfl] at h0
      omega
    · rw [jWidthChar_three_of_eq_zero rfl] at h0
      omega

end S_ModularCurve_twelve_mul_natCard_evalAt_mem_ssJSet_le_sub_one_mul_index_gamma1_x1FunctionFieldC
end P2MW
export P2MW.S_ModularCurve_twelve_mul_natCard_evalAt_mem_ssJSet_le_sub_one_mul_index_gamma1_x1FunctionFieldC (solution)
