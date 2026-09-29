-- Prove2me | solution 1 for ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ed7d870b-ca79-5770-8607-4cc82bd65822

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j
import Theorems.Thm_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j
import Theorems.Thm_ModularCurve_isSeparable_adjoin_qExpFunctionFieldC_gamma1
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero"
p2m_attr_erase "simp" "ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve WeierstrassCurve~cusp WeierstrassCurve.Affine Polynomial"
open scoped MatrixGroups

namespace P2MKcG1Dia

universe u v w

theorem u_sq_eq_one_and_r_eq_zero_of_smul_eq {F : Type u} [Field F] (A : VariableChange F)
    (W : WeierstrassCurve F) (h : A • W = W) (hc₄ : W.c₄ ≠ 0) (hc₆ : W.c₆ ≠ 0) :
    ((A.u : F)) ^ 2 = 1 ∧ A.r = 0 := by
  have h4 : (A • W).c₄ = W.c₄ := by rw [h]
  have h6 : (A • W).c₆ = W.c₆ := by rw [h]
  rw [variableChange_c₄] at h4
  rw [variableChange_c₆] at h6
  have hu4 : ((A.u⁻¹ : Fˣ) : F) ^ 4 = 1 := by
    have := mul_right_cancel₀ hc₄ (h4.trans (one_mul _).symm)
    exact this
  have hu6 : ((A.u⁻¹ : Fˣ) : F) ^ 6 = 1 := by
    have := mul_right_cancel₀ hc₆ (h6.trans (one_mul _).symm)
    exact this
  have hv2 : ((A.u⁻¹ : Fˣ) : F) ^ 2 = 1 := by
    have hne : ((A.u⁻¹ : Fˣ) : F) ^ 4 ≠ 0 := by rw [hu4]; exact one_ne_zero
    have : ((A.u⁻¹ : Fˣ) : F) ^ 4 * ((A.u⁻¹ : Fˣ) : F) ^ 2 = ((A.u⁻¹ : Fˣ) : F) ^ 4 * 1 := by
      rw [← pow_add, mul_one]; exact hu6.trans hu4.symm
    exact mul_left_cancel₀ hne this
  have hu2 : ((A.u : F)) ^ 2 = 1 := by
    have hmul : ((A.u : F)) * ((A.u⁻¹ : Fˣ) : F) = 1 := by
      rw [Units.val_inv_eq_inv_val]; exact mul_inv_cancel₀ A.u.ne_zero
    calc ((A.u : F)) ^ 2 = ((A.u : F)) ^ 2 * (((A.u⁻¹ : Fˣ) : F) ^ 2) := by rw [hv2, mul_one]
      _ = (((A.u : F)) * ((A.u⁻¹ : Fˣ) : F)) ^ 2 := by ring
      _ = 1 := by rw [hmul, one_pow]
  refine ⟨hu2, ?_⟩
  have h2 : (A • W).b₂ = W.b₂ := by rw [h]
  have h4' : (A • W).b₄ = W.b₄ := by rw [h]
  rw [variableChange_b₂, hv2, one_mul] at h2
  rw [variableChange_b₄] at h4'
  have hv4 : ((A.u⁻¹ : Fˣ) : F) ^ 4 = 1 := hu4
  rw [hv4, one_mul] at h4'
  have e1 : 12 * A.r = 0 := by linear_combination h2
  have e2 : A.r * W.b₂ + 6 * A.r ^ 2 = 0 := by linear_combination h4'
  have e3 : A.r * W.c₄ = 0 := by
    have hc : W.c₄ = W.b₂ ^ 2 - 24 * W.b₄ := rfl
    rw [hc]
    linear_combination (W.b₂ - 6 * A.r) * e2 + (3 * A.r ^ 2 - 2 * W.b₄) * e1
  rcases mul_eq_zero.1 e3 with h0 | h0
  · exact h0
  · exact absurd h0 hc₄

theorem exists_pointEquiv_of_smul_eq {F : Type u} [Field F] [DecidableEq F] (C : VariableChange F)
    (W V : WeierstrassCurve F) (h : C • W = V) :
    ∃ e : V.toAffine.Point ≃+ W.toAffine.Point,
      ∀ (x y : F) (hxy : V.toAffine.Nonsingular x y),
        ∃ h' : W.toAffine.Nonsingular ((C.u : F) ^ 2 * x + C.r)
            ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t),
          e (.some x y hxy) = .some ((C.u : F) ^ 2 * x + C.r)
            ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) h' := by
  subst h
  let e₀ : (C • W).toAffine.Point ≃ W.toAffine.Point := Point.variableChangeEquiv C W
  have hinv : ∀ P Q : W.toAffine.Point, e₀.symm (P + Q) = e₀.symm P + e₀.symm Q :=
    fun P Q => Point.vcInvFun_add C W P Q
  let eI : W.toAffine.Point ≃+ (C • W).toAffine.Point := AddEquiv.mk' e₀.symm hinv
  refine ⟨eI.symm, fun x y hxy => ?_⟩
  refine ⟨(nonsingular_variableChange_iff x y).mp hxy, ?_⟩
  show e₀ (.some x y hxy) = _
  rfl

theorem exists_eq_of_nsmul_eq_zero {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) (N : ℕ) [NeZero N]
    (hA : Nat.card {P : A // N • P = 0} = N ^ 2) (hB : Nat.card {Q : B // N • Q = 0} = N ^ 2)
    (Q : B) (hQ : N • Q = 0) : ∃ P : A, N • P = 0 ∧ f P = Q := by
  haveI : Finite {Q : B // N • Q = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact pow_ne_zero 2 (NeZero.ne N))
  let g : {P : A // N • P = 0} → {Q : B // N • Q = 0} := fun P =>
    ⟨f P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hg : Function.Injective g := fun P P' h => Subtype.ext (hf (congrArg Subtype.val h))
  have hbij := hg.bijective_of_nat_card_le (by rw [hA, hB])
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, P.2, congrArg Subtype.val hP⟩

theorem natCard_torsion_of_isAlgClosed {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω] [DecidableEq Ω] (E : WeierstrassCurve k) [E.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : Ω) ≠ 0) :
    Nat.card {Q : (E.baseChange Ω).toAffine.Point // N • Q = 0} = N ^ 2 := by
  obtain ⟨e⟩ := E.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := Ω) hN
  have h1 : Nat.card (Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point N) = N ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Q => ?_)
  rw [Submodule.mem_torsionBy_iff]
  change N • Q = 0 ↔ ((N : ℤ)) • Q = 0
  rw [natCast_zsmul]

theorem mem_range_of_fixed {Ω : Type u} [Field Ω] {L : Type v} [Field L] [Algebra Ω L]
    [IsAlgClosure Ω L] (α : L) (p : Polynomial Ω) (hsep : p.Separable)
    (hroot : (p.map (algebraMap Ω L)).IsRoot α)
    (hfix : ∀ τ : L ≃ₐ[Ω] L, τ α = α) : α ∈ Set.range (algebraMap Ω L) := by
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed Ω
  haveI : Algebra.IsAlgebraic Ω L := IsAlgClosure.isAlgebraic
  haveI : Normal Ω L := ⟨fun x => IsAlgClosed.splits _⟩
  have hint : IsIntegral Ω α := Algebra.IsIntegral.isIntegral α
  have hmin_dvd : minpoly Ω α ∣ p := minpoly.dvd Ω α (by
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def] at hroot)
  have hmin_sep : (minpoly Ω α).Separable := hsep.of_dvd hmin_dvd
  have hroots : ∀ β : L, (minpoly Ω α).map (algebraMap Ω L) |>.IsRoot β → β = α := by
    intro β hβ
    have hβ' : β ∈ ((minpoly Ω α).map (algebraMap Ω L)).roots :=
      (Polynomial.mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hint))).2 hβ
    let f₀ : IntermediateField.adjoin Ω ({α} : Set L) →ₐ[Ω] L :=
      (IntermediateField.algHomAdjoinIntegralEquiv Ω hint).symm ⟨β, hβ'⟩
    have hf₀ : f₀ (IntermediateField.AdjoinSimple.gen Ω α) = β :=
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen Ω hint _
    let f₁ : L →ₐ[Ω] L := f₀.liftNormal L
    let τ : L ≃ₐ[Ω] L := AlgEquiv.ofBijective f₁ (Algebra.IsAlgebraic.algHom_bijective f₁)
    have hτ : τ α = β := by
      change f₁ α = β
      have := AlgHom.liftNormal_commutes f₀ L (IntermediateField.AdjoinSimple.gen Ω α)
      rw [IntermediateField.AdjoinSimple.algebraMap_gen] at this
      change f₁ α = algebraMap L L (f₀ _) at this
      rw [this, hf₀]; rfl
    rw [← hτ, hfix τ]
  have hsplit : ((minpoly Ω α).map (algebraMap Ω L)).Splits := IsAlgClosed.splits _
  have hcard : ((minpoly Ω α).map (algebraMap Ω L)).roots.card = (minpoly Ω α).natDegree := by
    rw [← Polynomial.natDegree_map (algebraMap Ω L)]
    exact (Polynomial.splits_iff_card_roots.1 hsplit)
  have hnodup : ((minpoly Ω α).map (algebraMap Ω L)).roots.Nodup :=
    Polynomial.nodup_roots hmin_sep.map
  have hall : ∀ b ∈ ((minpoly Ω α).map (algebraMap Ω L)).roots, b = α := fun β hβ =>
    hroots β ((Polynomial.mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hint))).1 hβ)
  have hrep := Multiset.eq_replicate_card.2 hall
  have hle : ((minpoly Ω α).map (algebraMap Ω L)).roots.card ≤ 1 := by
    classical
    have hc := (Multiset.nodup_iff_count_le_one.1 hnodup) α
    rw [hrep, Multiset.count_replicate_self] at hc
    exact hc
  have hdeg : (minpoly Ω α).natDegree = 1 := by
    have h1 : 0 < (minpoly Ω α).natDegree := minpoly.natDegree_pos hint
    omega
  exact minpoly.mem_range_of_degree_eq_one Ω α (by
    rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), hdeg]; rfl)

theorem isSeparable_of_eq (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M]
    {Γ : Subgroup SL(2, ℤ)} (hΓ : Γ = CongruenceSubgroup.Gamma1 M)
    (x : qExpFunctionFieldC K Γ) (hx : (x : LaurentSeries K) = jqModC K) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ)))
      (qExpFunctionFieldC K Γ) := by
  subst hΓ
  exact ModularCurve.isSeparable_adjoin_qExpFunctionFieldC_gamma1 K M x hx

section Universal

variable {K : Type u} [Field K] {k Ω : Type v} [Field k] [Field Ω] [DecidableEq Ω]
  [Algebra K k] [Algebra K Ω] [Algebra k Ω] [IsScalarTower K k Ω]
  {E : WeierstrassCurve k} [E.IsElliptic] {L : Type w} [Field L] [Algebra K L]
  {M : ℕ}

noncomputable def sprd (P₀ : (E.baseChange Ω).toAffine.Point) (ψ₀ : L →ₐ[K] Ω)
    (Q : (E.baseChange Ω).toAffine.Point) : L →ₐ[K] Ω := by
  classical
  exact if h : ∃ σ : Ω ≃ₐ[k] Ω, Q = Point.map (σ : Ω →ₐ[k] Ω) P₀ then
    ((h.choose : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀ else ψ₀

variable (P₀ : (E.baseChange Ω).toAffine.Point) (ψ₀ : L →ₐ[K] Ω)
  (hP₀ : addOrderOf P₀ = M)
  (hstab : ∀ σ : Ω ≃ₐ[k] Ω,
    (Point.map (σ : Ω →ₐ[k] Ω) P₀ = P₀ ∨ Point.map (σ : Ω →ₐ[k] Ω) P₀ = -P₀) →
      ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀ = ψ₀)
  (hconv : ∀ σ : Ω ≃ₐ[k] Ω, ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀ = ψ₀ →
    (Point.map (σ : Ω →ₐ[k] Ω) P₀ = P₀ ∨ Point.map (σ : Ω →ₐ[k] Ω) P₀ = -P₀))
  (htrans : ∀ P P' : (E.baseChange Ω).toAffine.Point, addOrderOf P = M → addOrderOf P' = M →
    ∃ σ : Ω ≃ₐ[k] Ω, P' = Point.map (σ : Ω →ₐ[k] Ω) P)

include hP₀ htrans in
theorem sprd_spec {Q : (E.baseChange Ω).toAffine.Point} (hQ : addOrderOf Q = M) :
    ∃ σ : Ω ≃ₐ[k] Ω, Q = Point.map (σ : Ω →ₐ[k] Ω) P₀ ∧
      ∀ f, sprd P₀ ψ₀ Q f = σ (ψ₀ f) := by
  classical
  have h : ∃ σ : Ω ≃ₐ[k] Ω, Q = Point.map (σ : Ω →ₐ[k] Ω) P₀ := htrans P₀ Q hP₀ hQ
  refine ⟨h.choose, h.choose_spec, fun f => ?_⟩
  unfold sprd
  rw [dif_pos h]
  rfl

include hstab in

theorem stab_apply (ρ : Ω ≃ₐ[k] Ω)
    (hρ : Point.map (ρ : Ω →ₐ[k] Ω) P₀ = P₀ ∨ Point.map (ρ : Ω →ₐ[k] Ω) P₀ = -P₀) (f : L) :
    ρ (ψ₀ f) = ψ₀ f := by
  have := congrArg (fun φ : L →ₐ[K] Ω => φ f) (hstab ρ hρ)
  exact this

omit [IsScalarTower K k Ω] in

theorem map_eq_self_of_forall {f : Ω →ₐ[k] Ω} (hf : ∀ z, f z = z)
    (P : (E.baseChange Ω).toAffine.Point) : Point.map f P = P := by
  rcases P with (_ | ⟨x, y, h⟩)
  · rfl
  · have hx : f x = x := hf x
    have hy : f y = y := hf y
    simp only [Point.map_some, hx, hy]

omit [IsScalarTower K k Ω] in
theorem map_symm_map (σ : Ω ≃ₐ[k] Ω) (P : (E.baseChange Ω).toAffine.Point) :
    Point.map ((σ.symm : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω) (Point.map (σ : Ω →ₐ[k] Ω) P) = P := by
  rw [Point.map_map]
  exact map_eq_self_of_forall (fun z => σ.symm_apply_apply z) P

omit [IsScalarTower K k Ω] in
theorem map_map_symm (σ : Ω ≃ₐ[k] Ω) (P : (E.baseChange Ω).toAffine.Point) :
    Point.map (σ : Ω →ₐ[k] Ω) (Point.map ((σ.symm : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω) P) = P := by
  rw [Point.map_map]
  exact map_eq_self_of_forall (fun z => σ.apply_symm_apply z) P

include hP₀ hstab htrans in

theorem sprd_self (f : L) : sprd P₀ ψ₀ P₀ f = ψ₀ f := by
  obtain ⟨σ₁, hσ₁, hval₁⟩ := sprd_spec P₀ ψ₀ hP₀ htrans hP₀
  rw [hval₁]
  exact stab_apply P₀ ψ₀ hstab σ₁ (Or.inl hσ₁.symm) f

include hP₀ hstab htrans in

theorem sprd_natural {Q : (E.baseChange Ω).toAffine.Point} (hQ : addOrderOf Q = M)
    (τ : Ω ≃ₐ[k] Ω) (f : L) :
    sprd P₀ ψ₀ (Point.map (τ : Ω →ₐ[k] Ω) Q) f = τ (sprd P₀ ψ₀ Q f) := by
  have hτQ : addOrderOf (Point.map (τ : Ω →ₐ[k] Ω) Q) = M := by
    rw [addOrderOf_injective _ (Point.map_injective (τ : Ω →ₐ[k] Ω)) Q, hQ]
  obtain ⟨σ, hσ, hval⟩ := sprd_spec P₀ ψ₀ hP₀ htrans hQ
  obtain ⟨σ₁, hσ₁, hval₁⟩ := sprd_spec P₀ ψ₀ hP₀ htrans hτQ
  rw [hval, hval₁]

  let ρ : Ω ≃ₐ[k] Ω := (σ.trans τ).trans σ₁.symm
  have hρapp : ∀ z, ρ z = σ₁.symm (τ (σ z)) := fun z => rfl
  have hcomp : (ρ : Ω →ₐ[k] Ω) =
      ((σ₁.symm : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω).comp ((τ : Ω →ₐ[k] Ω).comp (σ : Ω →ₐ[k] Ω)) := by
    ext z; rfl
  have hρ : Point.map (ρ : Ω →ₐ[k] Ω) P₀ = P₀ ∨ Point.map (ρ : Ω →ₐ[k] Ω) P₀ = -P₀ := by
    left
    rw [hcomp, ← Point.map_map, ← Point.map_map, ← hσ, hσ₁, map_symm_map]
  have hfix := stab_apply P₀ ψ₀ hstab ρ hρ f
  rw [hρapp] at hfix
  have := congrArg σ₁ hfix
  rw [σ₁.apply_symm_apply] at this
  exact this.symm

include hP₀ hstab htrans in

theorem sprd_neg {Q : (E.baseChange Ω).toAffine.Point} (hQ : addOrderOf Q = M) (f : L) :
    sprd P₀ ψ₀ (-Q) f = sprd P₀ ψ₀ Q f := by
  have hnQ : addOrderOf (-Q) = M := by rw [addOrderOf_neg, hQ]
  obtain ⟨σ, hσ, hval⟩ := sprd_spec P₀ ψ₀ hP₀ htrans hQ
  obtain ⟨σ₁, hσ₁, hval₁⟩ := sprd_spec P₀ ψ₀ hP₀ htrans hnQ
  rw [hval, hval₁]
  let ρ : Ω ≃ₐ[k] Ω := σ₁.trans σ.symm
  have hρapp : ∀ z, ρ z = σ.symm (σ₁ z) := fun z => rfl
  have hcomp : (ρ : Ω →ₐ[k] Ω) =
      ((σ.symm : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω).comp (σ₁ : Ω →ₐ[k] Ω) := by
    ext z; rfl
  have hρ : Point.map (ρ : Ω →ₐ[k] Ω) P₀ = P₀ ∨ Point.map (ρ : Ω →ₐ[k] Ω) P₀ = -P₀ := by
    right
    rw [hcomp, ← Point.map_map, ← hσ₁, hσ, ← map_neg, map_symm_map]
  have hfix := stab_apply P₀ ψ₀ hstab ρ hρ f
  rw [hρapp] at hfix
  have := congrArg σ hfix
  rw [σ.apply_symm_apply] at this
  exact this

include hP₀ htrans in
theorem sprd_apply_of_eq {Q : (E.baseChange Ω).toAffine.Point}
    (hQ : addOrderOf Q = M) {z : L} {c : k} (hz : ψ₀ z = algebraMap k Ω c) :
    sprd P₀ ψ₀ Q z = algebraMap k Ω c := by
  obtain ⟨σ, hσ, hval⟩ := sprd_spec P₀ ψ₀ hP₀ htrans hQ
  rw [hval, hz, AlgEquiv.commutes]

include hP₀ hconv htrans in

theorem sprd_eq_imp {Q Q' : (E.baseChange Ω).toAffine.Point} (hQ : addOrderOf Q = M)
    (hQ' : addOrderOf Q' = M) (h : ∀ f, sprd P₀ ψ₀ Q' f = sprd P₀ ψ₀ Q f) :
    Q' = Q ∨ Q' = -Q := by
  obtain ⟨σ, hσ, hval⟩ := sprd_spec P₀ ψ₀ hP₀ htrans hQ
  obtain ⟨σ', hσ', hval'⟩ := sprd_spec P₀ ψ₀ hP₀ htrans hQ'
  let ρ : Ω ≃ₐ[k] Ω := σ'.trans σ.symm
  have hρapp : ∀ z, ρ z = σ.symm (σ' z) := fun z => rfl
  have hfix : ((ρ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ₀ = ψ₀ := by
    apply AlgHom.ext
    intro f
    change ρ (ψ₀ f) = ψ₀ f
    rw [hρapp, ← hval', h f, hval, σ.symm_apply_apply]
  have hρP := hconv ρ hfix
  have hcomp : (ρ : Ω →ₐ[k] Ω) =
      ((σ.symm : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω).comp (σ' : Ω →ₐ[k] Ω) := by
    ext z; rfl
  rw [hcomp, ← Point.map_map, ← hσ'] at hρP
  rcases hρP with h1 | h1
  · left
    have := congrArg (Point.map (σ : Ω →ₐ[k] Ω)) h1
    rw [map_map_symm] at this
    rw [this, hσ]
  · right
    have := congrArg (Point.map (σ : Ω →ₐ[k] Ω)) h1
    rw [map_map_symm, map_neg] at this
    rw [this, hσ]

include hP₀ hstab htrans in

theorem sprd_dia {g : L → L} {σγ : Ω ≃ₐ[k] Ω} {n : ℕ}
    (hσγP : Point.map (σγ : Ω →ₐ[k] Ω) P₀ = n • P₀) (hσγψ : ∀ f, ψ₀ (g f) = σγ (ψ₀ f))
    {Q : (E.baseChange Ω).toAffine.Point} (hQ : addOrderOf Q = M) (f : L) :
    sprd P₀ ψ₀ (n • Q) f = sprd P₀ ψ₀ Q (g f) := by
  obtain ⟨σ, hσ, hval⟩ := sprd_spec P₀ ψ₀ hP₀ htrans hQ
  let τ : Ω ≃ₐ[k] Ω := σγ.trans σ
  have hτapp : ∀ z, τ z = σ (σγ z) := fun z => rfl
  have hcomp : (τ : Ω →ₐ[k] Ω) = (σ : Ω →ₐ[k] Ω).comp (σγ : Ω →ₐ[k] Ω) := by
    ext z; rfl
  have hnQ : n • Q = Point.map (τ : Ω →ₐ[k] Ω) P₀ := by
    rw [hcomp, ← Point.map_map, hσγP, map_nsmul, ← hσ]
  rw [hnQ, sprd_natural P₀ ψ₀ hP₀ hstab htrans hP₀ τ f, sprd_self P₀ ψ₀ hP₀ hstab htrans f,
    hτapp, hval, hσγψ]

end Universal

section Main

variable (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)

local notation "Fb" => qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)

variable
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))
    (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2)

theorem ne_of_transcendental {R A : Type*} [Field R] [Field A] [Algebra R A] {a : A}
    (ha : Transcendental R a) (n : ℕ) : a ≠ (n : A) := by
  intro h
  apply ha
  rw [h, show ((n : A)) = algebraMap R A n by simp]
  exact isAlgebraic_algebraMap _

theorem c₄_ne_zero_of_transcendental_j {A : Type*} [Field A] {R : Type*} [Field R] [Algebra R A]
    (W : WeierstrassCurve A) [W.IsElliptic] (hW : Transcendental R W.j) : W.c₄ ≠ 0 := by
  intro h
  have : W.j = 0 := W.j_eq_zero h
  exact ne_of_transcendental hW 0 (by rw [this, Nat.cast_zero])

theorem c₆_ne_zero_of_transcendental_j {A : Type*} [Field A] {R : Type*} [Field R] [Algebra R A]
    (W : WeierstrassCurve A) [W.IsElliptic] (hW : Transcendental R W.j) : W.c₆ ≠ 0 := by
  intro h
  have hrel := W.c_relation
  rw [h, zero_pow two_ne_zero, sub_zero] at hrel
  have : W.j = 1728 := by
    rw [WeierstrassCurve.j, ← hrel, ← W.coe_Δ', mul_left_comm, Units.inv_mul, mul_one]
  exact ne_of_transcendental hW 1728 (by rw [this]; norm_num)

include hM hx hE hfull in
theorem main :
    ∃ Ψ : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M} →
        {ψ : Fb →ₐ[K] Ω // ψ x = algebraMap k Ω E.j},
      (∀ (σ : Ω ≃ₐ[k] Ω) (P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}),
        P'.1 = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P.1 →
          ((Ψ P').1 : Fb →ₐ[K] Ω) = ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Ψ P).1) ∧
      (∀ (ρ : CongruenceSubgroup.Gamma0 M →* (Fb ≃ₐ[K] Fb)),
        IsDiamondPullbackModL K M ⊥ ρ →
        ∀ (γ : CongruenceSubgroup.Gamma0 M)
          (P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}),
          P'.1 = ((((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M).val) • P.1 →
            ((Ψ P').1 : Fb →ₐ[K] Ω) = ((Ψ P).1 : Fb →ₐ[K] Ω).comp (ρ γ : Fb →ₐ[K] Fb)) ∧
      (∀ P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M},
        P'.1 = -P.1 → Ψ P' = Ψ P) ∧
      (∀ P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M},
        Ψ P' = Ψ P → P'.1 = P.1 ∨ P'.1 = -P.1) := by
  classical

  let Ωb := AlgebraicClosure Ω
  let k₀ : IntermediateField K k := IntermediateField.adjoin K ({E.j} : Set k)
  haveI : IsScalarTower k₀ k Ωb := inferInstance
  haveI : IsScalarTower K k Ωb := inferInstance
  haveI : IsScalarTower K k₀ Ωb := inferInstance
  haveI : IsScalarTower k Ω Ωb := inferInstance
  haveI : IsScalarTower K Ω Ωb := inferInstance
  let Ω₀ : IntermediateField k₀ Ωb := algebraicClosure k₀ Ωb
  haveI : IsAlgClosure k₀ Ω₀ := inferInstance
  haveI : IsScalarTower K k₀ Ω₀ := inferInstance
  haveI : IsAlgClosed Ω₀ := IsAlgClosure.isAlgClosed k₀
  let t : k₀ := ⟨E.j, IntermediateField.mem_adjoin_simple_self K E.j⟩
  let E₀ : WeierstrassCurve k₀ := WeierstrassCurve.ofJ t
  haveI : E₀.IsElliptic := inferInstance
  have hE₀j : E₀.j = t := WeierstrassCurve.ofJ_j t
  have ht : algebraMap k₀ k t = E.j := rfl
  have hE₀ : Transcendental K E₀.j := by
    rw [hE₀j, ← transcendental_algebraMap_iff (algebraMap k₀ k).injective, ht]
    exact hE
  have hgen : IntermediateField.adjoin K ({E₀.j} : Set k₀) = ⊤ := by
    rw [hE₀j]
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
  have hMΩb : (M : Ωb) ≠ 0 := fun h =>
    hM ((algebraMap K Ωb).injective (by rw [map_natCast, map_zero]; exact h))
  have hMΩ₀ : (M : Ω₀) ≠ 0 := fun h =>
    hM ((algebraMap K Ω₀).injective (by rw [map_natCast, map_zero]; exact h))

  obtain ⟨P₀, ψ₀, hP₀, hψ₀x, hiff, hdia0⟩ :=
    ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j
      K M hM x hx k₀ Ω₀ E₀ hE₀ hgen
  have hstab : ∀ σ : Ω₀ ≃ₐ[k₀] Ω₀,
      (Point.map (σ : Ω₀ →ₐ[k₀] Ω₀) P₀ = P₀ ∨ Point.map (σ : Ω₀ →ₐ[k₀] Ω₀) P₀ = -P₀) →
        ((σ : Ω₀ →ₐ[k₀] Ω₀).restrictScalars K).comp ψ₀ = ψ₀ := fun σ h => (hiff σ).1 h
  have hconv : ∀ σ : Ω₀ ≃ₐ[k₀] Ω₀, ((σ : Ω₀ →ₐ[k₀] Ω₀).restrictScalars K).comp ψ₀ = ψ₀ →
      (Point.map (σ : Ω₀ →ₐ[k₀] Ω₀) P₀ = P₀ ∨ Point.map (σ : Ω₀ →ₐ[k₀] Ω₀) P₀ = -P₀) :=
    fun σ h => (hiff σ).2 h
  have htrans := WeierstrassCurve.exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j
    K M hM k₀ Ω₀ E₀ hE₀ hgen

  let ι₀ : Ω₀ →ₐ[k₀] Ωb := IntermediateField.val Ω₀
  have hι₀ : ∀ z : Ω₀, ι₀ z = (z : Ωb) := fun z => rfl
  let W : WeierstrassCurve Ωb := E₀.baseChange Ωb
  let ι₀p : (E₀.baseChange Ω₀).toAffine.Point →+ W.toAffine.Point := Point.map ι₀
  have hι₀p : Function.Injective ι₀p := Point.map_injective ι₀
  let V : WeierstrassCurve Ωb := E.baseChange Ωb
  let ι : Ω →ₐ[k] Ωb := IsScalarTower.toAlgHom k Ω Ωb
  have hιalg : ∀ z : Ω, ι z = algebraMap Ω Ωb z := fun z => rfl
  let ιp : (E.baseChange Ω).toAffine.Point →+ V.toAffine.Point := Point.map ι
  have hιp : Function.Injective ιp := Point.map_injective ι
  haveI : W.IsElliptic := show (E₀.map _).IsElliptic from inferInstance
  haveI : V.IsElliptic := show (E.map _).IsElliptic from inferInstance
  have hWj : W.j = algebraMap k Ωb E.j := by
    change (E₀.map (algebraMap k₀ Ωb)).j = _
    rw [WeierstrassCurve.map_j, hE₀j]
    rfl
  have hjWV : W.j = V.j := by
    rw [hWj]
    change _ = (E.map (algebraMap k Ωb)).j
    rw [WeierstrassCurve.map_j]
  have hWtr : Transcendental K W.j := by
    rw [hWj]
    exact (transcendental_algebraMap_iff (algebraMap k Ωb).injective).2 hE
  have hc₄ : W.c₄ ≠ 0 := c₄_ne_zero_of_transcendental_j W hWtr
  have hc₆ : W.c₆ ≠ 0 := c₆_ne_zero_of_transcendental_j W hWtr
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq (E := W) (E' := V) hjWV
  obtain ⟨e, he⟩ := exists_pointEquiv_of_smul_eq C W V hC

  have hWmap : ∀ τ : Ωb ≃ₐ[k] Ωb, W.map ((τ.restrictScalars k₀ : Ωb ≃ₐ[k₀] Ωb) : Ωb →ₐ[k₀] Ωb) = W :=
    fun τ => WeierstrassCurve.map_baseChange E₀ _
  have hVmap : ∀ τ : Ωb ≃ₐ[k] Ωb, V.map (τ : Ωb →ₐ[k] Ωb) = V :=
    fun τ => WeierstrassCurve.map_baseChange E _
  have hfixC : ∀ τ : Ωb ≃ₐ[k] Ωb, τ ((C.u : Ωb) ^ 2) = (C.u : Ωb) ^ 2 ∧ τ C.r = C.r := by
    intro τ
    have h1 : (C.map (τ : Ωb →+* Ωb)) • W = V := by
      have := congrArg (fun X : WeierstrassCurve Ωb => X.map (τ : Ωb →+* Ωb)) hC
      rw [← WeierstrassCurve.map_variableChange] at this
      have hW' : W.map (τ : Ωb →+* Ωb) = W := hWmap τ
      have hV' : V.map (τ : Ωb →+* Ωb) = V := hVmap τ
      rw [hW', hV'] at this
      exact this
    have h2 : (C⁻¹ * C.map (τ : Ωb →+* Ωb)) • W = W := by
      rw [mul_smul, h1, ← hC, inv_smul_smul]
    obtain ⟨hu, hr⟩ := u_sq_eq_one_and_r_eq_zero_of_smul_eq _ W h2 hc₄ hc₆
    simp only [VariableChange.mul_def, VariableChange.inv_def, VariableChange.map, Units.val_mul,
      Units.coe_map, MonoidHom.coe_coe, RingHom.coe_coe] at hu hr
    have hu0 : (C.u : Ωb) ≠ 0 := C.u.ne_zero
    have hui : ((C.u⁻¹ : Ωbˣ) : Ωb) = (C.u : Ωb)⁻¹ := Units.val_inv_eq_inv_val C.u
    rw [hui] at hu hr
    rw [mul_pow, inv_pow, inv_mul_eq_one₀ (pow_ne_zero 2 hu0)] at hu
    have hτu : τ ((C.u : Ωb) ^ 2) = (C.u : Ωb) ^ 2 := by rw [map_pow]; exact hu.symm
    refine ⟨hτu, ?_⟩
    rw [← hu, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hu0), mul_one] at hr
    exact (neg_add_eq_zero.1 hr).symm

  have hres : ∀ τ : Ωb ≃ₐ[k] Ωb, ∃ τ₀ : Ω₀ ≃ₐ[k₀] Ω₀, ∀ z : Ω₀, ((τ₀ z : Ω₀) : Ωb) = τ z := by
    intro τ
    exact ⟨algebraicClosure.algEquivOfAlgEquiv (τ.restrictScalars k₀ : Ωb ≃ₐ[k₀] Ωb),
      fun z => rfl⟩
  let mW : (Ωb ≃ₐ[k] Ωb) → W.toAffine.Point →+ W.toAffine.Point := fun τ =>
    Point.map ((τ.restrictScalars k₀ : Ωb ≃ₐ[k₀] Ωb) : Ωb →ₐ[k₀] Ωb)
  let mV : (Ωb ≃ₐ[k] Ωb) → V.toAffine.Point →+ V.toAffine.Point := fun τ =>
    Point.map (τ : Ωb →ₐ[k] Ωb)
  have hmWι₀ : ∀ (τ : Ωb ≃ₐ[k] Ωb) (τ₀ : Ω₀ ≃ₐ[k₀] Ω₀),
      (∀ z : Ω₀, ((τ₀ z : Ω₀) : Ωb) = τ z) → ∀ Q : (E₀.baseChange Ω₀).toAffine.Point,
        mW τ (ι₀p Q) = ι₀p (Point.map (τ₀ : Ω₀ →ₐ[k₀] Ω₀) Q) := by
    intro τ τ₀ hτ₀ Q
    change Point.map _ (Point.map ι₀ Q) = Point.map ι₀ (Point.map _ Q)
    have hc : ((τ.restrictScalars k₀ : Ωb ≃ₐ[k₀] Ωb) : Ωb →ₐ[k₀] Ωb).comp ι₀ =
        ι₀.comp (τ₀ : Ω₀ →ₐ[k₀] Ω₀) := by
      ext z
      exact (hτ₀ z).symm
    rw [Point.map_map, Point.map_map, hc]
  have hsign : ∀ (τ : Ωb ≃ₐ[k] Ωb) (R : V.toAffine.Point),
      e (mV τ R) = mW τ (e R) ∨ e (mV τ R) = -(mW τ (e R)) := by
    intro τ R
    rcases R with (_ | ⟨xR, yR, hR⟩)
    · left
      change e (Point.map _ 0) = Point.map _ (e 0)
      rw [map_zero, map_zero, map_zero]
    · obtain ⟨hτu, hτr⟩ := hfixC τ
      have hmapV : ∀ (a b : Ωb) (hab : V.toAffine.Nonsingular a b),
          ∃ h', mV τ (.some a b hab) = .some (τ a) (τ b) h' := fun a b hab => ⟨_, rfl⟩
      have hmapW : ∀ (a b : Ωb) (hab : W.toAffine.Nonsingular a b),
          ∃ h', mW τ (.some a b hab) = .some (τ a) (τ b) h' := fun a b hab => ⟨_, rfl⟩
      obtain ⟨hR', hmap⟩ := hmapV xR yR hR
      obtain ⟨h₁, he₁⟩ := he (τ xR) (τ yR) hR'
      obtain ⟨h₂, he₂⟩ := he xR yR hR
      rw [hmap, he₁, he₂]
      obtain ⟨h₃, hmap'⟩ := hmapW ((C.u : Ωb) ^ 2 * xR + C.r)
          ((C.u : Ωb) ^ 3 * yR + (C.u : Ωb) ^ 2 * C.s * xR + C.t) h₂
      rw [hmap']
      apply Point.X_eq_iff.1
      rw [map_add, map_mul, hτu, hτr]

  have htorW : Nat.card {Q : W.toAffine.Point // M • Q = 0} = M ^ 2 :=
    natCard_torsion_of_isAlgClosed (Ω := Ωb) E₀ M hMΩb
  have htor₀ : Nat.card {Q : (E₀.baseChange Ω₀).toAffine.Point // M • Q = 0} = M ^ 2 :=
    natCard_torsion_of_isAlgClosed (Ω := Ω₀) E₀ M hMΩ₀
  have hhit : ∀ R : W.toAffine.Point, M • R = 0 →
      ∃ Q : (E₀.baseChange Ω₀).toAffine.Point, M • Q = 0 ∧ ι₀p Q = R :=
    exists_eq_of_nsmul_eq_zero ι₀p hι₀p M htor₀ htorW
  have hav : ∀ P : (E.baseChange Ω).toAffine.Point, M • P = 0 →
      ∃ Q : (E₀.baseChange Ω₀).toAffine.Point, ι₀p Q = e (ιp P) := by
    intro P hP
    obtain ⟨Q, -, hQ⟩ := hhit (e (ιp P)) (by rw [← map_nsmul, ← map_nsmul, hP, map_zero, map_zero])
    exact ⟨Q, hQ⟩
  let av : (E.baseChange Ω).toAffine.Point → (E₀.baseChange Ω₀).toAffine.Point := fun P =>
    if h : M • P = 0 then (hav P h).choose else 0
  have hav_spec : ∀ P : (E.baseChange Ω).toAffine.Point, M • P = 0 → ι₀p (av P) = e (ιp P) := by
    intro P hP
    simp only [av, dif_pos hP]
    exact (hav P hP).choose_spec
  have hav_ord : ∀ P : (E.baseChange Ω).toAffine.Point, addOrderOf P = M → addOrderOf (av P) = M := by
    intro P hP
    have hP0 : M • P = 0 := by rw [← hP]; exact addOrderOf_nsmul_eq_zero P
    have h1 := addOrderOf_injective ι₀p hι₀p (av P)
    rw [hav_spec P hP0, AddEquiv.addOrderOf_eq e, addOrderOf_injective ιp hιp, hP] at h1
    exact h1.symm

  have hav_nsmul : ∀ (P : (E.baseChange Ω).toAffine.Point) (n : ℕ), M • P = 0 →
      av (n • P) = n • av P := by
    intro P n hP
    have hnP : M • (n • P) = 0 := by rw [smul_comm, hP, smul_zero]
    apply hι₀p
    rw [hav_spec _ hnP, map_nsmul, map_nsmul, map_nsmul, hav_spec P hP]
  have hav_neg : ∀ P : (E.baseChange Ω).toAffine.Point, M • P = 0 → av (-P) = -(av P) := by
    intro P hP
    apply hι₀p
    rw [hav_spec _ (by rw [smul_neg, hP, neg_zero]), map_neg, map_neg, map_neg, hav_spec P hP]
  have hav_nat : ∀ (τ : Ωb ≃ₐ[k] Ωb) (τ₀ : Ω₀ ≃ₐ[k₀] Ω₀),
      (∀ z : Ω₀, ((τ₀ z : Ω₀) : Ωb) = τ z) →
      ∀ P P₁ : (E.baseChange Ω).toAffine.Point, M • P = 0 → M • P₁ = 0 →
        ιp P₁ = mV τ (ιp P) →
          av P₁ = Point.map (τ₀ : Ω₀ →ₐ[k₀] Ω₀) (av P) ∨
            av P₁ = -(Point.map (τ₀ : Ω₀ →ₐ[k₀] Ω₀) (av P)) := by
    intro τ τ₀ hτ₀ P P₁ hP hP₁ hPP
    have h1 : ι₀p (av P₁) = e (mV τ (ιp P)) := by rw [hav_spec P₁ hP₁, hPP]
    rcases hsign τ (ιp P) with h2 | h2
    · left
      apply hι₀p
      rw [h1, h2, ← hav_spec P hP, hmWι₀ τ τ₀ hτ₀]
    · right
      apply hι₀p
      rw [h1, h2, ← hav_spec P hP, hmWι₀ τ τ₀ hτ₀, map_neg]

  let Φ := sprd (K := K) (k := k₀) (Ω := Ω₀) (E := E₀) P₀ ψ₀
  have hΦnat := fun {Q : (E₀.baseChange Ω₀).toAffine.Point} (hQ : addOrderOf Q = M) =>
    sprd_natural (K := K) P₀ ψ₀ hP₀ hstab htrans hQ
  have hΦneg := fun {Q : (E₀.baseChange Ω₀).toAffine.Point} (hQ : addOrderOf Q = M) =>
    sprd_neg (K := K) P₀ ψ₀ hP₀ hstab htrans hQ
  have hΦx : ∀ {Q : (E₀.baseChange Ω₀).toAffine.Point}, addOrderOf Q = M →
      Φ Q x = algebraMap k₀ Ω₀ t := fun hQ =>
    sprd_apply_of_eq (K := K) P₀ ψ₀ hP₀ htrans hQ (by rw [hψ₀x, hE₀j])
  let ι₀K : Ω₀ →ₐ[K] Ωb := ι₀.restrictScalars K
  let Ψ' : (E.baseChange Ω).toAffine.Point → (Fb →ₐ[K] Ωb) := fun P => ι₀K.comp (Φ (av P))
  have hΨ'app : ∀ P f, Ψ' P f = ((Φ (av P) f : Ω₀) : Ωb) := fun P f => rfl
  have hΨ'nat : ∀ (τ : Ωb ≃ₐ[k] Ωb) (P P₁ : (E.baseChange Ω).toAffine.Point),
      addOrderOf P = M → addOrderOf P₁ = M → ιp P₁ = mV τ (ιp P) →
        ∀ f, Ψ' P₁ f = τ (Ψ' P f) := by
    intro τ P P₁ hP hP₁ hPP f
    obtain ⟨τ₀, hτ₀⟩ := hres τ
    have hP0 : M • P = 0 := by rw [← hP]; exact addOrderOf_nsmul_eq_zero P
    have hP10 : M • P₁ = 0 := by rw [← hP₁]; exact addOrderOf_nsmul_eq_zero P₁
    rw [hΨ'app, hΨ'app, ← hτ₀]
    congr 1
    have hordτ : addOrderOf (Point.map (τ₀ : Ω₀ →ₐ[k₀] Ω₀) (av P)) = M := by
      rw [addOrderOf_injective _ (Point.map_injective _), hav_ord P hP]
    rcases hav_nat τ τ₀ hτ₀ P P₁ hP0 hP10 hPP with h1 | h1
    · show Φ (av P₁) f = τ₀ (Φ (av P) f)
      rw [h1]
      exact hΦnat (hav_ord P hP) τ₀ f
    · show Φ (av P₁) f = τ₀ (Φ (av P) f)
      rw [h1, hΦneg hordτ]
      exact hΦnat (hav_ord P hP) τ₀ f

  have hfixΩ : ∀ (P : (E.baseChange Ω).toAffine.Point), addOrderOf P = M →
      ∀ (τ : Ωb ≃ₐ[Ω] Ωb) (f), τ (Ψ' P f) = Ψ' P f := by
    intro P hP τ f
    let τk : Ωb ≃ₐ[k] Ωb := τ.restrictScalars k
    have hιτ : ιp P = mV τk (ιp P) := by
      change Point.map ι P = Point.map _ (Point.map ι P)
      have hc : (τk : Ωb →ₐ[k] Ωb).comp ι = ι := by
        ext z
        exact τ.commutes z
      rw [Point.map_map, hc]
    exact (hΨ'nat τk P P hP hP hιτ f).symm
  let ιK : Ω →ₐ[K] Ωb := ι.restrictScalars K
  have hιK : ∀ z, ιK z = algebraMap Ω Ωb z := fun z => rfl
  have hιKinj : Function.Injective ιK := (algebraMap Ω Ωb).injective
  haveI hsepF := isSeparable_of_eq K M (ModularCurve.GammaH_bot M) x hx
  have hΨ'x : ∀ P : (E.baseChange Ω).toAffine.Point, addOrderOf P = M →
      Ψ' P x = ιK (algebraMap k Ω E.j) := by
    intro P hP
    rw [hΨ'app, hΦx (hav_ord P hP), hιK, ← IsScalarTower.algebraMap_apply]
    rfl
  have hsepΩ : ∀ (P : (E.baseChange Ω).toAffine.Point), addOrderOf P = M → ∀ f,
      ∃ p : Polynomial Ω, p.Separable ∧ (p.map (algebraMap Ω Ωb)).IsRoot (Ψ' P f) := by
    intro P hP f
    set Kx := IntermediateField.adjoin K ({x} : Set Fb) with hKx
    have hsep : (minpoly Kx f).Separable := Algebra.IsSeparable.isSeparable Kx f
    let φ : Kx →+* Ωb := (Ψ' P).toRingHom.comp (algebraMap Kx _)
    have hφroot : ((minpoly Kx f).map φ).IsRoot (Ψ' P f) := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_map]
      change Polynomial.eval₂ ((Ψ' P).toRingHom.comp (algebraMap Kx _)) ((Ψ' P).toRingHom f)
        (minpoly Kx f) = 0
      rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    have hφΩ : ∀ z : Kx, φ z ∈ Set.range (algebraMap Ω Ωb) := by
      let T : IntermediateField K Fb := IntermediateField.comap (Ψ' P) ιK.fieldRange
      have hle : Kx ≤ T := by
        rw [hKx, IntermediateField.adjoin_le_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        change (Ψ' P) x ∈ ιK.fieldRange
        rw [hΨ'x P hP]
        exact ⟨_, rfl⟩
      intro z
      have hz : (z : Fb) ∈ T := hle z.2
      change (Ψ' P) z ∈ ιK.fieldRange at hz
      obtain ⟨w, hw⟩ := AlgHom.mem_fieldRange.1 hz
      exact ⟨w, hw⟩
    have hlift : (minpoly Kx f).map φ ∈ Polynomial.lifts (algebraMap Ω Ωb) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      exact hφΩ _
    obtain ⟨p, hp⟩ := (Polynomial.mem_lifts _).1 hlift
    refine ⟨p, ?_, ?_⟩
    · rw [← Polynomial.separable_map (algebraMap Ω Ωb), hp]
      exact hsep.map
    · rw [hp]; exact hφroot
  have hrange : ∀ (P : (E.baseChange Ω).toAffine.Point), addOrderOf P = M → ∀ f,
      Ψ' P f ∈ ιK.range := by
    intro P hP f
    obtain ⟨p, hpsep, hproot⟩ := hsepΩ P hP f
    obtain ⟨z, hz⟩ := mem_range_of_fixed (Ψ' P f) p hpsep hproot (fun τ => hfixΩ P hP τ f)
    exact ⟨z, hz⟩

  let eΩ : Ω ≃ₐ[K] ιK.range := AlgEquiv.ofInjective ιK hιKinj
  have heΩ : ∀ z : ιK.range, ιK (eΩ.symm z) = (z : Ωb) := fun z => by
    rw [← AlgEquiv.ofInjective_apply ιK hιKinj]; simp [eΩ]
  let Ψ₁ : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M} → (Fb →ₐ[K] Ω) := fun P =>
    (eΩ.symm : ιK.range →ₐ[K] Ω).comp ((Ψ' P.1).codRestrict ιK.range (hrange P.1 P.2))
  have hΨ₁ : ∀ (P : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}) (f),
      ιK (Ψ₁ P f) = Ψ' P.1 f := by
    intro P f
    change ιK (eΩ.symm _) = _
    rw [heΩ]
    rfl
  have hΨ₁x : ∀ P : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M},
      Ψ₁ P x = algebraMap k Ω E.j := by
    intro P
    apply hιKinj
    rw [hΨ₁, hΨ'x P.1 P.2]
  have hord0 : ∀ P : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}, M • P.1 = 0 :=
    fun P => by
      have := addOrderOf_nsmul_eq_zero P.1
      rwa [P.2] at this
  refine ⟨fun P => ⟨Ψ₁ P, hΨ₁x P⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro σ P P' hPP'
    apply AlgHom.ext
    intro f
    change Ψ₁ P' f = σ (Ψ₁ P f)
    apply hιKinj
    let σM : Ωb ≃+* Ωb := IsAlgClosure.equivOfEquiv Ωb Ωb (σ : Ω ≃+* Ω)
    have hσM : ∀ y : Ω, σM (algebraMap Ω Ωb y) = algebraMap Ω Ωb (σ y) := fun y =>
      IsAlgClosure.equivOfEquiv_algebraMap Ωb Ωb (σ : Ω ≃+* Ω) y
    let σb : Ωb ≃ₐ[k] Ωb := AlgEquiv.ofRingEquiv (f := σM) fun c => by
      rw [IsScalarTower.algebraMap_apply k Ω Ωb, hσM, AlgEquiv.commutes]
    have hσb : ∀ y : Ω, σb (ιK y) = ιK (σ y) := hσM
    have hιτ : ιp P'.1 = mV σb (ιp P.1) := by
      change Point.map ι P'.1 = Point.map _ (Point.map ι P.1)
      have hc : ι.comp (σ : Ω →ₐ[k] Ω) = (σb : Ωb →ₐ[k] Ωb).comp ι := by
        ext z
        exact (hσb z).symm
      rw [hPP', Point.map_map, Point.map_map, hc]
    rw [hΨ₁, ← hσb, hΨ₁, hΨ'nat σb P.1 P'.1 P.2 P'.2 hιτ f]
  ·
    intro ρ hρ γ P P' hPP'
    obtain ⟨σγ, hσγP, hσγψ⟩ := hdia0 ρ hρ γ
    have hσγψ' : ∀ f : Fb, ψ₀ (ρ γ f) = σγ (ψ₀ f) := fun f =>
      congrArg (fun φ : Fb →ₐ[K] Ω₀ => φ f) hσγψ
    apply AlgHom.ext
    intro f
    change Ψ₁ P' f = Ψ₁ P (ρ γ f)
    apply hιKinj
    rw [hΨ₁, hΨ₁, hΨ'app, hΨ'app]
    have havP' : av P'.1 = ((((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M).val) • av P.1 := by
      rw [hPP']
      exact hav_nsmul P.1 _ (hord0 P)
    rw [havP']
    exact congrArg (fun z : Ω₀ => (z : Ωb))
      (sprd_dia (K := K) P₀ ψ₀ hP₀ hstab htrans (g := fun f => ρ γ f) hσγP hσγψ'
        (hav_ord P.1 P.2) f)
  ·
    intro P P' hPP'
    apply Subtype.ext
    apply AlgHom.ext
    intro f
    change Ψ₁ P' f = Ψ₁ P f
    apply hιKinj
    rw [hΨ₁, hΨ₁, hΨ'app, hΨ'app]
    have hneg : av P'.1 = -(av P.1) := by
      rw [hPP']
      exact hav_neg P.1 (hord0 P)
    rw [hneg, hΦneg (hav_ord P.1 P.2)]
  ·
    intro P P' hPP'
    have h1 : ∀ f, Φ (av P'.1) f = Φ (av P.1) f := by
      intro f
      have h2 : Ψ₁ P' f = Ψ₁ P f := by
        have := congrArg (fun ψ : {ψ : Fb →ₐ[K] Ω // ψ x = algebraMap k Ω E.j} =>
          (ψ.1 : Fb →ₐ[K] Ω) f) hPP'
        exact this
      have h3 := congrArg ιK h2
      rw [hΨ₁, hΨ₁, hΨ'app, hΨ'app] at h3
      exact Subtype.ext h3
    have h4 := sprd_eq_imp (K := K) P₀ ψ₀ hP₀ hconv htrans (hav_ord P.1 P.2) (hav_ord P'.1 P'.2)
      h1
    rcases h4 with h4 | h4
    · left
      apply hιp
      apply e.injective
      rw [← hav_spec P'.1 (hord0 P'), ← hav_spec P.1 (hord0 P), h4]
    · right
      apply hιp
      apply e.injective
      rw [← hav_spec P'.1 (hord0 P'), map_neg, map_neg, ← hav_spec P.1 (hord0 P), h4, map_neg]

end Main

end P2MKcG1Dia

universe u v in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2) :
    ∃ Ψ : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M} →
        {ψ : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω // ψ x = algebraMap k Ω E.j},
      (∀ (σ : Ω ≃ₐ[k] Ω) (P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}),
        P'.1 = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P.1 →
          ((Ψ P').1 : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω) =
            ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Ψ P).1) ∧
      (∀ (ρ : CongruenceSubgroup.Gamma0 M →*
          (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
            qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))),
        IsDiamondPullbackModL K M ⊥ ρ →
        ∀ (γ : CongruenceSubgroup.Gamma0 M)
          (P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M}),
          P'.1 = ((((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M).val) • P.1 →
            ((Ψ P').1 : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω) =
              ((Ψ P).1 : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] Ω).comp
                (ρ γ : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K]
                  qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))) ∧
      (∀ P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M},
        P'.1 = -P.1 → Ψ P' = Ψ P) ∧
      (∀ P P' : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M},
        Ψ P' = Ψ P → P'.1 = P.1 ∨ P'.1 = -P.1) :=
  P2MKcG1Dia.main K M hM x hx k Ω E hE hfull

end S_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j
end P2MW
export P2MW.S_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j (solution)
