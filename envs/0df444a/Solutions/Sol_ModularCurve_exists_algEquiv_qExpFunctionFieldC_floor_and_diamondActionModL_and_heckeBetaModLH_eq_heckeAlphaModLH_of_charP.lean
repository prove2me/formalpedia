-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_qExpFunctionFieldC_floor_and_diamondActionModL_and_heckeBetaModLH_eq_heckeAlphaModLH_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/57ed2663-1367-5432-8c03-4bd3673317af

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_forall_apply_mem_gaussValuationSubring_iff_of_apply_j_eq_of_liesOverPrime_xHTop
import Theorems.Thm_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop
import Theorems.Thm_ModularCurve_exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC_of_liesOverPrime
import Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_of_isAlgClosed
import Theorems.Thm_ModularCurve_heckeBetaModLHDefined
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ModularCurve_IsDiamondPullbackModL_apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_qExpFunctionFieldC_floor_and_diamondActionModL_and_heckeBetaModLH_eq_heckeAlphaModLH_of_charP
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP"
p2m_attr_erase "simp" "ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve
open scoped MatrixGroups

namespace RedW

theorem gammaLift_entry (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) :
    ((((CuspForm.gammaLift N d : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = (d : ZMod N) := by
  have h := CuspForm.gamma0Units_gammaLift (M := N) d
  have h2 := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) h
  first
    | simpa [CohCarrier.val_gamma0Units] using h2
    | simpa [CohCarrier.val_gamma0Units, Gamma0Map] using h2
    | (simp [CohCarrier.val_gamma0Units] at h2; exact h2)

end RedW

namespace RedW

theorem isAlgebraic_residueField (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p] :
    letI : Algebra (ZMod p) (IsLocalRing.ResidueField ↥A) := ZMod.algebra _ p
    Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField ↥A) := by
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField ↥A) := ZMod.algebra _ p
  haveI : CharZero (AlgebraicClosure ℚ) := charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  haveI : IsAddTorsionFree (AlgebraicClosure ℚ) := IsAddTorsionFree.of_isCancelMulZero_charZero
  haveI : Module.IsTorsionFree ℤ (AlgebraicClosure ℚ) := inferInstance
  haveI hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  refine ⟨fun c => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  obtain ⟨P0, hP00, hP0a⟩ := hQalg.isAlgebraic (a : AlgebraicClosure ℚ)

  let P : Polynomial ℤ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) P0
  have hP0 : P ≠ 0 := fun h => hP00 ((IsFractionRing.integerNormalization_eq_zero_iff).mp h)
  have hPa : Polynomial.aeval (a : AlgebraicClosure ℚ) P = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) P0 hP0a

  set Q := P.primPart with hQ
  have hQa : Polynomial.aeval (a : AlgebraicClosure ℚ) Q = 0 := by
    have h := hPa
    rw [P.eq_C_content_mul_primPart, map_mul, Polynomial.aeval_C] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exfalso
      apply hP0
      rw [← Polynomial.content_eq_zero_iff]
      have : ((P.content : ℤ) : AlgebraicClosure ℚ) = 0 := by rwa [← eq_intCast (algebraMap ℤ (AlgebraicClosure ℚ))]
      exact_mod_cast this
    · exact h1
  have hQprim : Q.IsPrimitive := P.isPrimitive_primPart

  have hQA : Polynomial.aeval a Q = 0 := by
    have h1 : A.subtype (Polynomial.aeval a Q) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, ← hQa, Polynomial.aeval_def]
      congr 1
    exact Subtype.ext (by simpa using h1)
  have hred : Polynomial.aeval (IsLocalRing.residue ↥A a) Q = 0 := by
    have h := congrArg (IsLocalRing.residue ↥A) hQA
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂] at h
    rwa [Polynomial.aeval_def, show algebraMap ℤ (IsLocalRing.ResidueField ↥A) = (IsLocalRing.residue ↥A).comp (algebraMap ℤ ↥A) from
      RingHom.ext_int _ _]

  have hQp : Q.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro h0
    apply (Fact.out : p.Prime).ne_one
    have hdvd : Polynomial.C (p : ℤ) ∣ Q := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro n
      have := congrArg (fun q => q.coeff n) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact this
    have hu := hQprim (p : ℤ) hdvd
    rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega
  refine ⟨Q.map (Int.castRingHom (ZMod p)), hQp, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    show (algebraMap (ZMod p) (IsLocalRing.ResidueField ↥A)).comp (Int.castRingHom (ZMod p)) = algebraMap ℤ (IsLocalRing.ResidueField ↥A) from
      RingHom.ext_int _ _, ← Polynomial.aeval_def]
  exact hred

end RedW

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hcop : ℓ.Coprime N) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (hβ : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (hdia : ∃ ρ : CongruenceSubgroup.Gamma0 N →*
        (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
      ModularCurve.IsDiamondPullbackModL K N H' ρ) :
    ∃ W : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) ≃ₐ[K]
        ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))),
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldC K N →
          W (ModularCurve.heckeAlphaModLH K N H' ℓ x) = ModularCurve.heckeBetaModLH K N H' ℓ x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldC K N →
          W (ModularCurve.heckeBetaModLH K N H' ℓ x) = ModularCurve.heckeAlphaModLH K N H' ℓ x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        W (ModularCurve.heckeAlphaModLH K N H' ℓ x) =
          ModularCurve.heckeBetaModLH K N H' ℓ
            (ModularCurve.diamondActionModL K N H'
              (CuspForm.gammaLift N (ZMod.unitOfCoprime ℓ hcop)⁻¹) x)) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
        W (ModularCurve.heckeBetaModLH K N H' ℓ x) = ModularCurve.heckeAlphaModLH K N H' ℓ x) := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

  have hpN : ¬ p ∣ N := fun h => hNK ((CharP.cast_eq_zero_iff K p N).mpr h)
  have hℓN : ¬ ℓ ∣ N := (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    exact hℓK (CharP.cast_eq_zero K p)

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  haveI hcharκ : CharP (IsLocalRing.ResidueField ↥A) p :=
    ValuationSubring.residueField_charP_of_liesOverPrime A Fact.out hA
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  have hNκ : ((N : ℕ) : IsLocalRing.ResidueField ↥A) ≠ 0 := fun h =>
    hpN ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥A) p N).mp h)

  have hβκ := ModularCurve.heckeBetaModLHDefined (IsLocalRing.ResidueField ↥A) N H' ℓ
  obtain ⟨ρκ, hρκ⟩ := ModularCurve.exists_isDiamondPullbackModL_of_isAlgClosed (IsLocalRing.ResidueField ↥A) N hNκ H'

  have hin := ModularCurve.heckeDiamondInputsHAll N H'
  obtain ⟨hβ0, -⟩ := hin.heckeInputsHAlong ℓ Fact.out
  obtain ⟨w, hwα, hwβ⟩ := ModularCurve.exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar N H' hℓN hin

  obtain ⟨W, hW, hWA, hWm⟩ :
      ∃ W : ValuationSubring ↥(xHFunctionFieldBar N H'),
        (∀ f : ↥(xHFunctionFieldBar N H'), f ∈ W ↔ ∃ x y : PowerSeries ↥A, y.map (IsLocalRing.residue ↥A) ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
            = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ)))) ∧
        (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar N H') (a : (AlgebraicClosure ℚ)) ∈ W) ∧
        (∀ a : ↥A, a ∈ IsLocalRing.maximalIdeal ↥A → algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar N H') (a : (AlgebraicClosure ℚ)) ∈ W.nonunits) :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC_of_liesOverPrime (CohCarrier.GammaH N H') (translation_mem_GammaH N H') p A hA
  obtain ⟨W', hW', hW'A, hW'm⟩ :
      ∃ W' : ValuationSubring ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ N H' (N * ℓ))),
        (∀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ N H' (N * ℓ))), f ∈ W' ↔ ∃ x y : PowerSeries ↥A, y.map (IsLocalRing.residue ↥A) ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
            = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ)))) ∧
        (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ N H' (N * ℓ))) (a : (AlgebraicClosure ℚ)) ∈ W') ∧
        (∀ a : ↥A, a ∈ IsLocalRing.maximalIdeal ↥A →
          algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ N H' (N * ℓ))) (a : (AlgebraicClosure ℚ)) ∈ W'.nonunits) := by
    haveI : (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)).FiniteIndex := by
      unfold xHTopFunctionFieldC at *
      infer_instance
    exact ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC_of_liesOverPrime (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))
      (Subgroup.mem_inf.mpr ⟨translation_mem_GammaH N H', by
        rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.coe_T]⟩) p A hA

  let jx : ↥(xHFunctionFieldBar N H') :=
    ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ _))⟩
  have hjxQ : ((jx : ↥(xHFunctionFieldBar N H')) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    show (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)
    exact map_jqModC _
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime ℓ hcop with hu
  have hdj : diamondAutHBar N H' u jx = jx :=
    ModularCurve.diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0 N H' u jx (jqModC ℚ)
      (intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ _)) rfl
  have hwj : w (heckeAlphaHBar (AlgebraicClosure ℚ) N H' ℓ jx) = heckeBetaHBar (AlgebraicClosure ℚ) N H' ℓ jx := hwα jx
  have hwjℓ : w (heckeBetaHBar (AlgebraicClosure ℚ) N H' ℓ jx) = heckeAlphaHBar (AlgebraicClosure ℚ) N H' ℓ jx := by
    rw [hwβ jx]
    exact congrArg _ hdj

  have hstab : ∀ f, w f ∈ W' ↔ f ∈ W' :=
    ModularCurve.forall_apply_mem_gaussValuationSubring_iff_of_apply_j_eq_of_liesOverPrime_xHTop p N H' ℓ hpN hpℓ hℓN A hA _ rfl
      (heckeAlphaHBar (AlgebraicClosure ℚ) N H' ℓ jx) (heckeBetaHBar (AlgebraicClosure ℚ) N H' ℓ jx)
      (by rw [coe_heckeAlphaHBar, hjxQ]) (by rw [coe_heckeBetaHBar N H' ℓ hβ0, hjxQ])
      W' hW' w hwj hwjℓ

  obtain ⟨red, red', hpres, hpres', hsurj, hsurj', hker, hker', hαc, hβc, hdc⟩ :=
    ModularCurve.exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop p N H' ℓ hpN hpℓ hℓN hβ0 A hA hβκ ρκ hρκ W hW W' hW'

  have hstab' : ∀ f, w.symm f ∈ W' ↔ f ∈ W' := fun f => by
    have h := hstab (w.symm f)
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm
  let ws : ↥W' ≃+* ↥W' :=
    { toFun := fun g => ⟨w.symm g, (hstab' g).mpr g.2⟩
      invFun := fun g => ⟨w g, (hstab g).mpr g.2⟩
      left_inv := fun g => Subtype.ext (w.apply_symm_apply (g : _))
      right_inv := fun g => Subtype.ext (w.symm_apply_apply (g : _))
      map_mul' := fun a b => Subtype.ext (map_mul w.symm _ _)
      map_add' := fun a b => Subtype.ext (map_add w.symm _ _) }
  have ws_apply : ∀ g : ↥W', ((ws g : ↥W') : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ N H' (N * ℓ)))) = w.symm g :=
    fun g => rfl

  have hunit : ∀ (e : ↥W' ≃+* ↥W') (x : ↥W'), x ∈ IsLocalRing.maximalIdeal ↥W' → e x ∈ IsLocalRing.maximalIdeal ↥W' := by
    intro e x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu
    apply hx
    have := hu.map e.symm
    rwa [RingEquiv.symm_apply_apply] at this
  have hI : RingHom.ker red' = Ideal.map (ws : ↥W' →+* ↥W') (RingHom.ker red') := by
    apply le_antisymm
    · intro x hx
      have hx' : ws.symm x ∈ RingHom.ker red' := by
        rw [hker'] at hx ⊢
        exact hunit ws.symm x hx
      have := Ideal.mem_map_of_mem (ws : ↥W' →+* ↥W') hx'
      rwa [RingHom.coe_coe, RingEquiv.apply_symm_apply] at this
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.coe_coe]
      rw [hker'] at hx ⊢
      exact hunit ws x hx

  let e := RingHom.quotientKerEquivOfSurjective hsurj'
  let qws := Ideal.quotientEquiv (RingHom.ker red') (RingHom.ker red') ws hI
  let Wr : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) ≃+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) := e.symm.trans (qws.trans e)
  have Wr_red : ∀ g : ↥W', Wr (red' g) = red' (ws g) := by
    intro g
    show e (qws (e.symm (red' g))) = red' (ws g)
    have h1 : e.symm (red' g) = Ideal.Quotient.mk (RingHom.ker red') g :=
      RingHom.quotientKerEquivOfSurjective_symm_apply hsurj' g
    rw [h1]
    show e (Ideal.quotientEquiv _ _ ws hI (Ideal.Quotient.mk (RingHom.ker red') g)) = _
    rw [Ideal.quotientEquiv_mk]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hsurj' (ws g)

  have red'_const : ∀ a : ↥A,
      red' ⟨algebraMap (AlgebraicClosure ℚ) _ (a : (AlgebraicClosure ℚ)), hW'A a⟩ =
        algebraMap (IsLocalRing.ResidueField ↥A) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) (IsLocalRing.residue ↥A a) := by
    intro a
    have h := hpres' ⟨algebraMap (AlgebraicClosure ℚ) _ (a : (AlgebraicClosure ℚ)), hW'A a⟩ (PowerSeries.C a) 1
      (by rw [map_one]; exact one_ne_zero)
      (by
        rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]
        show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : (AlgebraicClosure ℚ)) = HahnSeries.C (a : (AlgebraicClosure ℚ))
        rw [algebraMap_laurentSeries_eq_single]
        rfl)
    rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C] at h
    apply Subtype.ext
    rw [h]
    show HahnSeries.C ((IsLocalRing.residue ↥A) a) = algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A)) ((IsLocalRing.residue ↥A) a)
    rw [algebraMap_laurentSeries_eq_single]
    rfl

  have Wr_alg : ∀ c : IsLocalRing.ResidueField ↥A,
      Wr (algebraMap (IsLocalRing.ResidueField ↥A) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) c) = algebraMap (IsLocalRing.ResidueField ↥A) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← red'_const a, Wr_red]
    have : ws ⟨algebraMap (AlgebraicClosure ℚ) _ (a : (AlgebraicClosure ℚ)), hW'A a⟩ = ⟨algebraMap (AlgebraicClosure ℚ) _ (a : (AlgebraicClosure ℚ)), hW'A a⟩ :=
      Subtype.ext (w.symm.commutes (a : (AlgebraicClosure ℚ)))
    rw [this]
  let Wκ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) ≃ₐ[(IsLocalRing.ResidueField ↥A)] ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) := AlgEquiv.ofRingEquiv (f := Wr) Wr_alg
  have Wκ_red : ∀ g : ↥W', Wκ (red' g) = red' (ws g) := Wr_red

  have lawβ : ∀ x : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H')), Wκ (ModularCurve.heckeBetaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ x) = ModularCurve.heckeAlphaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ x := by
    intro x
    obtain ⟨f, rfl⟩ := hsurj x
    obtain ⟨hβf, hβ'⟩ := hβc f
    obtain ⟨hαf, hα'⟩ := hαc f
    rw [← hβ', Wκ_red, ← hα']
    congr 1
    apply Subtype.ext
    show w.symm (heckeBetaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(xHFunctionFieldBar N H'))) = heckeAlphaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(xHFunctionFieldBar N H'))
    rw [AlgEquiv.symm_apply_eq]
    exact (hwα _).symm

  have hmulone := ModularCurve.diamondAutHBar_mul_and_diamondAutHBar_one N H'
  have lawdia : ∀ x : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H')), Wκ (ModularCurve.heckeAlphaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ x) =
      ModularCurve.heckeBetaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ (ρκ (CuspForm.gammaLift N (ZMod.unitOfCoprime ℓ hcop)⁻¹) x) := by
    intro x
    obtain ⟨f, hdf, hfx, hdred⟩ := hdc (CuspForm.gammaLift N u⁻¹) u⁻¹ (RedW.gammaLift_entry N u⁻¹) x
    obtain ⟨hαf, hα'⟩ := hαc f
    obtain ⟨hβg, hβ'⟩ := hβc ⟨_, hdf⟩
    have hcancel : diamondAutHBar N H' u (diamondAutHBar N H' u⁻¹ (f : ↥(xHFunctionFieldBar N H'))) = f := by
      rw [← AlgEquiv.mul_apply, ← hmulone.1, mul_inv_cancel, hmulone.2, AlgEquiv.one_apply]
    have hsymm : w.symm (heckeAlphaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(xHFunctionFieldBar N H'))) =
        heckeBetaHBar (AlgebraicClosure ℚ) N H' ℓ (diamondAutHBar N H' u⁻¹ (f : ↥(xHFunctionFieldBar N H'))) := by
      rw [AlgEquiv.symm_apply_eq, hwβ, hcancel]
    have step1 : Wκ (ModularCurve.heckeAlphaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ x) = red' (ws ⟨_, hαf⟩) := by
      rw [← Wκ_red, hα', hfx]
    have step2 : ws ⟨_, hαf⟩ = ⟨_, hβg⟩ := Subtype.ext hsymm
    rw [step1, step2, hβ', hdred]

  have hΓ0 := ModularCurve.qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd (IsLocalRing.ResidueField ↥A) N p hpN
  have lawfα : ∀ x : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H')), (x : LaurentSeries (IsLocalRing.ResidueField ↥A)) ∈ ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N →
      Wκ (ModularCurve.heckeAlphaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ x) = ModularCurve.heckeBetaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ x := by
    intro x hx
    rw [lawdia]
    congr 1
    exact ModularCurve.IsDiamondPullbackModL.apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0 (IsLocalRing.ResidueField ↥A) N H' hρκ _ x
      (by rw [hΓ0]; exact hx)
  have lawfβ : ∀ x : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H')), (x : LaurentSeries (IsLocalRing.ResidueField ↥A)) ∈ ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N →
      Wκ (ModularCurve.heckeBetaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ x) = ModularCurve.heckeAlphaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ x :=
    fun x _ => lawβ x

  letI : Algebra (ZMod p) (IsLocalRing.ResidueField ↥A) := ZMod.algebra _ p
  letI : Algebra (ZMod p) K := ZMod.algebra _ p
  haveI : Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField ↥A) := RedW.isAlgebraic_residueField p A
  let ι : (IsLocalRing.ResidueField ↥A) →ₐ[ZMod p] K := IsAlgClosed.lift
  letI : Algebra (IsLocalRing.ResidueField ↥A) K := ι.toRingHom.toAlgebra
  obtain ⟨WK, hWK⟩ := ModularCurve.exists_algEquiv_laws_of_algEquiv_laws_of_algebra_of_charP K p N H' ℓ hcop hNK hℓK (IsLocalRing.ResidueField ↥A) hβκ hβ ρκ hρκ
    (ModularCurve.diamondActionModL K N H') (ModularCurve.isDiamondPullbackModL_diamondActionModL hdia) Wκ
    ⟨lawfα, lawfβ, lawdia, lawβ⟩
  exact ⟨WK, hWK⟩

end S_ModularCurve_exists_algEquiv_qExpFunctionFieldC_floor_and_diamondActionModL_and_heckeBetaModLH_eq_heckeAlphaModLH_of_charP
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_qExpFunctionFieldC_floor_and_diamondActionModL_and_heckeBetaModLH_eq_heckeAlphaModLH_of_charP (solution)
