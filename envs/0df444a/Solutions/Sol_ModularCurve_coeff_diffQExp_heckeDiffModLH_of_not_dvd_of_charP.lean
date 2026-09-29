-- Prove2me | solution 1 for ModularCurve.coeff_diffQExp_heckeDiffModLH_of_not_dvd_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b7270810-01e0-5798-b984-90e989c9483d

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_coeff_trace_along_heckeBetaModLH_of_not_dvd
import Theorems.Thm_ModularCurve_exists_algEquiv_qExpFunctionFieldC_heckeBetaModLH_eq_heckeAlphaModLH_and_eq_diamondActionModL_of_charP
import Theorems.Thm_ModularCurve_finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_diffQExp_heckeDiffModLH_of_not_dvd_of_charP
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve HahnSeries KaehlerDifferential AlgebraicCurve AlgebraicCurve.Differential

namespace QCDndvd

section Twist

variable {R : Type*} [Field R]

def twistFun (c : Rˣ) (x : LaurentSeries R) : LaurentSeries R where
  coeff n := ((c ^ n : Rˣ) : R) * x.coeff n
  isPWO_support' := x.isPWO_support.mono fun n hn => by
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro h
    exact hn (by rw [h, mul_zero])

@[scoped simp] theorem twistFun_coeff (c : Rˣ) (x : LaurentSeries R) (n : ℤ) :
    (twistFun c x).coeff n = ((c ^ n : Rˣ) : R) * x.coeff n := rfl

theorem support_twistFun (c : Rˣ) (x : LaurentSeries R) : (twistFun c x).support = x.support := by
  ext n
  simp only [HahnSeries.mem_support, twistFun_coeff, ne_eq, Units.mul_right_eq_zero]

theorem twistFun_single (c : Rˣ) (k : ℤ) (r : R) :
    twistFun c (single k r) = single k (((c ^ k : Rˣ) : R) * r) := by
  ext n
  by_cases h : n = k
  · subst h; simp
  · simp [coeff_single_of_ne h]

def twist (c : Rˣ) : LaurentSeries R →ₐ[R] LaurentSeries R where
  toFun := twistFun c
  map_one' := by
    rw [← single_zero_one, twistFun_single]; simp
  map_mul' x y := by
    ext a
    rw [twistFun_coeff,
      coeff_mul_right' (x := x) (y := y) (twistFun c y).isPWO_support
        (support_twistFun c y).symm.subset,
      coeff_mul_left' (x := twistFun c x) (y := twistFun c y) x.isPWO_support
        (support_twistFun c x).subset,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    rw [twistFun_coeff, twistFun_coeff, ← hij.2.2, zpow_add, Units.val_mul]
    ring
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [mul_add]
  commutes' r := by
    rw [algebraMap_laurentSeries_eq_single]
    show twistFun c (single 0 r) = single 0 r
    rw [twistFun_single]; simp

@[scoped simp] theorem twist_coeff (c : Rˣ) (x : LaurentSeries R) (n : ℤ) :
    (twist c x).coeff n = ((c ^ n : Rˣ) : R) * x.coeff n := rfl

theorem twist_qExpand_of_pow_eq_one (c : Rˣ) (m : ℕ) [NeZero m] (hc : c ^ m = 1)
    (z : LaurentSeries R) : twist c (qExpand R m z) = qExpand R m z := by
  ext n
  rw [twist_coeff]
  by_cases h : (m : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [zpow_mul, zpow_natCast, hc, one_zpow, Units.val_one, one_mul]
  · rw [qExpand_coeff_of_not_dvd m _ h, mul_zero]

end Twist

section Euler

variable {R : Type*} [CommRing R]

theorem qEuler_qExpand (m : ℕ) [NeZero m] (x : LaurentSeries R) :
    qEuler R (qExpand R m x) = C (m : R) * qExpand R m (qEuler R x) := by
  ext n
  rw [qEuler_coeff, C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  by_cases h : (m : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [qExpand_coeff_mul, qExpand_coeff_mul, qEuler_coeff]
    push_cast
    ring
  · rw [qExpand_coeff_of_not_dvd m _ h, qExpand_coeff_of_not_dvd m _ h, mul_zero, mul_zero]

end Euler

section Pull

variable {L : Type*} [Field L]

theorem diffQExp_pullbackAlong (F₁ F₂ : IntermediateField L (LaurentSeries L))
    (φ : F₁ →ₐ[L] F₂) (ρ : LaurentSeries L →+* LaurentSeries L) (c : L)
    (hφ : ∀ x : F₁, ((φ x : F₂) : LaurentSeries L) = ρ x)
    (hρ : ∀ y, qEuler L (ρ y) = C c * ρ (qEuler L y)) (η : Ω[F₁⁄L]) :
    diffQExp F₂ (pullbackAlong φ η) = C c * ρ (diffQExp F₁ η) := by
  have key : ∀ η : Ω[F₁⁄L], η ∈ Submodule.span F₁ (Set.range (D L F₁)) → ∀ f : F₁,
      diffQExp F₂ (pullbackAlong φ (f • η)) = C c * ρ (diffQExp F₁ (f • η)) := by
    intro η hη
    induction hη using Submodule.span_induction with
    | mem η h =>
      obtain ⟨g, rfl⟩ := h
      intro f
      rw [pullbackAlong_smul, pullbackAlong_D, diffQExp_smul_D, diffQExp_smul_D, hφ, hφ, hρ,
        map_mul, mul_left_comm]
    | zero => intro f; simp
    | add x y _ _ hx hy =>
      intro f
      rw [smul_add, map_add, map_add, hx, hy, map_add, map_add, mul_add]
    | smul a x _ hx => intro f; rw [smul_smul]; exact hx (f * a)
  simpa using key η (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1

theorem pullbackAlong_pullbackAlong (F₁ F₂ F₃ : Type*) [Field F₁] [Field F₂] [Field F₃]
    [Algebra L F₁] [Algebra L F₂] [Algebra L F₃] (φ : F₁ →ₐ[L] F₂) (ψ : F₂ →ₐ[L] F₃)
    (η : Ω[F₁⁄L]) :
    pullbackAlong ψ (pullbackAlong φ η) = pullbackAlong (ψ.comp φ) η := by
  have key : ∀ η : Ω[F₁⁄L], η ∈ Submodule.span F₁ (Set.range (D L F₁)) → ∀ f : F₁,
      pullbackAlong ψ (pullbackAlong φ (f • η)) = pullbackAlong (ψ.comp φ) (f • η) := by
    intro η hη
    induction hη using Submodule.span_induction with
    | mem η h =>
      obtain ⟨g, rfl⟩ := h
      intro f
      rw [pullbackAlong_smul, pullbackAlong_D, pullbackAlong_smul, pullbackAlong_D,
        pullbackAlong_smul, pullbackAlong_D, AlgHom.comp_apply, AlgHom.comp_apply]
    | zero => intro f; simp
    | add x y _ _ hx hy =>
      intro f
      rw [smul_add, map_add, map_add, hx, hy, map_add]
    | smul a x _ hx => intro f; rw [smul_smul]; exact hx (f * a)
  simpa using key η (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1

theorem pullbackAlong_id (F₁ : Type*) [Field F₁] [Algebra L F₁] (η : Ω[F₁⁄L]) :
    pullbackAlong (AlgHom.id L F₁) η = η := by
  have key : ∀ η : Ω[F₁⁄L], η ∈ Submodule.span F₁ (Set.range (D L F₁)) → ∀ f : F₁,
      pullbackAlong (AlgHom.id L F₁) (f • η) = f • η := by
    intro η hη
    induction hη using Submodule.span_induction with
    | mem η h =>
      obtain ⟨g, rfl⟩ := h
      intro f
      rw [pullbackAlong_smul, pullbackAlong_D, AlgHom.id_apply, AlgHom.id_apply]
    | zero => intro f; simp
    | add x y _ _ hx hy =>
      intro f
      rw [smul_add, map_add, hx, hy]
    | smul a x _ hx => intro f; rw [smul_smul]; exact hx (f * a)
  simpa using key η (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1

theorem diffQExp_smul (F : IntermediateField L (LaurentSeries L)) (u : F) (ξ : Ω[F⁄L]) :
    diffQExp F (u • ξ) = (u : LaurentSeries L) * diffQExp F ξ := by
  rw [map_smul]; rfl

end Pull

section RootSum

variable {R : Type*} [Field R]

theorem twist_C (c : Rˣ) (r : R) : twist c (C r) = C r := by
  show twistFun c (single 0 r) = single 0 r
  rw [twistFun_single]; simp

def rootSum (u : Rˣ) (ℓ : ℕ) (x : LaurentSeries R) : LaurentSeries R :=
  ∑ j ∈ Finset.range ℓ, twist (u ^ j) x

theorem rootSum_apply (u : Rˣ) (ℓ : ℕ) (x : LaurentSeries R) :
    rootSum u ℓ x = ∑ j ∈ Finset.range ℓ, twist (u ^ j) x := rfl

theorem rootSum_add (u : Rˣ) (ℓ : ℕ) (x y : LaurentSeries R) :
    rootSum u ℓ (x + y) = rootSum u ℓ x + rootSum u ℓ y := by
  simp only [rootSum, map_add, Finset.sum_add_distrib]

theorem rootSum_zero (u : Rˣ) (ℓ : ℕ) : rootSum u ℓ (0 : LaurentSeries R) = 0 := by
  simp only [rootSum, map_zero, Finset.sum_const_zero]

theorem rootSum_C_mul (u : Rˣ) (ℓ : ℕ) (r : R) (x : LaurentSeries R) :
    rootSum u ℓ (C r * x) = C r * rootSum u ℓ x := by
  simp only [rootSum, map_mul, twist_C, Finset.mul_sum]

theorem rootSum_mul_of_fixed (u : Rˣ) (ℓ : ℕ) (x y : LaurentSeries R)
    (hy : ∀ j : ℕ, twist (u ^ j) y = y) : rootSum u ℓ (x * y) = rootSum u ℓ x * y := by
  rw [rootSum_apply, rootSum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hy]

theorem sum_zpow_pow {ζ : R} {ℓ : ℕ} (hζ : IsPrimitiveRoot ζ ℓ) (n : ℤ) :
    ∑ j ∈ Finset.range ℓ, (ζ ^ n) ^ j = if (ℓ : ℤ) ∣ n then (ℓ : R) else 0 := by
  split_ifs with h
  · rw [(hζ.zpow_eq_one_iff_dvd n).mpr h]
    simp
  · have hne : ζ ^ n ≠ 1 := fun h' => h ((hζ.zpow_eq_one_iff_dvd n).mp h')
    rw [geom_sum_eq hne]
    have : (ζ ^ n) ^ ℓ = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [this, sub_self, zero_div]

theorem rootSum_coeff {ζ : R} {ℓ : ℕ} (hζ : IsPrimitiveRoot ζ ℓ) (hz : ζ ≠ 0)
    (x : LaurentSeries R) (n : ℤ) :
    (rootSum (Units.mk0 ζ hz) ℓ x).coeff n = if (ℓ : ℤ) ∣ n then (ℓ : R) * x.coeff n else 0 := by
  rw [rootSum_apply, HahnSeries.coeff_sum]
  simp only [twist_coeff]
  rw [← Finset.sum_mul]
  have h : ∀ j ∈ Finset.range ℓ, (((Units.mk0 ζ hz ^ j) ^ n : Rˣ) : R) = (ζ ^ n) ^ j := by
    intro j _
    rw [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← zpow_natCast,
      ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [Finset.sum_congr rfl h, sum_zpow_pow hζ n]
  split_ifs <;> simp

end RootSum

section Trace

variable (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
  (ℓ : ℕ) [Fact ℓ.Prime]

abbrev FXt : Type _ := ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))

abbrev FUf : IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))

abbrev FUt : Type _ := ↥(FUf K N H' ℓ)

abbrev bβ : FXt K N H' →ₐ[K] FUt K N H' ℓ := heckeBetaModLH K N H' ℓ

abbrev bα : FXt K N H' →ₐ[K] FUt K N H' ℓ := heckeAlphaModLH K N H' ℓ

abbrev Dmap (hcop : ℓ.Coprime N) : FXt K N H' ≃ₐ[K] FXt K N H' :=
  diamondActionModL K N H' (CuspForm.gammaLift N (ZMod.unitOfCoprime ℓ hcop)⁻¹)

@[reducible] def algAlongBeta : Algebra (FXt K N H') (FUt K N H' ℓ) :=
  algebraAlong (bβ K N H' ℓ)

attribute [local instance] algAlongBeta

theorem isScalarTower_beta : IsScalarTower K (FXt K N H') (FUt K N H' ℓ) :=
  isScalarTower_along (bβ K N H' ℓ)

attribute [local instance] isScalarTower_beta

theorem finiteDimensional_beta (hℓK : ((ℓ : ℕ) : K) ≠ 0) :
    FiniteDimensional (FXt K N H') (FUt K N H' ℓ) :=
  (ModularCurve.finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH K N H' ℓ hℓK).2.1

theorem separableAlong_beta (hℓK : ((ℓ : ℕ) : K) ≠ 0) : SeparableAlong K (bβ K N H' ℓ) :=
  (ModularCurve.finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH K N H' ℓ hℓK).2.2.2

structure ALData (hcop : ℓ.Coprime N) (W : FUt K N H' ℓ ≃ₐ[K] FUt K N H' ℓ) : Prop where
  wβ : ∀ x : FXt K N H', W (bβ K N H' ℓ x) = bα K N H' ℓ x
  wα : ∀ x : FXt K N H', W (bα K N H' ℓ x) = bβ K N H' ℓ (Dmap K N H' ℓ hcop x)

variable {K ℓ} in

def zu {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) : Kˣ := Units.mk0 ζ (hζ.ne_zero (NeZero.ne ℓ))

variable {K ℓ} in
theorem zu_pow {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) : (zu hζ ^ j) ^ ℓ = 1 := by
  ext
  rw [← pow_mul, mul_comm, pow_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, zu,
    Units.val_mk0, hζ.pow_eq_one, one_pow, Units.val_one]

theorem qExpand_trace (hcop : ℓ.Coprime N) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (hβ : HeckeBetaModLHDefined K N H' ℓ)
    (hdia : ∃ ρ : CongruenceSubgroup.Gamma0 N →* (FXt K N H' ≃ₐ[K] FXt K N H'),
      IsDiamondPullbackModL K N H' ρ)
    {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    (W : FUt K N H' ℓ ≃ₐ[K] FUt K N H' ℓ) (hW : ALData K N H' ℓ hcop W) (v : FUt K N H' ℓ) :
    qExpand K ℓ ((Algebra.trace (FXt K N H') (FUt K N H' ℓ) v : FXt K N H') : LaurentSeries K)
      = rootSum (zu hζ) ℓ (v : LaurentSeries K)
        + qExpand K ℓ ((W v : FUt K N H' ℓ) : LaurentSeries K) := by
  ext m
  rw [HahnSeries.coeff_add, zu, rootSum_coeff hζ]
  by_cases hm : (ℓ : ℤ) ∣ m
  · obtain ⟨n, rfl⟩ := hm
    rw [qExpand_coeff_mul, qExpand_coeff_mul, if_pos (dvd_mul_right _ _)]
    have h := ModularCurve.coeff_trace_along_heckeBetaModLH_of_not_dvd K N H' ℓ hcop hNK hℓK hβ hdia
      W hW.wβ hW.wα v n
    rw [mul_comm n (ℓ : ℤ)] at h
    exact h
  · rw [qExpand_coeff_of_not_dvd _ _ hm, qExpand_coeff_of_not_dvd _ _ hm, if_neg hm, add_zero]

end Trace

section Assembly

theorem coeff_C_mul {R : Type*} [CommRing R] (r : R) (x : LaurentSeries R) (n : ℤ) :
    (C r * x).coeff n = r * x.coeff n := by
  rw [C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

variable {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ} [NeZero N] {H' : Subgroup (ZMod N)ˣ} {ℓ : ℕ}
  [Fact ℓ.Prime] {hcop : ℓ.Coprime N}

attribute [local instance] algAlongBeta isScalarTower_beta

local notation "FN" => qExpFunctionFieldC K (CohCarrier.GammaH N H')
local notation "FNl" => FUf K N H' ℓ
local notation "β" => heckeBetaModLH K N H' ℓ
local notation "α" => heckeAlphaModLH K N H' ℓ
local notation "Dℓ" => Dmap K N H' ℓ hcop

theorem diffQExp_pullback_beta (hβ : HeckeBetaModLHDefined K N H' ℓ) (η : Ω[↥FN⁄K]) :
    diffQExp FNl (pullbackAlong β η) = C (ℓ : K) * qExpand K ℓ (diffQExp FN η) :=
  diffQExp_pullbackAlong FN FNl β (qExpand K ℓ) ℓ (fun x => coe_heckeBetaModLH K N H' ℓ hβ x)
    (fun y => qEuler_qExpand ℓ y) η

theorem diffQExp_pullback_w_beta {W : FUt K N H' ℓ ≃ₐ[K] FUt K N H' ℓ} (hW : ALData K N H' ℓ hcop W) (η : Ω[↥FN⁄K]) :
    diffQExp FNl (pullbackAlong (W.toAlgHom.comp β) η) = diffQExp FN η := by
  rw [diffQExp_pullbackAlong FN FNl (W.toAlgHom.comp β) (RingHom.id _) 1 ?_ ?_ η, C_one, one_mul,
    RingHom.id_apply]
  · intro x
    rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, hW.wβ, coe_heckeAlphaModLH, RingHom.id_apply]
  · intro y
    rw [C_one, one_mul]
    rfl

theorem diffQExp_pullback_w_alpha (hβ : HeckeBetaModLHDefined K N H' ℓ) {W : FUt K N H' ℓ ≃ₐ[K] FUt K N H' ℓ}
    (hW : ALData K N H' ℓ hcop W) (η : Ω[↥FN⁄K]) :
    diffQExp FNl (pullbackAlong (W.toAlgHom.comp α) η) =
      C (ℓ : K) * qExpand K ℓ (diffQExp FN (pullbackAlong ((Dℓ : ↥FN ≃ₐ[K] ↥FN) : ↥FN →ₐ[K] ↥FN) η)) := by
  have hcomp : W.toAlgHom.comp α = (β).comp ((Dℓ : ↥FN ≃ₐ[K] ↥FN) : ↥FN →ₐ[K] ↥FN) := by
    apply AlgHom.ext
    intro x
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, hW.wα]
    rfl
  rw [hcomp, ← pullbackAlong_pullbackAlong, diffQExp_pullback_beta hβ]

theorem twist_fix {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) (z : LaurentSeries K) :
    twist (zu hζ ^ j) (C (ℓ : K) * qExpand K ℓ z) = C (ℓ : K) * qExpand K ℓ z := by
  rw [map_mul, twist_C, twist_qExpand_of_pow_eq_one _ ℓ (zu_pow hζ j)]

def MC {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (W : FUt K N H' ℓ ≃ₐ[K] FUt K N H' ℓ) (ξ : Ω[↥FNl⁄K]) : Prop :=
  ∀ v : ↥FNl, C (ℓ : K) * qExpand K ℓ (diffQExp FN (traceAlong β (v • ξ)))
    = rootSum (zu hζ) ℓ ((v : LaurentSeries K) * diffQExp FNl ξ)
      + C (ℓ : K) * qExpand K ℓ (diffQExp FNl (pullbackAlong W.toAlgHom (v • ξ)))

theorem MC_base (hβ : HeckeBetaModLHDefined K N H' ℓ) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (hdia : ∃ ρ : CongruenceSubgroup.Gamma0 N →* (↥FN ≃ₐ[K] ↥FN), IsDiamondPullbackModL K N H' ρ) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    {W : FUt K N H' ℓ ≃ₐ[K] FUt K N H' ℓ} (hW : ALData K N H' ℓ hcop W) (η : Ω[↥FN⁄K]) : MC hζ W (pullbackAlong β η) := by
  intro v
  rw [traceAlong_smul_pullbackAlong β (separableAlong_beta K N H' ℓ hℓK) v η, diffQExp_smul, map_mul,
    qExpand_trace K N H' ℓ hcop hNK hℓK hβ hdia hζ W hW v, diffQExp_pullback_beta hβ,
    rootSum_mul_of_fixed _ _ _ _ (fun j => twist_fix hζ j _), pullbackAlong_smul,
    pullbackAlong_pullbackAlong, diffQExp_smul, diffQExp_pullback_w_beta hW, map_mul,
    AlgEquiv.coe_algHom]
  ring

theorem MC_smul {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) {W : FUt K N H' ℓ ≃ₐ[K] FUt K N H' ℓ}
    (ξ : Ω[↥FNl⁄K]) (h : MC hζ W ξ) (u' : ↥FNl) : MC hζ W (u' • ξ) := by
  intro v
  have e1 : v • (u' • ξ) = (v * u') • ξ := smul_smul v u' ξ
  have e2 : (v : LaurentSeries K) * diffQExp FNl (u' • ξ)
      = ((v * u' : ↥FNl) : LaurentSeries K) * diffQExp FNl ξ := by
    rw [diffQExp_smul, ← mul_assoc]; rfl
  rw [e1, e2]
  exact h (v * u')

theorem MC_add {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) {W : FUt K N H' ℓ ≃ₐ[K] FUt K N H' ℓ}
    (ξ₁ ξ₂ : Ω[↥FNl⁄K]) (h₁ : MC hζ W ξ₁) (h₂ : MC hζ W ξ₂) : MC hζ W (ξ₁ + ξ₂) := by
  intro v
  simp only [smul_add, map_add, mul_add, rootSum_add]
  rw [h₁ v, h₂ v]
  ring

theorem MC_zero {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) {W : FUt K N H' ℓ ≃ₐ[K] FUt K N H' ℓ} : MC hζ W 0 := by
  intro v
  simp only [smul_zero, map_zero, mul_zero, rootSum_zero, add_zero]

theorem MC_all (hβ : HeckeBetaModLHDefined K N H' ℓ) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (hdia : ∃ ρ : CongruenceSubgroup.Gamma0 N →* (↥FN ≃ₐ[K] ↥FN), IsDiamondPullbackModL K N H' ρ) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    {W : FUt K N H' ℓ ≃ₐ[K] FUt K N H' ℓ} (hW : ALData K N H' ℓ hcop W) (ξ : Ω[↥FNl⁄K]) : MC hζ W ξ := by
  haveI := finiteDimensional_beta K N H' ℓ hℓK
  haveI : Algebra.IsSeparable (FXt K N H') (FUt K N H' ℓ) := separableAlong_beta K N H' ℓ hℓK
  haveI : Algebra.FormallyEtale (FXt K N H') (FUt K N H' ℓ) := Algebra.FormallyEtale.of_isSeparable _ _
  obtain ⟨t, rfl⟩ :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (FXt K N H') (FUt K N H' ℓ)).surjective ξ
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact MC_zero hζ
  | tmul u' η =>
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
    change MC hζ W (u' • pullbackAlong β η)
    exact MC_smul hζ _ (MC_base hβ hNK hℓK hdia hζ hW η) u'
  | add x y hx hy => rw [map_add]; exact MC_add hζ _ _ hx hy

theorem key_identity (hβ : HeckeBetaModLHDefined K N H' ℓ) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (hdia : ∃ ρ : CongruenceSubgroup.Gamma0 N →* (↥FN ≃ₐ[K] ↥FN), IsDiamondPullbackModL K N H' ρ) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    {W : FUt K N H' ℓ ≃ₐ[K] FUt K N H' ℓ} (hW : ALData K N H' ℓ hcop W) (ω : Ω[↥FN⁄K]) :
    C (ℓ : K) * qExpand K ℓ (diffQExp FN (Differential.correspondence β α ω))
      = rootSum (zu hζ) ℓ (diffQExp FN ω)
        + C (ℓ : K) * (C (ℓ : K) * qExpand K ℓ (qExpand K ℓ
            (diffQExp FN (pullbackAlong ((Dℓ : ↥FN ≃ₐ[K] ↥FN) : ↥FN →ₐ[K] ↥FN) ω)))) := by
  have key : ∀ ω : Ω[↥FN⁄K], ω ∈ Submodule.span (↥FN) (Set.range (D K ↥FN)) → ∀ f : ↥FN,
      C (ℓ : K) * qExpand K ℓ (diffQExp FN (Differential.correspondence β α (f • ω)))
        = rootSum (zu hζ) ℓ (diffQExp FN (f • ω))
          + C (ℓ : K) * (C (ℓ : K) * qExpand K ℓ (qExpand K ℓ
              (diffQExp FN (pullbackAlong ((Dℓ : ↥FN ≃ₐ[K] ↥FN) : ↥FN →ₐ[K] ↥FN) (f • ω))))) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem ω h =>
      obtain ⟨g, rfl⟩ := h
      intro f
      have hM := MC_all hβ hNK hℓK hdia hζ hW (D K ↥FNl (α g)) (α f)

      have hW2 : diffQExp FNl (pullbackAlong W.toAlgHom ((α f) • D K ↥FNl (α g))) =
          C (ℓ : K) * qExpand K ℓ
            (diffQExp FN (pullbackAlong ((Dℓ : ↥FN ≃ₐ[K] ↥FN) : ↥FN →ₐ[K] ↥FN) (f • D K ↥FN g))) := by
        have e1 : (α f) • D K ↥FNl (α g) = pullbackAlong α (f • D K ↥FN g) := by
          rw [pullbackAlong_smul, pullbackAlong_D]
        rw [e1, pullbackAlong_pullbackAlong, diffQExp_pullback_w_alpha hβ hW]
      rw [correspondence_apply, pullbackAlong_smul, pullbackAlong_D, hM, hW2, diffQExp_D,
        coe_heckeAlphaModLH, coe_heckeAlphaModLH, diffQExp_smul_D, map_mul, qExpand_C]
    | zero => intro f; simp [rootSum_zero]
    | add x y _ _ hx hy =>
      intro f
      simp only [smul_add, map_add, mul_add, rootSum_add]
      rw [hx f, hy f]
      ring
    | smul a x _ hx => intro f; rw [smul_smul]; exact hx (f * a)
  simpa using key ω (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1

theorem coeff_identity (hβ : HeckeBetaModLHDefined K N H' ℓ) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (hdia : ∃ ρ : CongruenceSubgroup.Gamma0 N →* (↥FN ≃ₐ[K] ↥FN), IsDiamondPullbackModL K N H' ρ)
    (hAL : ∃ W : FUt K N H' ℓ ≃ₐ[K] FUt K N H' ℓ, ALData K N H' ℓ hcop W) (ω : Ω[↥FN⁄K]) (n : ℤ) :
    (diffQExp FN (Differential.correspondence β α ω)).coeff n
      = (diffQExp FN ω).coeff (n * ℓ)
        + (ℓ : K) * (if (ℓ : ℤ) ∣ n then
            (diffQExp FN (pullbackAlong ((Dℓ : ↥FN ≃ₐ[K] ↥FN) : ↥FN →ₐ[K] ↥FN) ω)).coeff (n / ℓ) else 0) := by
  haveI : NeZero ((ℓ : ℕ) : K) := ⟨hℓK⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ℓ
  obtain ⟨W, hW⟩ := hAL
  have h := congrArg (fun s : LaurentSeries K => s.coeff ((ℓ : ℤ) * n)) (key_identity hβ hNK hℓK hdia hζ hW ω)
  beta_reduce at h
  rw [coeff_C_mul, qExpand_coeff_mul, HahnSeries.coeff_add, coeff_C_mul, coeff_C_mul,
    qExpand_coeff_mul, zu, rootSum_coeff hζ, if_pos (dvd_mul_right _ _), ← mul_add] at h
  have hℓ0 : ((ℓ : ℕ) : K) ≠ 0 := hℓK
  have h' := mul_left_cancel₀ hℓ0 h
  rw [h', mul_comm (ℓ : ℤ) n]
  congr 2
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    rw [qExpand_coeff_mul, Int.mul_ediv_cancel_left _ (by exact_mod_cast (NeZero.ne ℓ))]
  · exact qExpand_coeff_of_not_dvd ℓ _ hd

end Assembly

end QCDndvd
p2m_reactivate "P2MW.S_ModularCurve_coeff_diffQExp_heckeDiffModLH_of_not_dvd_of_charP.QCDndvd"

open ModularCurve

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hcop : ℓ.Coprime N)
    (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (hβ : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (hdia : ∃ ρ : CongruenceSubgroup.Gamma0 N →*
        (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
      ModularCurve.IsDiamondPullbackModL K N H' ρ)
    (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) (n : ℤ) :
    (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) (ModularCurve.heckeDiffModLH K N H' ℓ ω)).coeff n =
      (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ω).coeff (n * ℓ) +
        (ℓ : K) *
          (if (ℓ : ℤ) ∣ n then
            (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))
              (ModularCurve.diamondDiffModLH K N H' (ZMod.unitOfCoprime ℓ hcop) ω)).coeff (n / ℓ)
           else 0) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨W, hWβ, hWα⟩ :=
    ModularCurve.exists_algEquiv_qExpFunctionFieldC_heckeBetaModLH_eq_heckeAlphaModLH_and_eq_diamondActionModL_of_charP
      K p N H' ℓ hcop hNK hℓK hβ hdia
  exact QCDndvd.coeff_identity hβ hNK hℓK hdia ⟨W, ⟨hWβ, hWα⟩⟩ ω n

end
p2m_reactivate "P2MW.S_ModularCurve_coeff_diffQExp_heckeDiffModLH_of_not_dvd_of_charP.QCDndvd"

end S_ModularCurve_coeff_diffQExp_heckeDiffModLH_of_not_dvd_of_charP
end P2MW
export P2MW.S_ModularCurve_coeff_diffQExp_heckeDiffModLH_of_not_dvd_of_charP (solution)
