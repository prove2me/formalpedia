-- Prove2me | solution 1 for ModularCurve.finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_add_one_of_charP_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/3ceb065c-2025-57ef-9a57-accd60a7f345

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup
import Theorems.Thm_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_add_one_of_charP_of_dvd
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
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

open scoped MatrixGroups
open CongruenceSubgroup

namespace ModularCurve
p2m_export "ModularCurve" "heckeAlphaModLH infSubgroup neZero_div qExpFunctionFieldC qExpFunctionFieldC_mono relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup GammaH_le_GammaH_div_infSubgroup"
p2m_open "ModularCurve"

namespace DegRedL

theorem unitsMap_square {a b c d : ℕ} (hba : b ∣ a) (hcb : c ∣ b) (hda : d ∣ a) (hcd : c ∣ d) :
    (ZMod.unitsMap hcb).comp (ZMod.unitsMap hba) = (ZMod.unitsMap hcd).comp (ZMod.unitsMap hda) := by
  rw [ZMod.unitsMap_comp, ZMod.unitsMap_comp]

theorem gammaH_comap_congr {N L₁ L₂ : ℕ} (h : L₁ = L₂) (h₁ : N ∣ L₁) (h₂ : N ∣ L₂)
    (H' : Subgroup (ZMod N)ˣ) :
    CohCarrier.GammaH L₁ (H'.comap (ZMod.unitsMap h₁)) =
      CohCarrier.GammaH L₂ (H'.comap (ZMod.unitsMap h₂)) := by
  subst h
  rfl

theorem qExpFunctionFieldC_gammaH_eq_infSubgroup
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    qExpFunctionFieldC K (CohCarrier.GammaH M H) =
      qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) :=
  le_antisymm
    (ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup p M hpM hpM2 H hHp K)
    (qExpFunctionFieldC_mono K (ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM))

theorem infSubgroup_mul_comap_eq
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (ℓ : ℕ) [NeZero ℓ] (hpMℓ : p ∣ M * ℓ) (h₃ : M / p ∣ M * ℓ / p) :
    infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) hpMℓ =
      (infSubgroup p M H hpM).comap (ZMod.unitsMap h₃) := by
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  set u₁ : (ZMod (M * ℓ))ˣ →* (ZMod M)ˣ := ZMod.unitsMap (dvd_mul_right M ℓ) with hu₁
  set u₂ : (ZMod (M * ℓ))ˣ →* (ZMod (M * ℓ / p))ˣ := ZMod.unitsMap (Nat.div_dvd_of_dvd hpMℓ) with hu₂
  set u₃ : (ZMod (M * ℓ / p))ˣ →* (ZMod (M / p))ˣ := ZMod.unitsMap h₃ with hu₃
  set u₄ : (ZMod M)ˣ →* (ZMod (M / p))ˣ := ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) with hu₄
  have hsq : u₄.comp u₁ = u₃.comp u₂ := by
    rw [hu₁, hu₂, hu₃, hu₄]
    exact unitsMap_square _ _ _ _
  have hH : H = (H.map u₄).comap u₄ := by
    rw [Subgroup.comap_map_eq]
    refine le_antisymm le_sup_left (sup_le le_rfl ?_)
    intro u hu
    exact hHp u hu
  show (H.comap u₁).map u₂ = (H.map u₄).comap u₃
  conv_lhs => rw [hH]
  rw [Subgroup.comap_comap, hsq, ← Subgroup.comap_comap,
    Subgroup.map_comap_eq_self_of_surjective (ZMod.unitsMap_surjective _)]

theorem qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    haveI : NeZero (M / p) := neZero_div p M hpM
    qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) =
      qExpFunctionFieldC K
        (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ⊓ Gamma0 (M / p * ℓ)) := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hpMℓ : p ∣ M * ℓ := dvd_mul_of_dvd_left hpM ℓ
  have hpℓ : p.Coprime ℓ := (Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓp)
  have hpMℓ2 : ¬ p ^ 2 ∣ M * ℓ := fun h =>
    hpM2 ((Nat.Coprime.pow_left 2 hpℓ).dvd_of_dvd_mul_right h)
  have hlev : M / p * ℓ = M * ℓ / p := Nat.div_mul_right_comm hpM ℓ
  have h₃ : M / p ∣ M * ℓ / p := Dvd.intro ℓ hlev
  have hHtp : ∀ u : (ZMod (M * ℓ))ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpMℓ) u = 1 →
      u ∈ H.comap (ZMod.unitsMap (dvd_mul_right M ℓ)) := by
    intro u hu
    rw [Subgroup.mem_comap]
    apply hHp
    have hsq := congrArg (fun f => f u)
      (unitsMap_square (dvd_mul_right M ℓ) (Nat.div_dvd_of_dvd hpM) (Nat.div_dvd_of_dvd hpMℓ) h₃)
    simp only [MonoidHom.comp_apply] at hsq
    rw [hsq, hu, map_one]
  calc qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ))
      = qExpFunctionFieldC K
          (CohCarrier.GammaH (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ)))) := by
        rw [CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap]
    _ = qExpFunctionFieldC K (CohCarrier.GammaH (M * ℓ / p)
          (infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) hpMℓ)) :=
        qExpFunctionFieldC_gammaH_eq_infSubgroup K p (M * ℓ) hpMℓ hpMℓ2 _ hHtp
    _ = qExpFunctionFieldC K (CohCarrier.GammaH (M * ℓ / p)
          ((infSubgroup p M H hpM).comap (ZMod.unitsMap h₃))) := by
        rw [infSubgroup_mul_comap_eq p M hpM H hHp ℓ hpMℓ h₃]
    _ = qExpFunctionFieldC K (CohCarrier.GammaH (M / p * ℓ)
          ((infSubgroup p M H hpM).comap (ZMod.unitsMap (dvd_mul_right (M / p) ℓ)))) := by
        rw [gammaH_comap_congr hlev.symm h₃ (dvd_mul_right (M / p) ℓ)]
    _ = qExpFunctionFieldC K
          (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ⊓ Gamma0 (M / p * ℓ)) := by
        rw [CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap]

theorem relfinrank_qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_add_one_of_charP
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p) :
    IntermediateField.relfinrank (qExpFunctionFieldC K (CohCarrier.GammaH M H))
        (qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ))) = ℓ + 1 := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have h1 := qExpFunctionFieldC_gammaH_eq_infSubgroup K p M hpM hpM2 H hHp
  have h2 := qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup K p M hpM hpM2 H hHp ℓ hℓp
  rw [h1, h2]
  have hcop : ℓ.Coprime (M / p) :=
    (Nat.Prime.coprime_iff_not_dvd hℓ).2 (fun h => hℓM (h.trans (Nat.div_dvd_of_dvd hpM)))
  have hNK : ((M / p : ℕ) : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K p] at h
    exact hpM2 (by rw [pow_two]; exact (Nat.dvd_div_iff_mul_dvd hpM).mp h)
  have hℓK : ((ℓ : ℕ) : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K p] at h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h).symm
  exact ModularCurve.relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one K (M / p)
    (infSubgroup p M H hpM) ℓ hcop hNK hℓK

theorem finrankAlong_heckeAlphaModLH_eq_add_one_of_charP
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p) :
    AlgebraicCurve.finrankAlong K (heckeAlphaModLH K M H ℓ) = ℓ + 1 := by
  have h68 := AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange
    (qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)))
    (IntermediateField.inclusion (qExpFunctionFieldC_mono K
      (inf_le_left : CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) ≤ CohCarrier.GammaH M H)))
  have hval : (qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ))).val.comp
      (IntermediateField.inclusion (qExpFunctionFieldC_mono K
        (inf_le_left : CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) ≤ CohCarrier.GammaH M H))) =
      (qExpFunctionFieldC K (CohCarrier.GammaH M H)).val := by
    ext x
    rfl
  rw [hval, IntermediateField.fieldRange_val] at h68
  exact h68.trans
    (relfinrank_qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_add_one_of_charP K p M hpM hpM2 H hHp ℓ hℓM hℓp)

end DegRedL

end ModularCurve

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p) :
    (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      AlgebraicCurve.finrankAlong K (ModularCurve.heckeAlphaModLH K M H ℓ) = ℓ + 1) ∧
    IntermediateField.relfinrank (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) = ℓ + 1 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  exact ⟨ModularCurve.DegRedL.finrankAlong_heckeAlphaModLH_eq_add_one_of_charP K p M hpM hpM2 H hHp ℓ hℓM hℓp,
    ModularCurve.DegRedL.relfinrank_qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_add_one_of_charP
      K p M hpM hpM2 H hHp ℓ hℓM hℓp⟩

end S_ModularCurve_finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_add_one_of_charP_of_dvd
end P2MW
export P2MW.S_ModularCurve_finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_add_one_of_charP_of_dvd (solution)
