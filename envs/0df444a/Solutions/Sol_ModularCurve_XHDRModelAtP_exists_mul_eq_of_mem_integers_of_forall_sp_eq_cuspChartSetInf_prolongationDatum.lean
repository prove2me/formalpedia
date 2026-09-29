-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_mul_eq_of_mem_integers_of_forall_sp_eq_cuspChartSetInf_prolongationDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/dd15d14c-abf2-5871-8b8f-e86174794788

import Theorems.Thm_ModularCurve_XHDRModelAtP_not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_XHDRModelAtP_isCuspidal_of_not_isAffinePlace_reduceFst_prolongationDatum
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_hasValue_and_hasValue_sp_residue_of_mem_closure_chartAlgInf_of_cusp
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_mem_closure_chartAlgInf_hasValue_residue_zero_and_not_hasValue_of_not_isAffinePlace_of_ne
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integralOverPoleChart_of_mem_integers_of_forall_inv_mem_imp_mem
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_and_residue_mem_and_mem_of_mem_cuspChartSetInf
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_JHCuspChartSet
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_mul_eq_of_mem_integers_of_forall_sp_eq_cuspChartSetInf_prolongationDatum
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.TwoChart.isOpenImmersion_fInf ModularCurve.TwoChart.isOpenImmersion_ιFin ModularCurve.TwoChart.isOpenImmersion_ιInf ModularCurve.TwoChart.isOpenImmersion_fFin ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun"
p2m_attr_erase "simp" "KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.TwoChart.coe_jChartFin ModularCurve.TwoChart.ιFin_modelTo ModularCurve.TwoChart.ιInf_modelTo ModularCurve.TwoChart.ιInf_modelTo_assoc ModularCurve.TwoChart.coe_jInvChartInf ModularCurve.TwoChart.ιFin_modelTo_assoc ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace Ws47
namespace OrderH1

open AlgebraicCurve IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem isUnit_mk_iff {K : Type*} [Field K] (S : ValuationSubring K) {y : K} (hy : y ∈ S) (hy0 : y ≠ 0) :
    IsUnit (⟨y, hy⟩ : S) ↔ y⁻¹ ∈ S := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have hb' : y * (b : K) = 1 := by
      have := congrArg (fun t : S => (t : K)) hb
      simpa using this
    have : (b : K) = y⁻¹ := eq_inv_of_mul_eq_one_right hb'
    rw [← this]; exact b.2
  · intro h
    exact isUnit_iff_exists_inv.mpr ⟨⟨y⁻¹, h⟩, Subtype.ext (by simp [mul_inv_cancel₀ hy0])⟩

private theorem _root_.Ws47.OrderH1.residue_eq_zero_iff (R : RegularProlongation A F Fb) (y : R.integers) :
    R.residue y = 0 ↔ ¬ IsUnit y := by
  constructor
  · intro h hu; exact R.residue_ne_zero_of_isUnit hu h
  · intro h; by_contra h0; exact h (R.isUnit_of_residue_ne_zero h0)

p2m_export "Ws47.OrderH1" "residue_eq_zero_iff"

theorem integers_eq_of_le {Fb₂ : Type*} [Field Fb₂] [Algebra (ResidueField A) Fb₂]
    (S : RegularProlongation A F Fb) (T : RegularProlongation A F Fb₂)
    (h : S.integers ≤ T.integers) : S.integers = T.integers := by
  refine le_antisymm h ?_
  intro y hyT
  by_contra hyS
  have hy0 : y ≠ 0 := fun h0 => hyS (h0 ▸ zero_mem _)
  have hyiS : y⁻¹ ∈ S.integers := (S.integers.mem_or_inv_mem y).resolve_left hyS
  obtain ⟨c, hcy, hres⟩ := S.exists_smul_mem y hy0
  have hc0 : c ≠ 0 := S.smul_const_ne_zero hcy hres
  have hcy0 : c • y ≠ 0 := smul_ne_zero hc0 hy0
  have hunit : IsUnit (⟨c • y, hcy⟩ : S.integers) := S.isUnit_of_residue_ne_zero hres
  have hcyiS : (c • y)⁻¹ ∈ S.integers := (isUnit_mk_iff S.integers hcy hcy0).mp hunit
  have hcS : algebraMap L F c ∈ S.integers := by
    have e : algebraMap L F c = (c • y) * y⁻¹ := by
      rw [Algebra.smul_def, mul_assoc, mul_inv_cancel₀ hy0, mul_one]
    rw [e]; exact mul_mem hcy hyiS
  have hcA : c ∈ A := (S.algebraMap_mem_iff c).mp hcS
  have hciT : algebraMap L F c⁻¹ ∈ T.integers := by
    have e : algebraMap L F c⁻¹ = y * (c • y)⁻¹ := by
      rw [Algebra.smul_def, mul_inv, ← mul_assoc, mul_comm y, mul_assoc, mul_inv_cancel₀ hy0, mul_one, map_inv₀]
    rw [e]; exact mul_mem hyT (h hcyiS)
  have hciA : c⁻¹ ∈ A := (T.algebraMap_mem_iff c⁻¹).mp hciT
  have hciS : algebraMap L F c⁻¹ ∈ S.integers := (S.algebraMap_mem_iff c⁻¹).mpr hciA
  apply hyS
  have e : y = algebraMap L F c⁻¹ * (c • y) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  rw [e]; exact mul_mem hciS hcy

end Ws47.OrderH1

namespace Ws47
namespace ZeroN

theorem ord_sub_algebraMap_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {g : F} {a : K} (h : v.HasValue g a) (hne : g ≠ algebraMap K F a) :
    0 < v.ord (g - algebraMap K F a) := by
  obtain ⟨hg, hres⟩ := h
  have ha : algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem' a
  have hsub : g - algebraMap K F a ∈ v.toValuationSubring := sub_mem hg ha
  have hne0 : g - algebraMap K F a ≠ 0 := sub_ne_zero.mpr hne

  have hmax : (⟨g - algebraMap K F a, hsub⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have heq : (⟨g - algebraMap K F a, hsub⟩ : v.toValuationSubring) = ⟨g, hg⟩ - algebraMap K v.toValuationSubring a :=
      Subtype.ext rfl
    rw [heq, map_sub, hres, Place.residue_algebraMap, sub_self]

  have hlt : v.adicValuation (g - algebraMap K F a) < 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd v.heightOneSpectrum
      (⟨g - algebraMap K F a, hsub⟩ : v.toValuationSubring)).mpr
      (by rw [Ideal.dvd_span_singleton, Place.heightOneSpectrum_asIdeal]; exact hmax)
    rwa [← Place.adicValuation_coe] at this
  have hne0' : v.adicValuation (g - algebraMap K F a) ≠ 0 := v.adicValuation_ne_zero hne0
  unfold Place.ord
  have hlog : WithZero.log (v.adicValuation (g - algebraMap K F a)) < 0 := by
    rw [WithZero.log_lt_iff_lt_exp hne0', WithZero.exp_zero]
    exact hlt
  omega

theorem coeffEmb_jqModC (L : Type*) [Field L] [Algebra ℚ L] :
    coeffEmb L (jqModC ℚ) = jqModC L := by
  rw [coeffEmb, coeffMap_jqModC]
end Ws47.ZeroN

namespace Ws47
namespace D3a

open AlgebraicCurve IsLocalRing

theorem mem_of_monic {E : Type*} [Field E] (O : ValuationSubring E) {T : Type*} [CommRing T]
    (g : T →+* E) (hg : ∀ t, g t ∈ O) {x : E} {p : Polynomial T} (hp : p.Monic) (hx : Polynomial.eval₂ g x p = 0) :
    x ∈ O := by
  let g' : T →+* O := g.codRestrict O hg
  have hcomp : (algebraMap O E).comp g' = g := RingHom.ext fun t => rfl
  have hint : IsIntegral O x := by
    refine ⟨p.map g', hp.map g', ?_⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

theorem residue_mem_of_monic {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb] {k : Type*} [Field k] [Algebra k Fb]
    (R : RegularProlongation A F Fb) (v : Place k Fb) {T : Type*} [CommRing T] (g : T →+* F)
    (hgI : ∀ t, g t ∈ R.integers) (hgv : ∀ t, (R.residue ⟨g t, hgI t⟩ : Fb) ∈ v.toValuationSubring)
    {x : F} (hx : x ∈ R.integers) {p : Polynomial T} (hp : p.Monic) (hroot : Polynomial.eval₂ g x p = 0) :
    (R.residue ⟨x, hx⟩ : Fb) ∈ v.toValuationSubring := by
  let g₁ : T →+* R.integers := g.codRestrict R.integers hgI
  have h2 : (R.integers.subtype).comp g₁ = g := RingHom.ext fun t => rfl
  have h1 : Polynomial.eval₂ g₁ ⟨x, hx⟩ p = 0 := by
    apply Subtype.ext
    show R.integers.subtype (Polynomial.eval₂ g₁ ⟨x, hx⟩ p) = 0
    rw [Polynomial.hom_eval₂, h2]
    exact hroot
  have h3 : Polynomial.eval₂ (R.residue.comp g₁) (R.residue ⟨x, hx⟩) p = 0 := by
    rw [← Polynomial.hom_eval₂, h1, map_zero]
  exact mem_of_monic v.toValuationSubring (R.residue.comp g₁) hgv hp h3

theorem inv_mem_of_ord_le_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (W : Place K F) {x : F}
    (hx0 : x ≠ 0) (h : W.ord x ≤ 0) : x⁻¹ ∈ W.toValuationSubring := by
  rcases W.toValuationSubring.mem_or_inv_mem x with hx | hx
  ·
    have hle : W.adicValuation x ≤ 1 := by
      rw [show x = ((⟨x, hx⟩ : W.toValuationSubring) : F) from rfl, W.adicValuation_coe]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    have hne : W.adicValuation x ≠ 0 := W.adicValuation_ne_zero hx0
    have hge : 0 ≤ W.ord x := by
      unfold Place.ord
      have : WithZero.log (W.adicValuation x) ≤ 0 := by
        rw [WithZero.log_le_iff_le_exp hne, WithZero.exp_zero]; exact hle
      omega
    have h0 : W.ord x = 0 := le_antisymm h hge
    have hval : W.adicValuation x = 1 := by
      unfold Place.ord at h0
      have hlog : WithZero.log (W.adicValuation x) = 0 := by omega
      rw [← WithZero.exp_log hne, hlog, WithZero.exp_zero]
    have hu : IsUnit (⟨x, hx⟩ : W.toValuationSubring) := (W.adicValuation_coe_eq_one_iff ⟨x, hx⟩).mp hval
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : x * (b : F) = 1 := by
      have := congrArg (fun t : W.toValuationSubring => (t : F)) hb
      simpa using this
    rw [← eq_inv_of_mul_eq_one_right hb']
    exact b.2
  · exact hx

end Ws47.D3a

namespace Ws47
namespace D3dH

open AlgebraicCurve

theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem isUnit_iff_ord_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

theorem hasValue_iff_eq_or_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {g : F}
    (hg : g ∈ v.toValuationSubring) (c : K) :
    v.HasValue g c ↔ g = algebraMap K F c ∨ 0 < v.ord (g - algebraMap K F c) := by
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hg hcm
  have key : v.HasValue g c ↔
      IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hsub⟩ = 0 := by
    have hx : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring c := Subtype.ext (by simp)
    rw [hx, map_sub, sub_eq_zero, v.residue_algebraMap c]
    constructor
    · intro h; exact h.residue_eq
    · intro h; exact ⟨hg, h⟩
  rw [key, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne (g - algebraMap K F c) 0 with h0 | h0
  · have hg' : g = algebraMap K F c := sub_eq_zero.mp h0
    have hz : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) = 0 := Subtype.ext h0
    rw [hz]
    exact ⟨fun _ => Or.inl hg', fun _ => not_isUnit_zero⟩
  · rw [isUnit_iff_ord_eq_zero v hsub h0]
    have hnn := ord_nonneg_of_mem v hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

theorem hasValue_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {c : K} (h : u.HasValue g c) (n : ℕ) : u.HasValue (g ^ n) (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact u.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem exists_hasValue (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) {g : ↥(xHFunctionFieldBar M H)}
    (hg : g ∈ W.toValuationSubring) : ∃ c : AlgebraicClosure ℚ, W.HasValue g c := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  have h1 : Module.finrank (AlgebraicClosure ℚ) W.ResidueField = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed W
  have hsurj : Function.Surjective (algebraMap (AlgebraicClosure ℚ) W.ResidueField) := by
    intro x
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : W.ResidueField) one_ne_zero).mp h1 x
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  obtain ⟨c, hc, -⟩ := W.exists_hasValue_of_surjective hsurj hg
  exact ⟨c, hc⟩

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (g : LaurentSeries R) : coeffMap f (qExpand R N g) = qExpand S N (coeffMap f g) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd (N := N) g hk, qExpand_coeff_of_not_dvd (N := N) (coeffMap f g) hk, map_zero]

end Ws47.D3dH
namespace Ws47
namespace D3d

open AlgebraicCurve

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
variable {A : ValuationSubring (AlgebraicClosure ℚ)}

@[reducible] noncomputable def instA (A : ValuationSubring (AlgebraicClosure ℚ)) : Algebra ↥A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
  ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))).comp A.subtype).toAlgebra

attribute [local instance] instA

theorem mem_ipc_iff (x' b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    b ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') ↔ IsIntegral ↥(Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) b := Iff.rfl

theorem ipc_mul {x' b c : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))} (hb : b ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x')) (hc : c ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x')) : b * c ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') :=
  IsIntegral.mul hb hc

theorem ipc_sub {x' b c : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))} (hb : b ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x')) (hc : c ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x')) : b - c ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') :=
  IsIntegral.sub hb hc

theorem ipc_pow {x' b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))} (hb : b ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x')) (n : ℕ) : b ^ n ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') :=
  IsIntegral.pow hb n

theorem ipc_zero (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : (0 : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') := isIntegral_zero

theorem ipc_add {x' b c : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))} (hb : b ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x')) (hc : c ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x')) : b + c ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') :=
  IsIntegral.add hb hc

theorem ipc_neg {x' b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))} (hb : b ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x')) : -b ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') :=
  IsIntegral.neg hb

theorem ipc_one (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : (1 : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') := isIntegral_one

theorem ipc_const (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (a : ↥A) : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ)) ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') := by
  show IsIntegral _ (algebraMap ↥A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) a)
  rw [IsScalarTower.algebraMap_apply ↥A ↥(Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]
  exact isIntegral_algebraMap

theorem ipc_inv (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : x'⁻¹ ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') := by
  show IsIntegral _ x'⁻¹
  have : x'⁻¹ ∈ Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) := Algebra.subset_adjoin (Set.mem_singleton _)
  exact isIntegral_algebraMap (x := (⟨x'⁻¹, this⟩ : ↥(Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))))))

theorem ipc_mem_of_inv_mem {x' b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))} (hb : b ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x')) (u : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hu : x'⁻¹ ∈ u.toValuationSubring) : b ∈ u.toValuationSubring := by
  obtain ⟨P, hPm, hP⟩ := hb
  refine Ws47.D3a.mem_of_monic u.toValuationSubring (algebraMap ↥(Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    ?_ hPm hP
  rintro ⟨z, hz⟩
  show z ∈ u.toValuationSubring
  induction hz using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff] at hy; subst hy; exact hu
  | algebraMap a => exact u.algebraMap_mem' (a : (AlgebraicClosure ℚ))
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

end Ws47.D3d

namespace Ws47
namespace D3d

open AlgebraicCurve

attribute [local instance] instA

theorem hasValue_add {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {g g' : F} {a a' : K}
    (h : v.HasValue g a) (h' : v.HasValue g' a') : v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_neg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {g : F} {a : K}
    (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

theorem hasValue_sub {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {g g' : F} {a a' : K}
    (h : v.HasValue g a) (h' : v.HasValue g' a') : v.HasValue (g - g') (a - a') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact hasValue_add v h (hasValue_neg v h')

theorem hasValue_zero_of_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {g : F}
    (h : g ∈ v.toValuationSubring.nonunits) : v.HasValue g 0 := by
  obtain ⟨hg, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
  refine ⟨hg, ?_⟩
  rw [map_zero]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hm

theorem ne_zero_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {g : F}
    (h : 0 < v.ord g) : g ≠ 0 := by
  rintro rfl; simp at h

theorem ord_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (W : Place K F) (f : F) (n : ℕ) :
    W.ord (f ^ n) = n * W.ord f := by
  rw [← zpow_natCast, W.ord_zpow]

end Ws47.D3d

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (hcomp : (∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hv : ∃ c, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) c ∧ (Psp.reduceFst α hα) c = v)
    (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (t : ↥(xHFunctionFieldBar M H))
    (ht : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p)
    (hint : ∀ s ∈ (JHPlaceSpecialization.cuspChartSetInf (p := p) A α x' t), s ∈ Rpd.R₁.integers)
    (φ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hφ : α φ ∈ Rpd.R₁.integers)
    (hreg : ∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), Psp.sp u₀ = v → φ ∈ u₀.toValuationSubring) :
    ∃ (s : ↥(xHFunctionFieldBar M H)) (_ : s ∈ (JHPlaceSpecialization.cuspChartSetInf (p := p) A α x' t))
      (e : ↥(xHFunctionFieldBar M H)) (he : e ∈ (JHPlaceSpecialization.cuspChartSetInf (p := p) A α x' t)),
      ¬ v.HasValue (Rpd.R₁.residue ⟨e, hint e he⟩) (0 : ResidueField ↥A) ∧ α φ * e = s := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  classical
  letI := Ws47.D3d.instA (p := p) (M := M) (H := H) (hpM := hpM) A

  have hvna : ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) v := by
    obtain ⟨c, hc, rfl⟩ := hv
    exact ModularCurve.XHDRModelAtP.not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcomp c hc

  have chart_ipc : ∀ (z : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (c : ↥(chartAlgInf p (ΓN p M H hpM) hj)),
      ((z : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : (LaurentSeries (AlgebraicClosure ℚ))) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) → z ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') := by
    intro z c hz

    let ιN : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) →+* ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
      { toFun := fun u => ⟨coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (show (u : LaurentSeries ℚ) ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) from u.2)⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by simp)
        map_zero' := Subtype.ext (by simp)
        map_add' := fun x y => Subtype.ext (by simp) }
    have hιN : ∀ u : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)), ((ιN u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : (LaurentSeries (AlgebraicClosure ℚ))) = coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ) := fun u => rfl
    have hzι : z = ιN (c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) := Subtype.ext (by rw [hιN]; exact hz)

    have hgen : ∀ y : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)), y ∈ Algebra.adjoin (R p) ({(jAt (ΓN p M H hpM) hj)⁻¹} : Set ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) → ιN y ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have : ιN (jAt (ΓN p M H hpM) hj)⁻¹ = x'⁻¹ := by
          apply Subtype.ext
          rw [hιN]
          push_cast
          rw [coe_jAt, map_inv₀, Ws47.ZeroN.coeffEmb_jqModC, hx']
        rw [this]; exact Ws47.D3d.ipc_inv x'
      | algebraMap r =>
        have : ιN (algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) r) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ((ρ r : ↥A) : (AlgebraicClosure ℚ)) := by
          apply Subtype.ext
          rw [hιN]
          have e1 : ((ρ r : ↥A) : (AlgebraicClosure ℚ)) = algebraMap (R p) (AlgebraicClosure ℚ) r := by
            have := congrArg (fun g : R p →+* (AlgebraicClosure ℚ) => g r) hρ
            simpa using this
          show coeffEmb (AlgebraicClosure ℚ) (((algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) r : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)))) : LaurentSeries ℚ) =
            ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ((ρ r : ↥A) : (AlgebraicClosure ℚ)) : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : (LaurentSeries (AlgebraicClosure ℚ)))
          have e2 : (((algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) r : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)))) : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) (r : ℚ) := by
            have h1 : (algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) r : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) = algebraMap ℚ ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (r : ℚ) := rfl
            rw [h1, eq_ratCast (algebraMap ℚ ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) (r : ℚ), SubfieldClass.coe_ratCast, eq_ratCast]
          have e3 : ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ((ρ r : ↥A) : (AlgebraicClosure ℚ)) : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : (LaurentSeries (AlgebraicClosure ℚ))) =
              algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ρ r : ↥A) : (AlgebraicClosure ℚ)) := rfl
          rw [e2, e3, e1, algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]
          exact congrArg (fun c : AlgebraicClosure ℚ => HahnSeries.single (0 : ℤ) c)
            ((IsScalarTower.algebraMap_apply (R p) ℚ (AlgebraicClosure ℚ) r).symm)
        rw [this]; exact Ws47.D3d.ipc_const x' _
      | add y z _ _ hy hz => rw [map_add]; exact Ws47.D3d.ipc_add hy hz
      | mul y z _ _ hy hz => rw [map_mul]; exact Ws47.D3d.ipc_mul hy hz

    obtain ⟨P, hPm, hP⟩ := (show IsIntegral ↥(Algebra.adjoin (R p) ({(jAt (ΓN p M H hpM) hj)⁻¹} : Set ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)))) (c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) from c.2)
    let B := Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    let g : ↥(Algebra.adjoin (R p) ({(jAt (ΓN p M H hpM) hj)⁻¹} : Set ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)))) →+* ↥(integralClosure ↥B ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :=
      (ιN.comp (algebraMap ↥(Algebra.adjoin (R p) ({(jAt (ΓN p M H hpM) hj)⁻¹} : Set ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)))) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)))).codRestrict (integralClosure ↥B ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))).toSubring
        (fun y => by
          show IsIntegral ↥B (ιN (y : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))))
          exact hgen _ y.2)
    have hroot : Polynomial.eval₂ (ιN.comp (algebraMap ↥(Algebra.adjoin (R p) ({(jAt (ΓN p M H hpM) hj)⁻¹} : Set ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)))) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)))) z P = 0 := by
      rw [hzι, ← Polynomial.hom_eval₂, hP, map_zero]
    have hS : IsIntegral ↥(integralClosure ↥B ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) z := by
      refine ⟨P.map g, hPm.map g, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap ↥(integralClosure ↥B ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))).comp g = ιN.comp (algebraMap ↥(Algebra.adjoin (R p) ({(jAt (ΓN p M H hpM) hj)⁻¹} : Set ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)))) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) :=
        RingHom.ext fun _ => rfl
      rw [this]
      exact hroot
    exact isIntegral_trans z hS

  have hCA_IPC : ∀ b ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})), b ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') := by
    intro b hb
    refine Subring.closure_induction (p := fun z _ => z ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x')) ?_ (Ws47.D3d.ipc_zero x') (Ws47.D3d.ipc_one x')
      (fun _ _ _ _ h1 h2 => Ws47.D3d.ipc_add h1 h2) (fun _ _ h => Ws47.D3d.ipc_neg h) (fun _ _ _ _ h1 h2 => Ws47.D3d.ipc_mul h1 h2) hb
    rintro z (⟨a, rfl⟩ | ⟨c, hc⟩)
    · exact Ws47.D3d.ipc_const x' a
    · exact chart_ipc z c hc
  have hB : ∀ b ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})), α b ∈ Rpd.R₁.integers := fun b hb => hint _ (Or.inl ⟨b, hCA_IPC b hb, rfl⟩)
  have hBI : ∀ b ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x'), α b ∈ Rpd.R₁.integers := fun b hb => hint _ (Or.inl ⟨b, hb, rfl⟩)

  have ca_mul : ∀ {b c : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))}, b ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) → c ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) → b * c ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) := fun hb hc => Subring.mul_mem _ hb hc
  have ca_sub : ∀ {b c : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))}, b ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) → c ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) → b - c ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) := fun hb hc => Subring.sub_mem _ hb hc
  have ca_pow : ∀ {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))}, b ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) → ∀ n : ℕ, b ^ n ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) := fun hb n => Subring.pow_mem _ hb n
  have ca_one : (1 : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) := Subring.one_mem _
  have ca_const : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ)) ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) := fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  have ca_inv : x'⁻¹ ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) := by
    refine Subring.subset_closure (Or.inr ⟨TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj), ?_⟩)
    push_cast
    rw [hx', TwoChartIntegralModel.coe_jInvChartInf]
    push_cast
    rw [coe_jAt, map_inv₀, Ws47.ZeroN.coeffEmb_jqModC]

  let red : ∀ b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), b ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) → (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := fun b hb => Rpd.R₁.residue ⟨α b, hB b hb⟩
  have hred_def : ∀ b hb, red b hb = Rpd.R₁.residue ⟨α b, hB b hb⟩ := fun _ _ => rfl
  have hred_mul : ∀ b c hb hc, red (b * c) (ca_mul hb hc) = red b hb * red c hc := by
    intro b c hb hc
    show Rpd.R₁.residue _ = Rpd.R₁.residue _ * Rpd.R₁.residue _
    rw [← map_mul]; congr 1; exact Subtype.ext (map_mul α b c)
  have hred_sub : ∀ b c hb hc, red (b - c) (ca_sub hb hc) = red b hb - red c hc := by
    intro b c hb hc
    show Rpd.R₁.residue _ = Rpd.R₁.residue _ - Rpd.R₁.residue _
    rw [← map_sub]; congr 1; exact Subtype.ext (map_sub α b c)
  have hred_pow : ∀ b hb (n : ℕ), red (b ^ n) (ca_pow hb n) = red b hb ^ n := by
    intro b hb n
    show Rpd.R₁.residue _ = Rpd.R₁.residue _ ^ n
    rw [← map_pow]; congr 1; exact Subtype.ext (map_pow α b n)
  have hred_const : ∀ a : ↥A, red _ (ca_const a) = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A a) := by
    intro a
    show Rpd.R₁.residue _ = _
    have : (⟨α (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))), hB _ (ca_const a)⟩ : ↥Rpd.R₁.integers) =
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a, (Rpd.R₁.algebraMap_mem_iff a).mpr a.2⟩ := Subtype.ext (α.commutes _)
    rw [this, Rpd.R₁.residue_algebraMap]
  have hred_one : red 1 ca_one = 1 := by
    show Rpd.R₁.residue _ = 1
    have : (⟨α 1, hB _ ca_one⟩ : ↥Rpd.R₁.integers) = 1 := Subtype.ext (map_one α)
    rw [this, map_one]

  have hred_zero : ∀ b hb, b = 0 → ∀ τ : (ResidueField ↥A), v.HasValue (red b hb) τ → τ = 0 := by
    intro b hb h0 τ hτ
    have hr : red b hb = 0 := by
      show Rpd.R₁.residue _ = 0
      have : (⟨α b, hB b hb⟩ : ↥Rpd.R₁.integers) = 0 := by
        apply Subtype.ext
        show α b = 0
        rw [h0, map_zero]
      rw [this, map_zero]
    rw [hr] at hτ
    have h1 := v.hasValue_algebraMap (0 : (ResidueField ↥A))
    rw [map_zero] at h1
    exact hτ.unique h1

  have hcuspv : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα W = v →
      (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) W := fun W hW =>
    ModularCurve.XHDRModelAtP.isCuspidal_of_not_isAffinePlace_reduceFst_prolongationDatum
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcomp W (by rw [hW]; exact hvna)
  have hregv : ∀ b hb, (red b hb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ v.toValuationSubring := by
    intro b hb
    obtain ⟨h₁, hr, -⟩ := ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_and_residue_mem_and_mem_of_mem_cuspChartSetInf
      p M H hpM hpM2 A hA θ α hα_coe hα Psp Rpd x' hx' t ht v hvna hcuspv (α b) (Or.inl ⟨b, hCA_IPC b hb, rfl⟩)
    exact hr

  have hred_val : ∀ b hb, ∃ τ : (ResidueField ↥A), v.HasValue (red b hb) τ := by
    intro b hb
    have hm : (red b hb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ v.toValuationSubring := (hregv b hb)
    haveI : AlgebraicCurve.IsCurveOver (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
      ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) (translation_mem_GammaH _ _)
    haveI : Module.Finite (ResidueField ↥A) v.ResidueField := AlgebraicCurve.IsCurveOver.finiteResidue v
    obtain ⟨τ, hτ, -⟩ := v.exists_hasValue_of_surjective (IsSepClosed.algebraMap_surjective _ _) hm
    exact ⟨τ, hτ⟩

  have hjMcoe : ((α x' : ↥(xHFunctionFieldBar M H)) : (LaurentSeries (AlgebraicClosure ℚ))) = jqModC (AlgebraicClosure ℚ) := by rw [hα_coe, hx']
  have hyA : coeffMap A.subtype (jqModC ↥A) = jqModC (AlgebraicClosure ℚ) := coeffMap_jqModC _
  have hymem : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar M H := by
    rw [hyA, ← hjMcoe]; exact (α x').2
  obtain ⟨hj₁', hres₁'⟩ := Rpd.residue₁_coeffMap (jqModC ↥A) hymem
  have heqx : (⟨coeffMap A.subtype (jqModC ↥A), hymem⟩ : ↥(xHFunctionFieldBar M H)) = α x' :=
    Subtype.ext (show coeffMap A.subtype (jqModC ↥A) = _ by rw [hyA, hjMcoe])
  have hj₁ : α x' ∈ Rpd.R₁.integers := heqx ▸ hj₁'
  have hres₁ser : ((Rpd.R₁.residue ⟨α x', hj₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
    have : (⟨α x', hj₁⟩ : ↥Rpd.R₁.integers) = ⟨_, hj₁'⟩ := Subtype.ext heqx.symm
    rw [this, hres₁', coeffMap_jqModC]
  have hres₁ne : Rpd.R₁.residue ⟨α x', hj₁⟩ ≠ 0 := by
    intro h0
    have : ((Rpd.R₁.residue ⟨α x', hj₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = ((0 : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) := by rw [h0]
    rw [hres₁ser, ZeroMemClass.coe_zero] at this
    exact jqModC_ne_zero_of_nontrivial (ResidueField ↥A) this
  have hj0 : jqModC (AlgebraicClosure ℚ) ≠ 0 := jqModC_ne_zero_of_nontrivial (AlgebraicClosure ℚ)
  have hx'0 : x' ≠ 0 := by
    intro h0
    have : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : (LaurentSeries (AlgebraicClosure ℚ))) = ((0 : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : (LaurentSeries (AlgebraicClosure ℚ))) := by rw [h0]
    rw [hx', ZeroMemClass.coe_zero] at this
    exact hj0 this
  have hred_jinv : red x'⁻¹ ca_inv = (Rpd.R₁.residue ⟨α x', hj₁⟩)⁻¹ := by
    show Rpd.R₁.residue _ = _
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul]
    have : (⟨α x', hj₁⟩ * ⟨α x'⁻¹, hB _ ca_inv⟩ : ↥Rpd.R₁.integers) = 1 := by
      apply Subtype.ext
      show α x' * α x'⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hx'0, map_one]
    rw [this, map_one]

  have hjbar_notmem : (Rpd.R₁.residue ⟨α x', hj₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∉ v.toValuationSubring := by
    intro hm
    apply hvna
    haveI : AlgebraicCurve.IsCurveOver (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
      ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) (translation_mem_GammaH _ _)
    haveI : Module.Finite (ResidueField ↥A) v.ResidueField := AlgebraicCurve.IsCurveOver.finiteResidue v
    obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective (IsSepClosed.algebraMap_surjective _ _) hm
    exact ⟨_, a, hres₁ser, ha⟩
  have hjinv_zero : v.HasValue (red x'⁻¹ ca_inv) (0 : (ResidueField ↥A)) := by
    rw [hred_jinv]
    apply Ws47.D3d.hasValue_zero_of_mem_nonunits
    have hmem : (Rpd.R₁.residue ⟨α x', hj₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))⁻¹ ∈ v.toValuationSubring :=
      (v.toValuationSubring.mem_or_inv_mem _).resolve_left hjbar_notmem
    refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨hmem, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hjbar_notmem
    have := (Ws47.OrderH1.isUnit_mk_iff v.toValuationSubring hmem (inv_ne_zero hres₁ne)).mp hu
    rwa [inv_inv] at this

  have killer : ∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), x'⁻¹ ∈ u₀.toValuationSubring → Psp.sp u₀ ≠ v →
      ∃ (b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hb : b ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)}))), 0 < u₀.ord b ∧ ∃ τ : (ResidueField ↥A), τ ≠ 0 ∧ v.HasValue (red b hb) τ := by
    intro u₀ hu₀j hu₀v
    by_cases hAv : ∃ a : ↥A, 0 < u₀.ord (x' - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ)))
    ·
      obtain ⟨a, ha⟩ := hAv
      have hbI : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ)) * x'⁻¹ - 1 ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) :=
        ca_sub (ca_mul (ca_const a) ca_inv) ca_one
      refine ⟨_, hbI, ?_, ?_⟩
      ·
        have hfactor : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ)) * x'⁻¹ - 1 =
            -(x'⁻¹ * (x' - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ)))) := by
          rw [mul_sub, inv_mul_cancel₀ hx'0]; ring
        have hja : x' - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ)) ≠ 0 := Ws47.D3d.ne_zero_of_ord_pos u₀ ha
        have hinv : (0 : ℤ) ≤ u₀.ord x'⁻¹ := Ws47.D3dH.ord_nonneg_of_mem u₀ hu₀j
        have hordneg : ∀ g : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), u₀.ord (-g) = u₀.ord g := fun g => by
          unfold Place.ord; rw [Valuation.map_neg]
        rw [hfactor, hordneg, u₀.ord_mul (inv_ne_zero hx'0) hja]
        omega
      ·
        refine ⟨IsLocalRing.residue ↥A a * 0 - 1, by simp, ?_⟩
        rw [hred_sub _ _ (ca_mul (ca_const a) ca_inv) ca_one,
          hred_mul _ _ (ca_const a) ca_inv, hred_const, hred_one]
        exact Ws47.D3d.hasValue_sub v ((v.hasValue_algebraMap _).mul hjinv_zero) v.hasValue_one
    ·
      have hpole : ∀ a : ↥A, u₀.ord (x' - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ≤ 0 :=
        fun a => not_lt.mp fun h => hAv ⟨a, h⟩

      obtain ⟨a₀, ha₀, hspa₀⟩ := ModularCurve.XHDRModelAtP.exists_hasValue_and_hasValue_sp_residue_of_mem_closure_chartAlgInf_of_cusp
        p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hres₂α hcomp x' hx' hB x'⁻¹ ca_inv u₀ hpole
      have ha₀0 : IsLocalRing.residue ↥A a₀ = 0 := by
        by_contra hne0
        have hu : IsUnit a₀ := by
          by_contra h; exact hne0 ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
        have hc0 : ((a₀ : ↥A) : (AlgebraicClosure ℚ)) ≠ 0 := fun h0 => hu.ne_zero (Subtype.ext h0)
        obtain ⟨au, hau⟩ := hu
        have hinvval : u₀.HasValue x' (((au⁻¹ : (↥A)ˣ) : ↥A) : (AlgebraicClosure ℚ)) := by
          have h1 : (((au⁻¹ : (↥A)ˣ) : ↥A) : (AlgebraicClosure ℚ)) = (((a₀ : ↥A) : (AlgebraicClosure ℚ)))⁻¹ := by
            have e1 : ((au⁻¹ : (↥A)ˣ) : ↥A) * a₀ = 1 := by rw [← hau]; exact Units.inv_mul au
            have e2 := congrArg (fun z : ↥A => (z : (AlgebraicClosure ℚ))) e1
            simp only [Subring.coe_mul, OneMemClass.coe_one] at e2
            exact eq_inv_of_mul_eq_one_left (by simpa using e2)
          rw [h1]
          have := ha₀.inv hc0
          rwa [inv_inv] at this
        have hne : x' ≠ algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ((((au⁻¹ : (↥A)ˣ) : ↥A) : (AlgebraicClosure ℚ))) := by
          intro h
          have := congrArg (fun z : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) => (z : (LaurentSeries (AlgebraicClosure ℚ))).coeff (-1 : ℤ)) h
          have hcoe : ∀ d : (AlgebraicClosure ℚ), ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) d : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : (LaurentSeries (AlgebraicClosure ℚ))) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) d := fun d => rfl
          simp only [hx', coeff_jqModC_neg_one, hcoe, algebraMap_laurentSeries_eq_single,
            HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by norm_num)] at this
          exact one_ne_zero this
        have hpos := Ws47.ZeroN.ord_sub_algebraMap_pos u₀ hinvval hne
        have := hpole ((au⁻¹ : (↥A)ˣ) : ↥A)
        omega
      have hspa₀' : (Psp.sp u₀).HasValue (red x'⁻¹ ca_inv) 0 := by
        rw [ha₀0] at hspa₀; exact hspa₀
      rw [hred_jinv] at hspa₀'
      have hspna : ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) (Psp.sp u₀) := by
        rintro ⟨xb, c, hxb, hc⟩
        have hxb' : xb = Rpd.R₁.residue ⟨α x', hj₁⟩ := Subtype.ext (by rw [hxb, hres₁ser])
        rw [hxb'] at hc
        have h1 := hc.mul hspa₀'
        rw [mul_inv_cancel₀ hres₁ne, mul_zero] at h1
        have h2 := (Psp.sp u₀).hasValue_one
        exact one_ne_zero (h2.unique h1)

      obtain ⟨b, hb, hbsp, hbv⟩ := ModularCurve.XHDRModelAtP.exists_mem_closure_chartAlgInf_hasValue_residue_zero_and_not_hasValue_of_not_isAffinePlace_of_ne
        p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hres₂α hcomp x' hx' hB v (Psp.sp u₀) hvna hspna hu₀v
      obtain ⟨c, hu₀c, hspc⟩ := ModularCurve.XHDRModelAtP.exists_hasValue_and_hasValue_sp_residue_of_mem_closure_chartAlgInf_of_cusp
        p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hres₂α hcomp x' hx' hB b hb u₀ hpole
      have hc0 : IsLocalRing.residue ↥A c = 0 := hspc.unique hbsp
      have hb'I : b - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (c : (AlgebraicClosure ℚ)) ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)})) := ca_sub hb (ca_const c)
      have hred_b' : red _ hb'I = red b hb := by
        rw [hred_sub _ _ hb (ca_const c), hred_const, hc0, map_zero, sub_zero]
      refine ⟨_, hb'I, ?_, ?_⟩
      · rcases (Ws47.D3dH.hasValue_iff_eq_or_ord_sub_pos u₀ hu₀c.mem _).mp hu₀c with heq | hpos
        · exfalso
          apply hbv
          show v.HasValue (red b hb) 0
          subst heq
          have : red _ hb = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c) := hred_const c
          rw [this, hc0, map_zero]
          have h1 := v.hasValue_algebraMap (0 : (ResidueField ↥A)); rwa [map_zero] at h1
        · exact hpos
      · obtain ⟨τ, hτ⟩ := hred_val _ hb'I
        refine ⟨τ, fun hτ0 => hbv ?_, hτ⟩
        show v.HasValue (red b hb) 0
        rw [← hred_b', ← hτ0]; exact hτ

  have clearing_aux : ∀ (n : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) → ℕ) (T : Finset (Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (∀ u ∈ T, x'⁻¹ ∈ u.toValuationSubring ∧ Psp.sp u ≠ v) →
      ∃ (e : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (he : e ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)}))), (∃ τ : (ResidueField ↥A), τ ≠ 0 ∧ v.HasValue (red e he) τ) ∧
        ∀ u ∈ T, (n u : ℤ) ≤ u.ord e := by
    intro n T
    refine Finset.induction_on T ?_ ?_
    · intro _
      refine ⟨1, ca_one, ⟨1, one_ne_zero, ?_⟩, fun u hu => absurd hu (by simp)⟩
      rw [hred_one]; exact v.hasValue_one
    · intro u T huT ih hT
      obtain ⟨e₁, he₁, ⟨τ₁, hτ₁0, hτ₁⟩, hbound⟩ := ih fun w hw => hT w (Finset.mem_insert_of_mem hw)
      obtain ⟨huj, huv⟩ := hT u (Finset.mem_insert_self u T)
      obtain ⟨b, hb, hbu, τ, hτ0, hτ⟩ := killer u huj huv
      refine ⟨b ^ n u * e₁, ca_mul (ca_pow hb _) he₁, ⟨τ ^ n u * τ₁, mul_ne_zero (pow_ne_zero _ hτ0) hτ₁0, ?_⟩, ?_⟩
      · rw [hred_mul _ _ (ca_pow hb _) he₁, hred_pow _ hb]
        exact (Ws47.D3dH.hasValue_pow v hτ _).mul hτ₁
      · have hb0 : b ≠ 0 := Ws47.D3d.ne_zero_of_ord_pos u hbu
        have he₁0 : e₁ ≠ 0 := fun h0 => hτ₁0 (hred_zero e₁ he₁ h0 τ₁ hτ₁)
        intro w hw
        rw [w.ord_mul (pow_ne_zero _ hb0) he₁0, Ws47.D3d.ord_pow]
        rcases Finset.mem_insert.mp hw with hwu | hwT
        · subst hwu
          have h1 : (0 : ℤ) ≤ w.ord e₁ := Ws47.D3dH.ord_nonneg_of_mem w (Ws47.D3d.ipc_mem_of_inv_mem (hCA_IPC _ he₁) w huj)
          have h2 : (n w : ℤ) * 1 ≤ (n w : ℤ) * w.ord b := mul_le_mul_of_nonneg_left hbu (Int.natCast_nonneg _)
          linarith
        · have h1 : (0 : ℤ) ≤ w.ord b :=
            Ws47.D3dH.ord_nonneg_of_mem w (Ws47.D3d.ipc_mem_of_inv_mem (hCA_IPC _ hb) w (hT w (Finset.mem_insert_of_mem hwT)).1)
          have h2 : (0 : ℤ) ≤ (n u : ℤ) * w.ord b := mul_nonneg (Int.natCast_nonneg _) h1
          have h3 := hbound w hwT
          linarith

  have clearing : ∃ (e : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (he : e ∈ (Subring.closure (Set.range (fun a : ↥A => algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ∪
        {b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) | ∃ c : ↥(chartAlgInf p (ΓN p M H hpM) hj),
          ((b : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)}))), (∃ τ : (ResidueField ↥A), τ ≠ 0 ∧ v.HasValue (red e he) τ) ∧
      ∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), x'⁻¹ ∈ u₀.toValuationSubring → φ * e ∈ u₀.toValuationSubring := by
    by_cases hφ0 : φ = 0
    · refine ⟨1, ca_one, ⟨1, one_ne_zero, by rw [hred_one]; exact v.hasValue_one⟩, fun u₀ _ => ?_⟩
      rw [hφ0, zero_mul]; exact zero_mem _
    haveI := ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := (AlgebraicClosure ℚ)) φ hφ0
    let T : Finset (Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) := D.support.filter (fun u => x'⁻¹ ∈ u.toValuationSubring ∧ u.ord φ < 0)
    have hTprop : ∀ u ∈ T, x'⁻¹ ∈ u.toValuationSubring ∧ Psp.sp u ≠ v := by
      intro u hu
      obtain ⟨-, huj, huord⟩ := Finset.mem_filter.mp hu
      refine ⟨huj, fun huv => ?_⟩
      have := Ws47.D3dH.ord_nonneg_of_mem u (hreg u huv)
      omega
    obtain ⟨e, he, hev, hbound⟩ := clearing_aux (fun u => (-u.ord φ).toNat) T hTprop
    refine ⟨e, he, hev, fun u₀ hu₀ => ?_⟩
    have he_mem : e ∈ u₀.toValuationSubring := Ws47.D3d.ipc_mem_of_inv_mem (hCA_IPC _ he) u₀ hu₀
    by_cases hpole : u₀.ord φ < 0
    · have hu₀T : u₀ ∈ T := by
        simp only [T, Finset.mem_filter, Finsupp.mem_support_iff, hD u₀]
        exact ⟨by omega, hu₀, hpole⟩
      have h1 : (((-u₀.ord φ).toNat : ℕ) : ℤ) ≤ u₀.ord e := hbound u₀ hu₀T
      rw [Int.toNat_of_nonneg (by omega)] at h1
      obtain ⟨τ, hτ0, hτ⟩ := hev
      have he0 : e ≠ 0 := fun h0 => hτ0 (hred_zero e he h0 τ hτ)
      refine Ws47.D3dH.mem_of_ord_nonneg u₀ (mul_ne_zero hφ0 he0) ?_
      rw [u₀.ord_mul hφ0 he0]; omega
    · exact mul_mem (Ws47.D3dH.mem_of_ord_nonneg u₀ hφ0 (not_lt.mp hpole)) he_mem

  obtain ⟨e₀, he₀, ⟨τ, hτ0, hτ⟩, hclear⟩ := clearing
  have hψ₁ : α (φ * e₀) ∈ Rpd.R₁.integers := by rw [map_mul]; exact mul_mem hφ (hB e₀ he₀)
  have hψIPC : φ * e₀ ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') :=
    ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integralOverPoleChart_of_mem_integers_of_forall_inv_mem_imp_mem p M H hpM hpM2 hHp A hA θ α hα_coe hα Psp Rpd x' hx' (φ * e₀) hψ₁ hclear
  refine ⟨α (φ * e₀), Or.inl ⟨_, hψIPC, rfl⟩, α e₀, Or.inl ⟨_, hCA_IPC _ he₀, rfl⟩, ?_, (map_mul α φ e₀).symm⟩
  intro h0
  exact hτ0 (hτ.unique h0)

end S_ModularCurve_XHDRModelAtP_exists_mul_eq_of_mem_integers_of_forall_sp_eq_cuspChartSetInf_prolongationDatum
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_mul_eq_of_mem_integers_of_forall_sp_eq_cuspChartSetInf_prolongationDatum (solution)
