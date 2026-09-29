-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/13a83e4e-b87e-5faf-848a-31af8f44d5bf

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois
import Theorems.Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_three
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun"
p2m_attr_erase "simp" "KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_three.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_three.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups Pointwise

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar coeffMap instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable modularFunctionFieldC ssPlaces"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty fieldBar Idx levelAutBar redQ exists_finite_subgroup_forall_levelAutBar_mem levelAutBar_mul comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_three exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_three mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_three"
namespace IdentIgGlobal
p2m_open "ModularCurve.FullLevel ModularCurve"

theorem mem_iff_symm_mem_of_smul_eq {E F : Type*} [Field E] [Field F] [Algebra E F]
    (σ : F ≃ₐ[E] F) (S T : ValuationSubring F) (h : σ • S = T) (y : F) :
    y ∈ T ↔ σ.symm y ∈ S := by
  rw [← h, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem smul_coe_eq_of_fixedPoints {G F : Type*} [Group G] [Field F] [MulSemiringAction G F]
    (x : FixedPoints.subfield G F) (g : G) : g • (x : F) = x :=
  x.2 g

theorem exists_smul_eq_apply {G F : Type*} [Group G] [Field F] [MulSemiringAction G F] [Finite G]
    (σ : F ≃ₐ[FixedPoints.subfield G F] F) : ∃ g : G, ∀ y : F, g • y = σ y := by
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective G F σ
  exact ⟨g, fun y => by rw [← hg]; rfl⟩

theorem levelAutBar_one (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') (ζ : Idx q) :
    levelAutBar q M' ζ 1 = AlgEquiv.refl := by
  have h := levelAutBar_mul q M' hqM' ζ 1 1 (one_mem _) (one_mem _)
  rw [mul_one] at h
  apply AlgEquiv.ext
  intro y
  have hy : levelAutBar q M' ζ 1 y = levelAutBar q M' ζ 1 (levelAutBar q M' ζ 1 y) := by
    conv_lhs => rw [h]
    rfl
  exact ((levelAutBar q M' ζ 1).injective hy).symm

theorem levelAutBar_inv_apply (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (y : fieldBar q M') :
    levelAutBar q M' ζ γ⁻¹ y = (levelAutBar q M' ζ γ).symm y := by
  have h := levelAutBar_mul q M' hqM' ζ γ⁻¹ γ (inv_mem hγ) hγ
  rw [inv_mul_cancel, levelAutBar_one q M' hqM' ζ] at h
  have hy : levelAutBar q M' ζ γ (levelAutBar q M' ζ γ⁻¹ y) = y := by
    have := congrArg (fun e : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M' => e y) h
    exact this.symm
  rw [eq_comm, AlgEquiv.symm_apply_eq]
  exact hy.symm

theorem comap_trans {K F : Type*} [Field K] [Field F] [Algebra K F]
    (S : ValuationSubring F) (e₁ e₂ : F ≃ₐ[K] F) :
    S.comap (e₁.trans e₂).toAlgHom.toRingHom =
      (S.comap e₂.toAlgHom.toRingHom).comap e₁.toAlgHom.toRingHom := by
  ext y
  simp only [ValuationSubring.mem_comap]
  rfl

end ModularCurve.FullLevel.IdentIgGlobal

open ModularCurve.FullLevel.IdentIgGlobal in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)

    (O : ValuationSubring (fieldBar q M'))
    (hOA : ∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A)
    (hOR₀ : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers →
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ O) :
    ∃ ℓ : CuspidalType.ProjLine q, O = OIg ℓ := by
  classical

  obtain ⟨G, hGfin, hGmem, hGsurj⟩ := exists_finite_subgroup_forall_levelAutBar_mem q M' hqM' ζ
  haveI : Finite G := hGfin
  letI act : MulSemiringAction G (fieldBar q M') := MulSemiringAction.compHom _ G.subtype
  have hact : ∀ (g : G) (y : fieldBar q M'), g • y = (g : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') y :=
    fun g y => rfl

  have hE : ∀ x : FixedPoints.subfield G (fieldBar q M'),
      algebraMap (FixedPoints.subfield G (fieldBar q M')) (fieldBar q M') x ∈ OIg (lineInfty q) ↔
        algebraMap (FixedPoints.subfield G (fieldBar q M')) (fieldBar q M') x ∈ O := by
    intro x
    have hfix : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M' → levelAutBar q M' ζ γ (x : fieldBar q M') = x := by
      intro γ hγ
      rw [← hact ⟨levelAutBar q M' ζ γ, hGmem γ hγ⟩ (x : fieldBar q M')]
      exact smul_coe_eq_of_fixedPoints x _
    obtain ⟨g, hg, hxg⟩ :=
      exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_three q hq3 M' hqM' ζ (x : fieldBar q M') hfix
    exact (mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_three q hq3 M' hqM' A hA hle R₀
      hR₀ OIg hIg_inf O hOA hOR₀ (x : fieldBar q M') g hg hxg).symm

  obtain ⟨σ, hσ⟩ := ValuationSubring.exists_smul_eq_of_forall_algebraMap_mem_iff_of_isGalois
    (E := FixedPoints.subfield G (fieldBar q M')) (OIg (lineInfty q)) O hE

  obtain ⟨g, hg⟩ := exists_smul_eq_apply σ
  obtain ⟨γ, hγ, hgγ⟩ := hGsurj (g : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') g.2
  have hσy : ∀ y : fieldBar q M', σ y = levelAutBar q M' ζ γ y := by
    intro y
    have h1 := hg y
    have h2 := hact g y
    rw [hgγ] at h2
    exact h1.symm.trans h2
  have hσsymm : ∀ y : fieldBar q M', σ.symm y = levelAutBar q M' ζ γ⁻¹ y := by
    intro y
    rw [levelAutBar_inv_apply q M' hqM' ζ γ hγ, AlgEquiv.symm_apply_eq]
    rw [hσy, AlgEquiv.apply_symm_apply]

  have hO : O = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ⁻¹).toAlgHom.toRingHom := by
    ext y
    rw [mem_iff_symm_mem_of_smul_eq σ _ _ hσ y, ValuationSubring.mem_comap, hσsymm]
    rfl

  obtain ⟨γℓ, hγℓ, hℓ, hOIgℓ⟩ := hIg (redQ q γ⁻¹ • lineInfty q)
  refine ⟨redQ q γ⁻¹ • lineInfty q, ?_⟩
  have hβmem : γℓ⁻¹ * γ⁻¹ ∈ Gamma0 M' := mul_mem (inv_mem hγℓ) (inv_mem hγ)
  have hβfix : redQ q (γℓ⁻¹ * γ⁻¹) • lineInfty q = lineInfty q := by
    rw [map_mul, map_inv, mul_smul, ← hℓ, inv_smul_smul]
  have hK1 := comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_three q hq3 M' hqM' A hA ζ (OIg (lineInfty q)) hIg_inf
    (γℓ⁻¹ * γ⁻¹) hβmem hβfix
  have hδeq : γ⁻¹ = γℓ * (γℓ⁻¹ * γ⁻¹) := by rw [mul_inv_cancel_left]
  rw [hO, hOIgℓ, hδeq, levelAutBar_mul q M' hqM' ζ γℓ (γℓ⁻¹ * γ⁻¹) hγℓ hβmem, comap_trans, hK1]

end S_ModularCurve_FullLevel_exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_three (solution)
