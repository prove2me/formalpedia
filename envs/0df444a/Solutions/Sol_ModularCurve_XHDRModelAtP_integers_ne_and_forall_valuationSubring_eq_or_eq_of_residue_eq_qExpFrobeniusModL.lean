-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/18b651fa-41dd-55b0-8299-e6996c74572c

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one
import Theorems.Thm_ModularCurve_XHDRModelAtP_integers_snd_isGeneric_and_forall_exists_valuation_alpha_sub_pow_lt_one_of_residue_eq_qExpFrobeniusModL
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_not_integers_le_integers_and_not_integers_le_integers
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_finrank_adjoin_residue_add_finrank_adjoin_residue_eq_finrank_adjoin
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq
import Theorems.Thm_ModularCurve_exists_algHom_xHFunctionFieldBar_div_infSubgroup_isIntegral_and_coe_eq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

section Ws2GenericUnique
open Polynomial

namespace GaussResAux

theorem residue_eval₂_eq_eval₂_map_residue {A O : Type*} [CommRing A] [IsLocalRing A] [CommRing O] [IsLocalRing O]
    (φ : A →+* O) [IsLocalHom φ] (x : O) (P : A[X]) :
    IsLocalRing.residue O (P.eval₂ φ x) =
      (P.map (IsLocalRing.residue A)).eval₂ (IsLocalRing.ResidueField.map φ) (IsLocalRing.residue O x) := by
  rw [Polynomial.eval₂_map, Polynomial.hom_eval₂]
  rfl

theorem residue_aeval_eq {A F : Type*} [CommRing A] [IsLocalRing A] [Field F] [Algebra A F]
    (O : ValuationSubring F) (hAO : ∀ a : A, algebraMap A F a ∈ O)
    (φ : A →+* ↥O) (hφ : ∀ a, ((φ a : ↥O) : F) = algebraMap A F a) [IsLocalHom φ]
    (x : ↥O) (P : A[X]) (hP : aeval (x : F) P ∈ O) :
    IsLocalRing.residue ↥O ⟨aeval (x : F) P, hP⟩ =
      (P.map (IsLocalRing.residue A)).eval₂ (IsLocalRing.ResidueField.map φ) (IsLocalRing.residue ↥O x) := by
  have key : (⟨aeval (x : F) P, hP⟩ : ↥O) = P.eval₂ φ x := by
    apply Subtype.ext
    show aeval (x : F) P = ((P.eval₂ φ x : ↥O) : F)
    rw [Polynomial.aeval_def, show ((P.eval₂ φ x : ↥O) : F) = P.eval₂ (O.subtype.comp φ) (x : F) from
      (Polynomial.hom_eval₂ P φ O.subtype x)]
    congr 1
    ext a
    exact (hφ a).symm
  rw [key]
  exact residue_eval₂_eq_eval₂_map_residue φ x P

theorem eval₂_map_residue_ne_zero_of_isUnit {A O : Type*} [CommRing A] [IsLocalRing A] [CommRing O] [IsLocalRing O]
    (φ : A →+* O) [IsLocalHom φ] (x : O) (P : A[X]) (hu : IsUnit (P.eval₂ φ x)) :
    (P.map (IsLocalRing.residue A)).eval₂ (IsLocalRing.ResidueField.map φ) (IsLocalRing.residue O x) ≠ 0 := by
  rw [← residue_eval₂_eq_eval₂_map_residue]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu

theorem eval₂_residue_ne_zero_of_forall_isUnit {A O : Type*} [CommRing A] [IsLocalRing A] [CommRing O] [IsLocalRing O]
    (φ : A →+* O) [IsLocalHom φ] (x : O)
    (hgauss : ∀ P : A[X], P.map (IsLocalRing.residue A) ≠ 0 → IsUnit (P.eval₂ φ x))
    (p : (IsLocalRing.ResidueField A)[X]) (hp : p ≠ 0) :
    p.eval₂ (IsLocalRing.ResidueField.map φ) (IsLocalRing.residue O x) ≠ 0 := by
  obtain ⟨P, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue A) IsLocalRing.residue_surjective p
  exact eval₂_map_residue_ne_zero_of_isUnit φ x P (hgauss P hp)

theorem transcendental_residue_of_forall_isUnit {A O : Type*} [CommRing A] [IsLocalRing A] [CommRing O] [IsLocalRing O]
    (φ : A →+* O) [IsLocalHom φ] (x : O)
    [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField O)]
    (halg : algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField O) = IsLocalRing.ResidueField.map φ)
    (hgauss : ∀ P : A[X], P.map (IsLocalRing.residue A) ≠ 0 → IsUnit (P.eval₂ φ x)) :
    Transcendental (IsLocalRing.ResidueField A) (IsLocalRing.residue O x) := by
  rw [transcendental_iff]
  intro p hp0
  by_contra hp
  apply eval₂_residue_ne_zero_of_forall_isUnit φ x hgauss p hp
  rw [← halg]
  exact hp0

theorem isUnit_eval₂_of_eval₂_map_residue_ne_zero {A O : Type*} [CommRing A] [IsLocalRing A] [CommRing O] [IsLocalRing O]
    (φ : A →+* O) [IsLocalHom φ] (x : O) (Q : A[X])
    (hQ : (Q.map (IsLocalRing.residue A)).eval₂ (IsLocalRing.ResidueField.map φ) (IsLocalRing.residue O x) ≠ 0) :
    IsUnit (Q.eval₂ φ x) := by
  rw [← residue_eval₂_eq_eval₂_map_residue] at hQ
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hQ

theorem residue_eval₂_mul_inv_eq {A O : Type*} [CommRing A] [IsLocalRing A] [CommRing O] [IsLocalRing O]
    (φ : A →+* O) [IsLocalHom φ] (x : O) (P Q : A[X])
    (hQ : (Q.map (IsLocalRing.residue A)).eval₂ (IsLocalRing.ResidueField.map φ) (IsLocalRing.residue O x) ≠ 0) :
    IsLocalRing.residue O (P.eval₂ φ x * ↑((isUnit_eval₂_of_eval₂_map_residue_ne_zero φ x Q hQ).unit⁻¹)) =
      (P.map (IsLocalRing.residue A)).eval₂ (IsLocalRing.ResidueField.map φ) (IsLocalRing.residue O x) *
        ((Q.map (IsLocalRing.residue A)).eval₂ (IsLocalRing.ResidueField.map φ) (IsLocalRing.residue O x))⁻¹ := by
  rw [map_mul, residue_eval₂_eq_eval₂_map_residue]
  congr 1
  apply eq_inv_of_mul_eq_one_left
  rw [← residue_eval₂_eq_eval₂_map_residue, ← map_mul, IsUnit.val_inv_mul, map_one]

theorem adjoin_residue_eq_top_of_forall_exists {A O : Type*} [CommRing A] [IsLocalRing A] [CommRing O] [IsLocalRing O]
    (φ : A →+* O) [IsLocalHom φ] (x : O)
    [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField O)]
    (halg : algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField O) = IsLocalRing.ResidueField.map φ)
    (hfrac : ∀ b : O, ∃ P Q : A[X],
      ∃ hQ : (Q.map (IsLocalRing.residue A)).eval₂ (IsLocalRing.ResidueField.map φ) (IsLocalRing.residue O x) ≠ 0,
        b = P.eval₂ φ x * ↑((isUnit_eval₂_of_eval₂_map_residue_ne_zero φ x Q hQ).unit⁻¹)) :
    IntermediateField.adjoin (IsLocalRing.ResidueField A) ({IsLocalRing.residue O x} : Set (IsLocalRing.ResidueField O)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨P, Q, hQ, rfl⟩ := hfrac b
  rw [residue_eval₂_mul_inv_eq φ x P Q hQ]
  have hmem : ∀ R : A[X], (R.map (IsLocalRing.residue A)).eval₂ (IsLocalRing.ResidueField.map φ) (IsLocalRing.residue O x) ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField A) ({IsLocalRing.residue O x} : Set (IsLocalRing.ResidueField O)) := by
    intro R
    rw [← halg, ← Polynomial.aeval_def]
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
  exact mul_mem (hmem P) (inv_mem (hmem Q))

end GaussResAux

namespace GRG

open Polynomial

noncomputable def toO {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring K) (O : ValuationSubring L)
    (hOA : ∀ c : K, algebraMap K L c ∈ O ↔ c ∈ A) : ↥A →+* ↥O where
  toFun a := ⟨algebraMap K L a, (hOA a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_toO {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring K) (O : ValuationSubring L)
    (hOA : ∀ c : K, algebraMap K L c ∈ O ↔ c ∈ A) (a : ↥A) : ((toO A O hOA a : ↥O) : L) = algebraMap K L a := rfl

theorem isUnit_of_inv_mem {L : Type*} [Field L] (O : ValuationSubring L) (y : L) (hy : y ∈ O) (hy' : y⁻¹ ∈ O) (hy0 : y ≠ 0) :
    IsUnit (⟨y, hy⟩ : ↥O) :=
  ⟨⟨⟨y, hy⟩, ⟨y⁻¹, hy'⟩, Subtype.ext (mul_inv_cancel₀ hy0), Subtype.ext (inv_mul_cancel₀ hy0)⟩, rfl⟩

theorem isLocalHom_toO {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring K) (O : ValuationSubring L)
    (hOA : ∀ c : K, algebraMap K L c ∈ O ↔ c ∈ A) : IsLocalHom (toO A O hOA) := by
  constructor
  intro a ha
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    apply ha.ne_zero
    exact Subtype.ext (by simp [h0])

  have hinvO : algebraMap K L ((a : K)⁻¹) ∈ O := by
    obtain ⟨u, hu⟩ := ha
    have hval : ((u⁻¹ : (↥O)ˣ) : ↥O).1 = (algebraMap K L (a : K))⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      have h := congrArg (fun z : ↥O => (z : L)) u.mul_inv
      simpa [hu] using h
    rw [map_inv₀, ← hval]
    exact ((u⁻¹ : (↥O)ˣ) : ↥O).2
  have hinvA : (a : K)⁻¹ ∈ A := (hOA _).mp hinvO
  exact ⟨⟨a, ⟨(a : K)⁻¹, hinvA⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩

theorem algebraMap_residueField_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring K)
    (x : L) (hx : Transcendental K x)
    (O : ValuationSubring L)
    (hOA : ∀ c : K, algebraMap K L c ∈ O ↔ c ∈ A)
    (hxO : x ∈ O)
    (hOx : ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval x (Q.map A.subtype) ∈ O ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O)
    [Algebra (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥O)]
    (hcompat : ∀ a : ↥A, algebraMap (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥O) (IsLocalRing.residue ↥A a) =
      IsLocalRing.residue ↥O ⟨algebraMap K L a, (hOA a).mpr a.2⟩) :
    haveI := isLocalHom_toO A O hOA
    algebraMap (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥O) = IsLocalRing.ResidueField.map (toO A O hOA) := by
  haveI := isLocalHom_toO A O hOA
  apply RingHom.ext
  intro z
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
  rw [hcompat a]
  rfl

theorem coe_eval₂_toO {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring K) (O : ValuationSubring L)
    (hOA : ∀ c : K, algebraMap K L c ∈ O ↔ c ∈ A) (x : L) (hxO : x ∈ O) (Q : Polynomial ↥A) :
    ((Q.eval₂ (toO A O hOA) ⟨x, hxO⟩ : ↥O) : L) = Polynomial.aeval x (Q.map A.subtype) := by
  rw [show ((Q.eval₂ (toO A O hOA) ⟨x, hxO⟩ : ↥O) : L) = Q.eval₂ (O.subtype.comp (toO A O hOA)) x from
    Polynomial.hom_eval₂ Q (toO A O hOA) O.subtype ⟨x, hxO⟩, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1

theorem isUnit_eval₂_toO
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring K)
    (x : L) (hx : Transcendental K x)
    (O : ValuationSubring L)
    (hOA : ∀ c : K, algebraMap K L c ∈ O ↔ c ∈ A)
    (hxO : x ∈ O)
    (hOx : ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval x (Q.map A.subtype) ∈ O ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O)
    [Algebra (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥O)]
    (hcompat : ∀ a : ↥A, algebraMap (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥O) (IsLocalRing.residue ↥A a) =
      IsLocalRing.residue ↥O ⟨algebraMap K L a, (hOA a).mpr a.2⟩)
    (Q : Polynomial ↥A) (hQ : Q.map (IsLocalRing.residue ↥A) ≠ 0) :
    IsUnit (Q.eval₂ (toO A O hOA) ⟨x, hxO⟩) := by
  have hQ0 : Q.map A.subtype ≠ 0 := by
    intro h0
    apply hQ
    have : Q = 0 := by
      apply (Polynomial.map_injective A.subtype Subtype.coe_injective)
      rw [h0, Polynomial.map_zero]
    rw [this, Polynomial.map_zero]
  have hne : Polynomial.aeval x (Q.map A.subtype) ≠ 0 := fun h0 => hQ0 (by
    by_contra hne
    exact hx ⟨Q.map A.subtype, hne, h0⟩)
  obtain ⟨h1, h2⟩ := hOx Q hQ
  have key : Q.eval₂ (toO A O hOA) ⟨x, hxO⟩ = ⟨Polynomial.aeval x (Q.map A.subtype), h1⟩ :=
    Subtype.ext (coe_eval₂_toO A O hOA x hxO Q)
  rw [key]
  exact isUnit_of_inv_mem O _ h1 h2 hne

theorem transcendental_residue
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring K)
    (x : L) (hx : Transcendental K x)
    (O : ValuationSubring L)
    (hOA : ∀ c : K, algebraMap K L c ∈ O ↔ c ∈ A)
    (hxO : x ∈ O)
    (hOx : ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval x (Q.map A.subtype) ∈ O ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O)
    [Algebra (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥O)]
    (hcompat : ∀ a : ↥A, algebraMap (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥O) (IsLocalRing.residue ↥A a) =
      IsLocalRing.residue ↥O ⟨algebraMap K L a, (hOA a).mpr a.2⟩) :
    Transcendental (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥O ⟨x, hxO⟩) := by
  haveI := isLocalHom_toO A O hOA
  exact GaussResAux.transcendental_residue_of_forall_isUnit (toO A O hOA) ⟨x, hxO⟩
    (algebraMap_residueField_eq A x hx O hOA hxO hOx hcompat)
    (fun Q hQ => isUnit_eval₂_toO A x hx O hOA hxO hOx hcompat Q hQ)

theorem adjoin_residue_eq_top {A O : Type*} [CommRing A] [IsLocalRing A] [CommRing O] [IsLocalRing O]
    (φ : A →+* O) [IsLocalHom φ] (xO : O)
    [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField O)]
    (halg : algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField O) =
      (IsLocalRing.ResidueField.map φ : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField O))
    (hunit : ∀ Q : Polynomial A, Q.map (IsLocalRing.residue A) ≠ 0 → IsUnit (Q.eval₂ φ xO))
    (hfrac : ∀ b : O, ∃ (P Q : Polynomial A) (hQ : Q.map (IsLocalRing.residue A) ≠ 0),
      b = P.eval₂ φ xO * ↑((hunit Q hQ).unit⁻¹ : Oˣ)) :
    IntermediateField.adjoin (IsLocalRing.ResidueField A)
      ({IsLocalRing.residue O xO} : Set (IsLocalRing.ResidueField O)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨P, Q, hQ, rfl⟩ := hfrac b
  have hmem : ∀ R : Polynomial A, IsLocalRing.residue O (R.eval₂ φ xO) ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField A) ({IsLocalRing.residue O xO} : Set (IsLocalRing.ResidueField O)) := by
    intro R
    rw [GaussResAux.residue_eval₂_eq_eval₂_map_residue, ← halg, ← Polynomial.aeval_def]
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
  rw [map_mul]
  refine mul_mem (hmem P) ?_

  have hinv : IsLocalRing.residue O (↑((hunit Q hQ).unit⁻¹ : Oˣ)) = (IsLocalRing.residue O (Q.eval₂ φ xO))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  rw [hinv]
  exact inv_mem (hmem Q)

theorem exists_eq_C_mul_map {K : Type*} [Field K] (A : ValuationSubring K) (P : Polynomial K) (hP : P ≠ 0) :
    ∃ (c : K) (Q : Polynomial ↥A), c ≠ 0 ∧ Q.map (IsLocalRing.residue ↥A) ≠ 0 ∧ P = Polynomial.C c * Q.map A.subtype := by
  classical
  have hsupp : P.support.Nonempty := Polynomial.nonempty_support_iff.mpr hP
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image P.support (fun i => A.valuation (P.coeff i)) hsupp
  have hc0 : P.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  have hvc : A.valuation (P.coeff i₀) ≠ 0 := (_root_.map_ne_zero A.valuation).mpr hc0

  have hmem : ∀ n, (Polynomial.C (P.coeff i₀)⁻¹ * P).coeff n ∈ A := by
    intro n
    rw [Polynomial.coeff_C_mul]
    by_cases hn : P.coeff n = 0
    · rw [hn, mul_zero]; exact zero_mem A
    · rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
      calc (A.valuation (P.coeff i₀))⁻¹ * A.valuation (P.coeff n)
          ≤ (A.valuation (P.coeff i₀))⁻¹ * A.valuation (P.coeff i₀) :=
            mul_le_mul_right (hmax n (Polynomial.mem_support_iff.mpr hn)) _
        _ = 1 := inv_mul_cancel₀ hvc
  have hlifts : Polynomial.C (P.coeff i₀)⁻¹ * P ∈ Polynomial.lifts A.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hmem n⟩, rfl⟩
  obtain ⟨Q, hQ⟩ := (Polynomial.mem_lifts _).mp hlifts
  refine ⟨P.coeff i₀, Q, hc0, ?_, ?_⟩
  · intro h
    have hQi : ((Q.coeff i₀ : ↥A) : K) = 1 := by
      have := congrArg (fun R : Polynomial K => R.coeff i₀) hQ
      simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at this
      rw [inv_mul_cancel₀ hc0] at this
      exact this
    have hQi' : Q.coeff i₀ = 1 := Subtype.ext hQi
    have h1 : (Q.map (IsLocalRing.residue ↥A)).coeff i₀ = 1 := by
      rw [Polynomial.coeff_map, hQi', map_one]
    rw [h, Polynomial.coeff_zero] at h1
    exact zero_ne_one h1
  · rw [hQ, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc0, Polynomial.C_1, one_mul]

theorem exists_eq_eval₂_mul_unit_inv
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring K)
    (x : L) (hgen : IntermediateField.adjoin K ({x} : Set L) = ⊤)
    (O : ValuationSubring L)
    (hOA : ∀ c : K, algebraMap K L c ∈ O ↔ c ∈ A)
    (hxO : x ∈ O)
    (hunit : ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 → IsUnit (Q.eval₂ (toO A O hOA) ⟨x, hxO⟩))
    (b : ↥O) :
    ∃ (P Q : Polynomial ↥A) (hQ : Q.map (IsLocalRing.residue ↥A) ≠ 0),
      b = P.eval₂ (toO A O hOA) ⟨x, hxO⟩ * ↑((hunit Q hQ).unit⁻¹ : (↥O)ˣ) := by
  classical
  have h1 : (1 : Polynomial ↥A).map (IsLocalRing.residue ↥A) ≠ 0 := by
    rw [Polynomial.map_one]; exact one_ne_zero
  by_cases hb0 : (b : L) = 0
  · refine ⟨0, 1, h1, ?_⟩
    have : b = 0 := Subtype.ext hb0
    rw [this, Polynomial.eval₂_zero, zero_mul]
  have hbL : (b : L) ∈ IntermediateField.adjoin K ({x} : Set L) := by
    rw [hgen]; exact IntermediateField.mem_top
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff _ _).mp hbL
  have hr0 : r ≠ 0 := by
    rintro rfl; apply hb0; rw [hrs, map_zero, zero_div]
  have hs0 : Polynomial.aeval x s ≠ 0 := by
    intro h; apply hb0; rw [hrs, h, div_zero]
  have hs0' : s ≠ 0 := by
    rintro rfl; exact hs0 (map_zero _)
  obtain ⟨c, R₀, hc0, hR₀, hr⟩ := exists_eq_C_mul_map A r hr0
  obtain ⟨d, S₀, hd0, hS₀, hs⟩ := exists_eq_C_mul_map A s hs0'

  set uR : (↥O)ˣ := (hunit R₀ hR₀).unit with huR_def
  set uS : (↥O)ˣ := (hunit S₀ hS₀).unit with huS_def
  have huR : (uR : ↥O) = R₀.eval₂ (toO A O hOA) ⟨x, hxO⟩ := (hunit R₀ hR₀).unit_spec
  have huS : (uS : ↥O) = S₀.eval₂ (toO A O hOA) ⟨x, hxO⟩ := (hunit S₀ hS₀).unit_spec
  have hcoeR : ((R₀.eval₂ (toO A O hOA) ⟨x, hxO⟩ : ↥O) : L) = Polynomial.aeval x (R₀.map A.subtype) :=
    coe_eval₂_toO A O hOA x hxO R₀
  have hcoeS : ((S₀.eval₂ (toO A O hOA) ⟨x, hxO⟩ : ↥O) : L) = Polynomial.aeval x (S₀.map A.subtype) :=
    coe_eval₂_toO A O hOA x hxO S₀
  have haR0 : Polynomial.aeval x (R₀.map A.subtype) ≠ 0 := by
    rw [← hcoeR, ← huR]
    intro h
    exact uR.ne_zero (Subtype.ext h)
  have haS0 : Polynomial.aeval x (S₀.map A.subtype) ≠ 0 := by
    rw [← hcoeS, ← huS]
    intro h
    exact uS.ne_zero (Subtype.ext h)

  have hinvR : (((uR⁻¹ : (↥O)ˣ) : ↥O) : L) = (Polynomial.aeval x (R₀.map A.subtype))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have h := congrArg (fun z : ↥O => (z : L)) uR.mul_inv
    simpa [huR, hcoeR] using h
  have hc' : algebraMap K L c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
  have hd' : algebraMap K L d ≠ 0 := (_root_.map_ne_zero _).mpr hd0

  set w : ↥O := b * S₀.eval₂ (toO A O hOA) ⟨x, hxO⟩ * ↑(uR⁻¹ : (↥O)ˣ) with hw_def
  have hw : (w : L) = algebraMap K L (c / d) := by
    have : (w : L) = (b : L) * Polynomial.aeval x (S₀.map A.subtype) * (Polynomial.aeval x (R₀.map A.subtype))⁻¹ := by
      rw [hw_def]
      push_cast
      rw [hcoeS, hinvR]
    rw [this, hrs, hr, hs, map_div₀]
    simp only [map_mul, Polynomial.aeval_C]
    field_simp
  have hcdA : c / d ∈ A := (hOA _).mp (hw ▸ w.2)
  have hφe : toO A O hOA ⟨c / d, hcdA⟩ = w := Subtype.ext (by rw [coe_toO, hw])
  refine ⟨Polynomial.C (⟨c / d, hcdA⟩ : ↥A) * R₀, S₀, hS₀, ?_⟩
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, hφe, ← huR, ← huS_def, hw_def, ← huS]
  simp only [Units.inv_mul_cancel_right, Units.mul_inv_cancel_right]

end GRG
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL.GRG"

namespace GRG

theorem isUnit_eval₂_toO' {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring K)
    (x : L) (hx : Transcendental K x) (O : ValuationSubring L)
    (hOA : ∀ c : K, algebraMap K L c ∈ O ↔ c ∈ A) (hxO : x ∈ O)
    (hOx : ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval x (Q.map A.subtype) ∈ O ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O)
    (Q : Polynomial ↥A) (hQ : Q.map (IsLocalRing.residue ↥A) ≠ 0) :
    IsUnit (Q.eval₂ (toO A O hOA) ⟨x, hxO⟩) := by
  have hQ0 : Q.map A.subtype ≠ 0 := by
    intro h0
    apply hQ
    have : Q = 0 := by
      apply (Polynomial.map_injective A.subtype Subtype.coe_injective)
      rw [h0, Polynomial.map_zero]
    rw [this, Polynomial.map_zero]
  have hne : Polynomial.aeval x (Q.map A.subtype) ≠ 0 := fun h0 => hQ0 (by
    by_contra hne
    exact hx ⟨Q.map A.subtype, hne, h0⟩)
  obtain ⟨h1, h2⟩ := hOx Q hQ
  have key : Q.eval₂ (toO A O hOA) ⟨x, hxO⟩ = ⟨Polynomial.aeval x (Q.map A.subtype), h1⟩ :=
    Subtype.ext (coe_eval₂_toO A O hOA x hxO Q)
  rw [key]
  exact isUnit_of_inv_mem O _ h1 h2 hne

theorem le_of_generic {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring K)
    (x : L) (hx : Transcendental K x) (hgen : IntermediateField.adjoin K ({x} : Set L) = ⊤)
    (O₁ O₂ : ValuationSubring L)
    (hOA₁ : ∀ c : K, algebraMap K L c ∈ O₁ ↔ c ∈ A) (hOA₂ : ∀ c : K, algebraMap K L c ∈ O₂ ↔ c ∈ A)
    (hx₁ : x ∈ O₁) (hx₂ : x ∈ O₂)
    (hgen₁ : ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval x (Q.map A.subtype) ∈ O₁ ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O₁)
    (hgen₂ : ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval x (Q.map A.subtype) ∈ O₂ ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O₂) :
    O₁ ≤ O₂ := by
  intro b hb
  have hunit₁ := isUnit_eval₂_toO' A x hx O₁ hOA₁ hx₁ hgen₁
  obtain ⟨P, Q, hQ, hPQ⟩ := exists_eq_eval₂_mul_unit_inv A x hgen O₁ hOA₁ hx₁ hunit₁ ⟨b, hb⟩

  set u : (↥O₁)ˣ := (hunit₁ Q hQ).unit with hu
  have huv : ((u : ↥O₁) : L) = Polynomial.aeval x (Q.map A.subtype) := by
    rw [hu, IsUnit.unit_spec, coe_eval₂_toO]
  have hinv : (((u⁻¹ : (↥O₁)ˣ) : ↥O₁) : L) = (Polynomial.aeval x (Q.map A.subtype))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have h := congrArg (fun z : ↥O₁ => (z : L)) u.mul_inv
    have h' : ((u : ↥O₁) : L) * (((u⁻¹ : (↥O₁)ˣ) : ↥O₁) : L) = 1 := by
      simpa only [Units.val_mul, Subring.coe_mul, MulMemClass.coe_mul, OneMemClass.coe_one, Units.val_one] using h
    rwa [huv] at h'
  have hbL : b = Polynomial.aeval x (P.map A.subtype) * (Polynomial.aeval x (Q.map A.subtype))⁻¹ := by
    have h := congrArg (fun z : ↥O₁ => (z : L)) hPQ
    have h' : (b : L) = ((P.eval₂ (toO A O₁ hOA₁) ⟨x, hx₁⟩ : ↥O₁) : L) * (((u⁻¹ : (↥O₁)ˣ) : ↥O₁) : L) := by
      simpa only [Subring.coe_mul, MulMemClass.coe_mul] using h
    rw [coe_eval₂_toO, hinv] at h'
    exact h'
  rw [hbL]
  refine mul_mem ?_ (hgen₂ Q hQ).2

  rw [← coe_eval₂_toO A O₂ hOA₂ x hx₂ P]
  exact (P.eval₂ (toO A O₂ hOA₂) ⟨x, hx₂⟩).2

theorem eq_of_generic {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring K)
    (x : L) (hx : Transcendental K x) (hgen : IntermediateField.adjoin K ({x} : Set L) = ⊤)
    (O₁ O₂ : ValuationSubring L)
    (hOA₁ : ∀ c : K, algebraMap K L c ∈ O₁ ↔ c ∈ A) (hOA₂ : ∀ c : K, algebraMap K L c ∈ O₂ ↔ c ∈ A)
    (hx₁ : x ∈ O₁) (hx₂ : x ∈ O₂)
    (hgen₁ : ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval x (Q.map A.subtype) ∈ O₁ ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O₁)
    (hgen₂ : ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval x (Q.map A.subtype) ∈ O₂ ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O₂) :
    O₁ = O₂ :=
  le_antisymm (le_of_generic A x hx hgen O₁ O₂ hOA₁ hOA₂ hx₁ hx₂ hgen₁ hgen₂)
    (le_of_generic A x hx hgen O₂ O₁ hOA₂ hOA₁ hx₂ hx₁ hgen₂ hgen₁)

end GRG
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL.GRG"

end Ws2GenericUnique
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL.GRG"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace Ws30C40Fold

theorem aeval_map_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (A : ValuationSubring K)
    (x : F) (hxT : Transcendental K x) (Q : Polynomial ↥A) (hQ : Q.map (IsLocalRing.residue ↥A) ≠ 0) :
    Polynomial.aeval x (Q.map A.subtype) ≠ 0 := by
  intro h0
  have hQ0 : Q.map A.subtype ≠ 0 := by
    intro hz; apply hQ
    have : Q = 0 := Polynomial.map_injective A.subtype Subtype.coe_injective (by rw [hz, Polynomial.map_zero])
    rw [this, Polynomial.map_zero]
  exact hQ0 (by by_contra hne; exact hxT ⟨Q.map A.subtype, hne, h0⟩)

theorem mem_iff_mem_of_mem_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F] (A : ValuationSubring K)
    (x : F) (hxT : Transcendental K x) (O₁ O₂ : ValuationSubring F)
    (hOA₁ : ∀ c : K, algebraMap K F c ∈ O₁ ↔ c ∈ A) (hOA₂ : ∀ c : K, algebraMap K F c ∈ O₂ ↔ c ∈ A)
    (hgen₁ : ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval x (Q.map A.subtype) ∈ O₁ ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O₁)
    (hgen₂ : ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval x (Q.map A.subtype) ∈ O₂ ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O₂)
    (e : F) (he : e ∈ IntermediateField.adjoin K ({x} : Set F)) :
    e ∈ O₁ ↔ e ∈ O₂ := by
  classical
  rw [IntermediateField.mem_adjoin_simple_iff] at he
  obtain ⟨r, s, rfl⟩ := he
  by_cases hr : r = 0
  · simp [hr]
  by_cases hs : s = 0
  · simp [hs]
  obtain ⟨c, R₀, hc, hR₀, hrR⟩ := GRG.exists_eq_C_mul_map A r hr
  obtain ⟨d, S₀, hd, hS₀, hsS⟩ := GRG.exists_eq_C_mul_map A s hs
  have crit : ∀ O : ValuationSubring F, (∀ c : K, algebraMap K F c ∈ O ↔ c ∈ A) →
      (∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
        Polynomial.aeval x (Q.map A.subtype) ∈ O ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O) →
      (Polynomial.aeval x r / Polynomial.aeval x s ∈ O ↔ c / d ∈ A) := by
    intro O hOA hgen
    obtain ⟨hu, hu'⟩ := hgen R₀ hR₀
    obtain ⟨hv, hv'⟩ := hgen S₀ hS₀
    have hu0 := aeval_map_ne_zero A x hxT R₀ hR₀
    have hv0 := aeval_map_ne_zero A x hxT S₀ hS₀
    have hd' : algebraMap K F d ≠ 0 := (map_ne_zero _).mpr hd
    have he : Polynomial.aeval x r / Polynomial.aeval x s =
        algebraMap K F (c / d) * (Polynomial.aeval x (R₀.map A.subtype) * (Polynomial.aeval x (S₀.map A.subtype))⁻¹) := by
      rw [hrR, hsS, map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, map_div₀]
      field_simp
    rw [he, ← hOA (c / d)]
    constructor
    · intro h
      have heq : algebraMap K F (c / d) =
          (algebraMap K F (c / d) * (Polynomial.aeval x (R₀.map A.subtype) * (Polynomial.aeval x (S₀.map A.subtype))⁻¹)) *
            (Polynomial.aeval x (S₀.map A.subtype) * (Polynomial.aeval x (R₀.map A.subtype))⁻¹) := by
        field_simp
      rw [heq]
      exact mul_mem h (mul_mem hv hu')
    · intro h
      exact mul_mem h (mul_mem hu hv')
  exact (crit O₁ hOA₁ hgen₁).trans (crit O₂ hOA₂ hgen₂).symm

theorem transcendental_of_algHom_apply {K S L : Type*} [Field K] [Field S] [Field L] [Algebra K S] [Algebra K L]
    (f : S →ₐ[K] L) (r : S) (hs : Transcendental K (f r)) : Transcendental K r := by
  rintro ⟨P, hP0, hP⟩
  exact hs ⟨P, hP0, by rw [Polynomial.aeval_algHom_apply, hP, map_zero]⟩

theorem transcendental_qExpand_jqModC (κ : Type) [Field κ] (p : ℕ) [NeZero p] :
    Transcendental κ (qExpand κ p (jqModC κ)) := by
  rintro ⟨P, hP0, hP⟩
  apply ModularCurve.transcendental_jqModC κ
  refine ⟨P, hP0, qExpand_injective p ?_⟩
  rw [map_zero]
  have hc : (qExpand κ p).comp (algebraMap κ (LaurentSeries κ)) = algebraMap κ (LaurentSeries κ) := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
  have := Polynomial.hom_eval₂ P (algebraMap κ (LaurentSeries κ)) (qExpand κ p) (jqModC κ)
  rw [hc] at this
  rw [Polynomial.aeval_def] at hP ⊢
  rw [this, hP]

theorem transcendental_x (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (x : ↥(xHFunctionFieldBar M H))
    (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) : Transcendental (AlgebraicClosure ℚ) x := by
  apply transcendental_of_algHom_apply (IntermediateField.val _) x
  show Transcendental (AlgebraicClosure ℚ) ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))
  rw [hx]; exact ModularCurve.transcendental_jqModC _

theorem exists_alpha_eq (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ∃ x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) ∧ α x' = x := by
  have hj' : jqModC ℚ ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) := by
    show jqModC ℚ ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))
    exact qExpFunctionFieldC_mono ℚ le_top hj
  have hmem : jqModC (AlgebraicClosure ℚ) ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) := by
    have h := coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) hj'
    have he : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := coeffMap_jqModC _
    rw [he] at h
    exact h
  exact ⟨⟨jqModC (AlgebraicClosure ℚ), hmem⟩, rfl, Subtype.ext (by rw [hα_coe, hx])⟩

theorem x_mem₁ (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ∃ h : x ∈ Rpd.R₁.integers, ((Rpd.R₁.residue ⟨x, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
  have hmem : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar M H := by
    rw [coeffMap_jqModC, ← hx]; exact x.2
  obtain ⟨h, hres⟩ := Rpd.residue₁_coeffMap (jqModC ↥A) hmem
  have hxe : (⟨coeffMap A.subtype (jqModC ↥A), hmem⟩ : ↥(xHFunctionFieldBar M H)) = x :=
    Subtype.ext (by show coeffMap A.subtype (jqModC ↥A) = (x : LaurentSeries (AlgebraicClosure ℚ)); rw [coeffMap_jqModC, hx])
  subst hxe
  exact ⟨h, by rw [hres, coeffMap_jqModC]⟩

theorem alpha_isIntegral (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) :
    α.IsIntegral := by
  obtain ⟨αH, hint, hcoe⟩ := ModularCurve.exists_algHom_xHFunctionFieldBar_div_infSubgroup_isIntegral_and_coe_eq p M H hpM
  have : α = αH := AlgHom.ext fun u => Subtype.ext (by rw [hα_coe, hcoe])
  rw [this]
  exact hint

end Ws30C40Fold
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL.GRG"

open Ws30C40Fold in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :

    Rpd.R₁.integers ≠ Rpd.R₂.integers ∧

    (∀ O : ValuationSubring ↥(xHFunctionFieldBar M H),
      (∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c ∈ O ↔ c ∈ A) →
      (∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
        Polynomial.aeval x (Q.map A.subtype) ∈ O ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O) →
      O = Rpd.R₁.integers ∨ O = Rpd.R₂.integers) ∧

    (∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      (Polynomial.aeval x (Q.map A.subtype) ∈ Rpd.R₁.integers ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ Rpd.R₁.integers) ∧
      (Polynomial.aeval x (Q.map A.subtype) ∈ Rpd.R₂.integers ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ Rpd.R₂.integers)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨hgen₁, hsep₁⟩ :=
    ModularCurve.JHPlaceSpecialization.ProlongationDatum.integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one
      p M H hpM hpM2 hHp A hA θ Psp Rpd α hα_coe x hx
  obtain ⟨hgen₂, hinsep₂⟩ :=
    ModularCurve.XHDRModelAtP.integers_snd_isGeneric_and_forall_exists_valuation_alpha_sub_pow_lt_one_of_residue_eq_qExpFrobeniusModL
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ hwgen Psp Rpd α hα_coe hres₂α x hx

  obtain ⟨x', hx', hαx'⟩ := exists_alpha_eq p M H hpM hj α hα_coe x hx
  have hα : α.IsIntegral := alpha_isIntegral p M H hpM α hα_coe

  have hne : Rpd.R₁.integers ≠ Rpd.R₂.integers := fun h =>
    (ModularCurve.JHPlaceSpecialization.ProlongationDatum.not_integers_le_integers_and_not_integers_le_integers
      p M H hpM hpM2 hHp A hA θ α hα_coe hα Psp Rpd hres₂α x' hx').1 (le_of_eq h)
  refine ⟨hne, ?_, fun Q hQ => ⟨hgen₁.2 Q hQ, hgen₂.2 Q hQ⟩⟩

  intro O hc hQ

  obtain ⟨h₁x, hres₁x⟩ := x_mem₁ p M H hpM A θ Psp Rpd x hx
  have h₂x : x ∈ Rpd.R₂.integers := by
    have := (hgen₂.2 Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
    rwa [Polynomial.map_X, Polynomial.aeval_X] at this
  have h₁' : α x' ∈ Rpd.R₁.integers := by rw [hαx']; exact h₁x
  have h₂' : α x' ∈ Rpd.R₂.integers := by rw [hαx']; exact h₂x
  have hres₂x : ((Rpd.R₂.residue ⟨x, h₂x⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = qExpand (ResidueField ↥A) p (jqModC (ResidueField ↥A)) := by
    have e := hres₂α x' h₁' h₂'
    have e2 : (⟨α x', h₂'⟩ : ↥Rpd.R₂.integers) = ⟨x, h₂x⟩ := Subtype.ext hαx'
    have e1 : (⟨α x', h₁'⟩ : ↥Rpd.R₁.integers) = ⟨x, h₁x⟩ := Subtype.ext hαx'
    rw [e2, e1] at e
    rw [e, coe_qExpFrobeniusModL, hres₁x]

  have hxT : Transcendental (AlgebraicClosure ℚ) x := transcendental_x M H x hx
  have htr₁ : Transcendental (ResidueField ↥A) (Rpd.R₁.residue ⟨x, h₁x⟩) := by
    apply transcendental_of_algHom_apply (IntermediateField.val _)
    show Transcendental (ResidueField ↥A) ((Rpd.R₁.residue ⟨x, h₁x⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A))
    rw [hres₁x]; exact ModularCurve.transcendental_jqModC _
  have htr₂ : Transcendental (ResidueField ↥A) (Rpd.R₂.residue ⟨x, h₂x⟩) := by
    apply transcendental_of_algHom_apply (IntermediateField.val _)
    show Transcendental (ResidueField ↥A) ((Rpd.R₂.residue ⟨x, h₂x⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A))
    rw [hres₂x]; exact transcendental_qExpand_jqModC _ p

  obtain ⟨hcurve, hess⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H
  haveI := hcurve
  haveI := hess
  obtain ⟨t, ht, hFD, -⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))
  haveI := hFD
  haveI : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(xHFunctionFieldBar M H))) ↥(xHFunctionFieldBar M H) :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental t hxT

  letI instField : ∀ _ : Fin 2, Field (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := fun _ => inferInstance
  letI instAlg : ∀ _ : Fin 2, Algebra (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := fun _ => inferInstance
  let Rfam : Fin 2 → RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := ![Rpd.R₁, Rpd.R₂]
  have hRinj : Function.Injective fun i => (Rfam i).integers := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hne
    · exact absurd hij.symm hne
    · rfl
  have hf : ∀ i, x ∈ (Rfam i).integers := fun i => by fin_cases i <;> assumption
  have htr : ∀ i, Transcendental (ResidueField ↥A) ((Rfam i).residue ⟨x, hf i⟩) := fun i => by
    fin_cases i
    · exact htr₁
    · exact htr₂
  have heq : ∑ i, Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({(Rfam i).residue ⟨x, hf i⟩} : Set (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) =
      Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(xHFunctionFieldBar M H))) ↥(xHFunctionFieldBar M H) := by
    have hh := ModularCurve.JHPlaceSpecialization.ProlongationDatum.finrank_adjoin_residue_add_finrank_adjoin_residue_eq_finrank_adjoin
      p M H hpM hpM2 hHp A hA θ α hα_coe hα Psp Rpd hres₂α x' hx' h₁' h₂'
    rw [Fin.sum_univ_two]
    have e2 : (⟨α x', h₂'⟩ : ↥Rpd.R₂.integers) = ⟨x, h₂x⟩ := Subtype.ext hαx'
    have e1 : (⟨α x', h₁'⟩ : ↥Rpd.R₁.integers) = ⟨x, h₁x⟩ := Subtype.ext hαx'
    rw [e1, e2, hαx'] at hh
    exact hh
  have hV : ∀ e : ↥(xHFunctionFieldBar M H), e ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) {x} → (e ∈ O ↔ e ∈ (Rfam 0).integers) := fun e he =>
    mem_iff_mem_of_mem_adjoin A x hxT O Rpd.R₁.integers hc Rpd.R₁.algebraMap_mem_iff hQ hgen₁.2 e he
  obtain ⟨j, hj'⟩ := AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq
    A (fun _ : Fin 2 => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) Rfam hRinj x hf htr heq 0 O hV
  fin_cases j
  · exact Or.inl hj'
  · exact Or.inr hj'

#print axioms solution

end S_ModularCurve_XHDRModelAtP_integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL (solution)
