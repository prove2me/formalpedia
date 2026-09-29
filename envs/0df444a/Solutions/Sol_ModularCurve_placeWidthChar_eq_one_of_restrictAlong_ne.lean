-- Prove2me | solution 1 for ModularCurve.placeWidthChar_eq_one_of_restrictAlong_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0b9a0a76-55c3-5a58-a536-1e56b4de1683

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_WeierstrassCurve_card_stabilizer_variableChange_eq_two_mul_jWidth
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq
import Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_veluQuotient_forall_apply_eq_of_comp_self_add_smul_eq_smul
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_finite_rationalHomSet_units
import Theorems.Thm_ModularCurve_exists_smul_one_add_smul_eq_diagonal_mul_of_mem_Gamma0
import Theorems.Thm_WeierstrassCurve_exists_addOrderOf_eq_prime_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_Affine_variableChange_eq_of_forall_equivOfVariableChangeEq_eq
import Theorems.Thm_WeierstrassCurve_fullKernelHom_eq_veluPointMap2_comp_of_stage_last
import Theorems.Thm_WeierstrassCurve_exists_fullKernelHom
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_veluQuotient2_forall_apply_eq_of_comp_self_add_two_smul_eq_smul
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_placeWidthChar_eq_one_of_restrictAlong_ne
p2m_attr_erase "instance" "ModularCurve.ModuliTestDatum.isElliptic_reduced ModularCurve.ModuliTestDatum.isElliptic_curve ModularCurve.ModuliTestDatum.isElliptic_generic ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.ComapPlace.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_emb ModularCurve.ModuliTestDatum.restrictLevel_res ModularCurve.ModuliTestDatum.mk.injEq ModularCurve.ModuliTestDatum.restrictLevel_W ModularCurve.ModuliTestDatum.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_curve ModularCurve.ModuliTestDatum.resEquiv_apply ModularCurve.ModuliTestDatum.restrictLevel_gen ModularCurve.ModuliTestDatum.mk.sizeOf_spec ModularCurve.coe_jqNFull ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero"
p2m_attr_erase "simp" "ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ"
p2m_attr_erase "simp" "ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply"
p2m_attr_erase "simp" "ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.pointAddEquivOfEq_refl"
set_option Elab.async false
set_option autoImplicit false

namespace CyclicLevelOrbit

noncomputable section

section PointTransport

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

section Transport

variable {k : Type*} [Field k]

private def ptCoords {W : WeierstrassCurve.Affine k} : W.Point → Option (k × k)
  | .zero => none
  | .some x y _ => some (x, y)

private theorem eq_of_ptCoords_eq {W : WeierstrassCurve.Affine k} :
    ∀ {P Q : W.Point}, ptCoords P = ptCoords Q → P = Q
  | .zero, .zero, _ => rfl
  | .zero, .some _ _ _, e => by simp [ptCoords] at e
  | .some _ _ _, .zero, e => by simp [ptCoords] at e
  | .some x y h, .some x' y' h', e => by
      simp only [ptCoords, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rfl

private theorem heq_iff_ptCoords_eq {W V : WeierstrassCurve k} (h : W = V)
    (P : W.toAffine.Point) (Q : V.toAffine.Point) : HEq P Q ↔ ptCoords P = ptCoords Q := by
  subst h
  exact ⟨fun e => (eq_of_heq e) ▸ rfl, fun e => heq_of_eq (eq_of_ptCoords_eq e)⟩

private def invCoords (C : VariableChange k) : Option (k × k) → Option (k × k)
  | none => none
  | some xy => some (vcXInv C xy.1, vcYInv C xy.1 xy.2)

private theorem ptCoords_vcInvFun (C : VariableChange k) (W : WeierstrassCurve.Affine k) (P : W.Point) :
    ptCoords (Point.vcInvFun C W P) = invCoords C (ptCoords P) := by
  cases P <;> rfl

private theorem invCoords_one : ∀ c : Option (k × k), invCoords (1 : VariableChange k) c = c
  | none => rfl
  | some (x, y) => by
      simp [invCoords, vcXInv, vcYInv, VariableChange.one_def]

private theorem invCoords_mul (C C' : VariableChange k) :
    ∀ c : Option (k × k), invCoords (C * C') c = invCoords C (invCoords C' c)
  | none => rfl
  | some (x, y) => by
      have hu : (C.u : k) ≠ 0 := C.u.ne_zero
      have hu' : (C'.u : k) ≠ 0 := C'.u.ne_zero
      simp only [invCoords, vcXInv, vcYInv, VariableChange.mul_def, mul_inv, Units.val_mul,
        Units.val_inv_eq_inv_val, Option.some.injEq, Prod.mk.injEq]
      constructor
      · field_simp
        ring
      · field_simp
        ring

variable [DecidableEq k]

private def ptCastOfEq {W V : WeierstrassCurve k} (h : W = V) : W.toAffine.Point ≃+ V.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

private theorem ptCoords_ptCastOfEq {W V : WeierstrassCurve k} (h : W = V) (P : W.toAffine.Point) :
    ptCoords (ptCastOfEq h P) = ptCoords P := by
  subst h
  rfl

variable (E : WeierstrassCurve k)

private noncomputable def stabAut (γ : MulAction.stabilizer (VariableChange k) E) :
    E.toAffine.Point ≃+ E.toAffine.Point :=
  (AddEquiv.mk' (Point.variableChangeEquiv (γ : VariableChange k) E.toAffine).symm
      (Point.vcInvFun_add (γ : VariableChange k) E.toAffine)).trans
    (ptCastOfEq (MulAction.mem_stabilizer_iff.mp γ.2))

private theorem ptCoords_stabAut (γ : MulAction.stabilizer (VariableChange k) E) (P : E.toAffine.Point) :
    ptCoords (stabAut E γ P) = invCoords (γ : VariableChange k) (ptCoords P) := by
  have h1 : stabAut E γ P =
      ptCastOfEq (MulAction.mem_stabilizer_iff.mp γ.2) (Point.vcInvFun (γ : VariableChange k) E.toAffine P) :=
    rfl
  rw [h1, ptCoords_ptCastOfEq, ptCoords_vcInvFun]

private theorem heq_vcInvFun_iff (γ : MulAction.stabilizer (VariableChange k) E) (T T' : E.toAffine.Point) :
    HEq (Point.vcInvFun (γ : VariableChange k) E.toAffine T) T' ↔ stabAut E γ T = T' := by
  refine (heq_iff_ptCoords_eq (MulAction.mem_stabilizer_iff.mp γ.2) _ T').trans ?_
  rw [ptCoords_vcInvFun, ← ptCoords_stabAut]
  exact ⟨fun e => eq_of_ptCoords_eq e, fun e => e ▸ rfl⟩

private theorem stabAut_one (P : E.toAffine.Point) : stabAut E 1 P = P :=
  eq_of_ptCoords_eq (by rw [ptCoords_stabAut]; exact invCoords_one _)

private theorem stabAut_mul (γ γ' : MulAction.stabilizer (VariableChange k) E) (P : E.toAffine.Point) :
    stabAut E (γ * γ') P = stabAut E γ (stabAut E γ' P) :=
  eq_of_ptCoords_eq (by simp only [ptCoords_stabAut]; exact invCoords_mul _ _ _)

private noncomputable scoped instance stabActAddSubgroup :
    MulAction (MulAction.stabilizer (VariableChange k) E) (AddSubgroup E.toAffine.Point) where
  smul γ K := K.map (stabAut E γ).toAddMonoidHom
  one_smul K := by
    show K.map (stabAut E 1).toAddMonoidHom = K
    have h : (stabAut E 1).toAddMonoidHom = AddMonoidHom.id _ := AddMonoidHom.ext (stabAut_one E)
    rw [h, AddSubgroup.map_id]
  mul_smul γ γ' K := by
    show K.map (stabAut E (γ * γ')).toAddMonoidHom =
      (K.map (stabAut E γ').toAddMonoidHom).map (stabAut E γ).toAddMonoidHom
    have h : (stabAut E (γ * γ')).toAddMonoidHom = (stabAut E γ).toAddMonoidHom.comp (stabAut E γ').toAddMonoidHom :=
      AddMonoidHom.ext (stabAut_mul E γ γ')
    rw [h, AddSubgroup.map_map]

private theorem stabSmul_def (γ : MulAction.stabilizer (VariableChange k) E) (K : AddSubgroup E.toAffine.Point) :
    γ • K = K.map (stabAut E γ).toAddMonoidHom :=
  rfl

private theorem natCard_stabSmul (γ : MulAction.stabilizer (VariableChange k) E) (K : AddSubgroup E.toAffine.Point) :
    Nat.card ↥(γ • K) = Nat.card K := by
  rw [stabSmul_def]
  exact AddSubgroup.card_map_of_injective (stabAut E γ).injective

private theorem stabSmul_eq_iff (γ : MulAction.stabilizer (VariableChange k) E)
    (K K' : AddSubgroup E.toAffine.Point) [Finite K'] (hcard : Nat.card K = Nat.card K') :
    γ • K = K' ↔ ∀ T ∈ K, ∃ T' ∈ K', HEq (Point.vcInvFun (γ : VariableChange k) E.toAffine T) T' := by
  constructor
  · rintro rfl T hT
    refine ⟨stabAut E γ T, ?_, (heq_vcInvFun_iff E γ T _).mpr rfl⟩
    rw [stabSmul_def]
    exact AddSubgroup.mem_map_of_mem _ hT
  · intro h
    have hle : γ • K ≤ K' := by
      intro x hx
      rw [stabSmul_def] at hx
      obtain ⟨T, hT, rfl⟩ := AddSubgroup.mem_map.mp hx
      obtain ⟨T', hT', hh⟩ := h T hT
      have e : stabAut E γ T = T' := (heq_vcInvFun_iff E γ T T').mp hh
      change stabAut E γ T ∈ K'
      rw [e]
      exact hT'
    exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [natCard_stabSmul, hcard])

private theorem isAddCyclic_stabSmul (γ : MulAction.stabilizer (VariableChange k) E)
    (K : AddSubgroup E.toAffine.Point) [IsAddCyclic K] : IsAddCyclic ↥(γ • K) := by
  rw [stabSmul_def]
  exact isAddCyclic_of_surjective _ (AddMonoidHom.addSubgroupMap_surjective (stabAut E γ).toAddMonoidHom K)

end Transport

section TransportMore

variable {k : Type*} [Field k]

private theorem exists_eq_some_of_ptCoords_eq {W : WeierstrassCurve.Affine k} :
    ∀ {P : W.Point} {a b : k}, ptCoords P = some (a, b) → ∃ h, P = .some a b h
  | .zero, _, _, e => by simp [ptCoords] at e
  | .some x y h, a, b, e => by
      simp only [ptCoords, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨h, rfl⟩

private def fwdCoords (C : VariableChange k) : Option (k × k) → Option (k × k)
  | none => none
  | some xy => some (vcX C xy.1, vcY C xy.1 xy.2)

private theorem invCoords_inv (C : VariableChange k) : ∀ c : Option (k × k), invCoords C⁻¹ c = fwdCoords C c
  | none => rfl
  | some (x, y) => by
      have hu : (C.u : k) ≠ 0 := C.u.ne_zero
      simp only [invCoords, fwdCoords, vcX, vcY, vcXInv, vcYInv, VariableChange.inv_def, inv_inv,
        Units.val_inv_eq_inv_val, Option.some.injEq, Prod.mk.injEq]
      constructor
      · field_simp
        ring
      · field_simp
        ring

private theorem fwdCoords_invCoords (C : VariableChange k) : ∀ c : Option (k × k), fwdCoords C (invCoords C c) = c
  | none => rfl
  | some (x, y) => by
      simp [invCoords, fwdCoords]

variable [DecidableEq k]

private theorem ptCoords_equivOfVariableChangeEq {C : VariableChange k} {W V : WeierstrassCurve k}
    (h : C • W = V) (P : V.toAffine.Point) :
    ptCoords (Point.equivOfVariableChangeEq h P) = fwdCoords C (ptCoords P) := by
  subst h
  cases P <;> rfl

variable (E : WeierstrassCurve k)

private theorem equivOfVariableChangeEq_stabAut (γ : MulAction.stabilizer (VariableChange k) E)
    (P : E.toAffine.Point) :
    Point.equivOfVariableChangeEq (MulAction.mem_stabilizer_iff.mp γ.2) (stabAut E γ P) = P :=
  eq_of_ptCoords_eq (by rw [ptCoords_equivOfVariableChangeEq, ptCoords_stabAut, fwdCoords_invCoords])

private noncomputable def stabEnd : MulAction.stabilizer (VariableChange k) E →* AddMonoid.End E.toAffine.Point where
  toFun γ := (stabAut E γ : E.toAffine.Point →+ E.toAffine.Point)
  map_one' := AddMonoidHom.ext (stabAut_one E)
  map_mul' γ γ' := AddMonoidHom.ext (stabAut_mul E γ γ')

private theorem stabEnd_apply (γ : MulAction.stabilizer (VariableChange k) E) (P : E.toAffine.Point) :
    stabEnd E γ P = stabAut E γ P :=
  rfl

end TransportMore

section TransportTwo

variable {k : Type*} [Field k]

private theorem invCoords_fwdCoords (C : VariableChange k) : ∀ c : Option (k × k), invCoords C (fwdCoords C c) = c
  | none => rfl
  | some (x, y) => by
      simp [invCoords, fwdCoords]

private theorem ptCoords_eq_some_coordsOrZero {W : WeierstrassCurve.Affine k} :
    ∀ {P : W.Point}, P ≠ 0 → ptCoords P = some P.coordsOrZero
  | .zero, h => absurd rfl h
  | .some _ _ _, _ => rfl

variable [DecidableEq k]

private theorem fullKernel_seam (h2 : (2 : k) ≠ 0) {E₀ V W : WeierstrassCurve k} (hV : V = E₀)
    (ρ : E₀.toAffine.Point →+ V.toAffine.Point) (hρc : ∀ P, ptCoords (ρ P) = ptCoords P)
    {x₁ y₁ : k} (h₁ : V.toAffine.Nonsingular x₁ y₁) (hgy₁ : V.veluGy x₁ y₁ = 0)
    (hΔ₁ : (V.veluQuotient2 x₁ y₁).Δ ≠ 0) (E : VariableChange k) (hE : E • W = V.veluQuotient2 x₁ y₁)
    (φ : E₀.toAffine.Point →+ W.toAffine.Point)
    (hφ : ∀ P, φ P = Point.equivOfVariableChangeEq hE (veluPointMap2 h2 h₁.1 hgy₁ hΔ₁ (ρ P)))
    (Q : E₀.toAffine.Point) (hρQ : ρ Q = .some x₁ y₁ h₁) :
    ∃ (h₁' : E₀.toAffine.Nonsingular x₁ y₁) (hgy' : E₀.veluGy x₁ y₁ = 0) (hΔ' : (E₀.veluQuotient2 x₁ y₁).Δ ≠ 0)
      (hE' : E • W = E₀.veluQuotient2 x₁ y₁), Q = .some x₁ y₁ h₁' ∧
        ∀ P, φ P = Point.equivOfVariableChangeEq hE' (veluPointMap2 h2 h₁'.1 hgy' hΔ' P) := by
  subst hV
  have hρid : ∀ P, ρ P = P := fun P => eq_of_ptCoords_eq (hρc P)
  refine ⟨h₁, hgy₁, hΔ₁, hE, by rw [← hρQ, hρid], fun P => ?_⟩
  have h := hφ P
  rwa [hρid P] at h

end TransportTwo

end PointTransport

section Absorption

open WeierstrassCurve WeierstrassCurve.Affine

section RootOfUnity

open Polynomial

variable {A : Type*} [Ring A]

private theorem aeval_quad (β : A) (t n : ℤ) :
    aeval β (X ^ 2 - C t * X + C n : ℤ[X]) = β * β - (t : A) * β + (n : A) := by
  simp [sq]

private theorem quad_monic (t n : ℤ) : (X ^ 2 - C t * X + C n : ℤ[X]).Monic := by
  have e : (X ^ 2 - C t * X + C n : ℤ[X]) = X ^ 2 + (C (-t) * X + C n) := by
    simp only [map_neg, neg_mul]
    ring
  rw [e]
  refine (monic_X_pow 2).add_of_left (degree_linear_le.trans_lt ?_)
  rw [degree_X_pow]
  exact WithBot.coe_lt_coe.mpr (by norm_num)

private theorem quad_natDegree (t n : ℤ) : (X ^ 2 - C t * X + C n : ℤ[X]).natDegree = 2 := by
  refine le_antisymm (by compute_degree) (le_natDegree_of_ne_zero ?_)
  have h : (X ^ 2 - C t * X + C n : ℤ[X]).coeff 2 = 1 := by
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
    norm_num
  rw [h]
  exact one_ne_zero

private theorem norm_eq_one_and_trace_of_pow_eq_one (β : A) {e : ℕ} (he : e ≠ 0) (hβe : β ^ e = 1) (t n : ℤ)
    (hrel : β * β - (t : A) * β + (n : A) = 0)
    (htf : ∀ c : ℤ, (c : A) = 0 → c = 0)
    (hdom : ∀ a b : ℤ, (β - a) * (β - b) = 0 → β = a ∨ β = b)
    (h1 : β ≠ 1) (hm1 : β ≠ -1) :
    n = 1 ∧ (t = 0 ∨ t = 1 ∨ t = -1) := by
  set Pq : ℤ[X] := X ^ 2 - C t * X + C n with hPq
  have hPqβ : aeval β Pq = 0 := by rw [hPq, aeval_quad]; exact hrel

  have hint : ∀ m : ℤ, β ≠ (m : A) := by
    intro m hm
    have hme : ((m ^ e - 1 : ℤ) : A) = 0 := by
      rw [Int.cast_sub, Int.cast_pow, ← hm, hβe, Int.cast_one, sub_self]
    have hu : IsUnit m := IsUnit.of_pow_eq_one (sub_eq_zero.mp (htf _ hme)) he
    rcases Int.isUnit_iff.mp hu with rfl | rfl
    · exact h1 (by rw [hm, Int.cast_one])
    · exact hm1 (by rw [hm, Int.cast_neg, Int.cast_one])

  have hroot : ∀ a : ℤ, a ^ 2 - t * a + n ≠ 0 := by
    intro a ha
    have hfac : (X - C a) * (X - C (t - a)) = Pq := by
      rw [hPq, show n = a * (t - a) by linear_combination ha, map_mul, map_sub]
      ring
    have h0 : (β - a) * (β - (t - a : ℤ)) = 0 := by
      have h := congrArg (aeval β) hfac
      rw [hPqβ, map_mul] at h
      simpa using h
    rcases hdom a (t - a) h0 with h | h
    · exact hint a h
    · exact hint (t - a) h

  have hmonic : Pq.Monic := quad_monic t n
  have hdvd : Pq ∣ X ^ e - 1 := by
    have hne1 : Pq ≠ 1 := by
      intro h
      have h2 := quad_natDegree t n
      rw [← hPq, h, natDegree_one] at h2
      exact absurd h2 (by norm_num)
    have hrdeg : ((X ^ e - 1) %ₘ Pq).natDegree ≤ 1 := by
      have h := natDegree_modByMonic_lt (X ^ e - 1 : ℤ[X]) hmonic hne1
      rw [quad_natDegree] at h
      omega
    set r : ℤ[X] := (X ^ e - 1) %ₘ Pq with hr
    have hr01 : r = C (r.coeff 1) * X + C (r.coeff 0) := eq_X_add_C_of_natDegree_le_one hrdeg
    have hrβ : (r.coeff 1 : A) * β + (r.coeff 0 : A) = 0 := by
      have h := congrArg (aeval β) (modByMonic_add_div (X ^ e - 1 : ℤ[X]) Pq)
      rw [map_add, map_mul, hPqβ, zero_mul, add_zero, ← hr, hr01] at h
      simpa [hβe] using h
    by_cases h1c : r.coeff 1 = 0
    · have h0c : r.coeff 0 = 0 := by
        apply htf
        simpa [h1c] using hrβ
      have hr0 : r = 0 := by
        rw [hr01, h1c, h0c]
        simp
      exact (modByMonic_eq_zero_iff_dvd hmonic).mp hr0
    · exfalso

      have hZ : r.coeff 0 ^ 2 + t * r.coeff 0 * r.coeff 1 + n * r.coeff 1 ^ 2 = 0 := by
        apply htf
        have hid : C (r.coeff 1 ^ 2) * Pq = (C (r.coeff 1) * X + C (r.coeff 0)) *
            (C (r.coeff 1) * X - C (r.coeff 0) - C (t * r.coeff 1)) +
              C (r.coeff 0 ^ 2 + t * r.coeff 0 * r.coeff 1 + n * r.coeff 1 ^ 2) := by
          rw [hPq]
          simp only [map_pow, map_mul, map_add]
          ring
        have h := congrArg (aeval β) hid
        rw [map_mul, hPqβ, mul_zero, map_add, map_mul] at h
        have hlin : aeval β (C (r.coeff 1) * X + C (r.coeff 0)) = 0 := by simpa using hrβ
        rw [hlin, zero_mul, zero_add] at h
        simpa using h.symm
      have hr1Q : (r.coeff 1 : ℚ) ≠ 0 := by exact_mod_cast h1c
      have hrootQ : aeval (-(r.coeff 0 : ℚ) / r.coeff 1) Pq = 0 := by
        rw [hPq, aeval_quad]
        field_simp
        have hZQ : ((r.coeff 0 ^ 2 + t * r.coeff 0 * r.coeff 1 + n * r.coeff 1 ^ 2 : ℤ) : ℚ) = 0 := by
          rw [hZ, Int.cast_zero]
        push_cast at hZQ
        linear_combination hZQ
      obtain ⟨m, hm⟩ := isInteger_of_is_root_of_monic hmonic hrootQ
      have hmQ : (m : ℚ) = -(r.coeff 0 : ℚ) / r.coeff 1 := by simpa using hm
      apply hroot m
      have h := hrootQ
      rw [← hmQ, hPq, aeval_quad] at h
      rw [sq]
      exact_mod_cast h

  obtain ⟨qq, hqq⟩ := hdvd
  have hdeg : Pq.degree ≠ 0 := by
    rw [degree_eq_natDegree hmonic.ne_zero, hPq, quad_natDegree]
    exact_mod_cast (by norm_num : (2 : ℕ) ≠ 0)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ Pq hdeg
  have hzq : z * z - (t : ℂ) * z + (n : ℂ) = 0 := by rw [← aeval_quad]; exact hz
  have hze : z ^ e = 1 := by
    have h := congrArg (aeval z) hqq
    rw [map_mul, hz, zero_mul, map_sub, map_pow, aeval_X, map_one] at h
    exact sub_eq_zero.mp h
  have hnorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hze he
  set w : ℂ := (starRingEnd ℂ) z with hw
  have hwq : w * w - (t : ℂ) * w + (n : ℂ) = 0 := by
    have h := congrArg (starRingEnd ℂ) hzq
    simpa [hw] using h

  have hsq : z.re * z.re + z.im * z.im = 1 := by
    have h : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
    rw [Complex.normSq_apply] at h
    exact h
  have hre1 : z.re ≠ 1 := by
    intro h
    have him : z.im = 0 := by rw [h] at hsq; nlinarith
    have hz1 : z = 1 := Complex.ext (by simp [h]) (by simp [him])
    rw [hz1] at hzq
    apply hroot 1
    exact_mod_cast hzq
  have hrem1 : z.re ≠ -1 := by
    intro h
    have him : z.im = 0 := by rw [h] at hsq; nlinarith
    have hz1 : z = -1 := Complex.ext (by simp [h]) (by simp [him])
    rw [hz1] at hzq
    apply hroot (-1)
    have h' : ((1 + t + n : ℤ) : ℂ) = 0 := by push_cast; linear_combination hzq
    have h'' : (1 + t + n : ℤ) = 0 := by exact_mod_cast h'
    linear_combination h''
  have hzw : z ≠ w := by
    intro h
    have him : z.im = 0 := Complex.conj_eq_iff_im.mp (by rw [← hw]; exact h.symm)
    rw [him, mul_zero, add_zero] at hsq
    have h1 : (z.re - 1) * (z.re + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp h1 with h1 | h1
    · exact hre1 (by linear_combination h1)
    · exact hrem1 (by linear_combination h1)

  have hsum : z + w = t := by
    have h : (z - w) * (z + w - t) = 0 := by linear_combination hzq - hwq
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hzw
    · exact sub_eq_zero.mp h
  have hprod : z * w = n := by linear_combination z * hsum - hzq
  have hn1 : n = 1 := by
    have h : (n : ℂ) = 1 := by
      rw [← hprod, hw, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    exact_mod_cast h
  have ht2 : (t : ℝ) = 2 * z.re := by
    have h : (t : ℂ) = ((2 * z.re : ℝ) : ℂ) := by rw [← Complex.add_conj, ← hw, hsum]
    exact_mod_cast h
  have hlt : z.re < 1 ∧ -1 < z.re := by
    have h := abs_le.mp (hnorm ▸ Complex.abs_re_le_norm z)
    exact ⟨lt_of_le_of_ne h.2 hre1, lt_of_le_of_ne' h.1 hrem1⟩
  have ht1 : (t : ℝ) < 2 := by linarith [hlt.1]
  have ht1' : (-2 : ℝ) < t := by linarith [hlt.2]
  have ht3 : t < 2 := by exact_mod_cast ht1
  have ht4 : -2 < t := by exact_mod_cast ht1'
  exact ⟨hn1, by omega⟩

end RootOfUnity

section Arithmetic

private theorem exists_norm_eq_and_dvd (s : ℕ) (hs0 : s ≠ 0) (t l : ℤ) (ht : t = 0 ∨ t = 1 ∨ t = -1)
    (hdiv : (s : ℤ) ∣ l ^ 2 - t * l + 1) :
    ∃ x y : ℤ, x ^ 2 + t * x * y + y ^ 2 = s ∧ (s : ℤ) ∣ x + y * l := by
  obtain ⟨b, hb⟩ := hdiv
  let U : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![t - l, -b; (s : ℤ), l], by rw [Matrix.det_fin_two_of]; linear_combination (-1 : ℤ) * hb⟩
  have hUcoe : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![t - l, -b; (s : ℤ), l] := rfl
  have hU : U ∈ CongruenceSubgroup.Gamma0 (1 * s) := by
    rw [CongruenceSubgroup.Gamma0_mem, one_mul]
    show (((U : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod s) = 0
    rw [hUcoe]
    simp
  have htr : (U : Matrix (Fin 2) (Fin 2) ℤ).trace = 0 ∨ (U : Matrix (Fin 2) (Fin 2) ℤ).trace = 1 ∨
      (U : Matrix (Fin 2) (Fin 2) ℤ).trace = -1 := by
    have h : (U : Matrix (Fin 2) (Fin 2) ℤ).trace = t := by
      rw [hUcoe, Matrix.trace_fin_two_of]
      ring
    rw [h]
    exact ht
  obtain ⟨x, y, δ, -, hxy⟩ :=
    ModularCurve.exists_smul_one_add_smul_eq_diagonal_mul_of_mem_Gamma0 1 s U hU htr
  rw [hUcoe] at hxy
  have hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := δ.prop
  rw [Matrix.det_fin_two] at hδ
  have hent : ∀ i j : Fin 2, (x • (1 : Matrix (Fin 2) (Fin 2) ℤ) + y • !![t - l, -b; (s : ℤ), l]) i j =
      (!![1, 0; 0, (s : ℤ)] * (δ : Matrix (Fin 2) (Fin 2) ℤ)) i j := fun i j => by rw [hxy]
  have h11 : x + y * l = (s : ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
    have h := hent 1 1
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, smul_eq_mul] at h
    norm_num at h
    linear_combination h
  have h10 : y * s = (s : ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have h := hent 1 0
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, smul_eq_mul] at h
    norm_num at h
    linear_combination h
  have h00 : x + y * (t - l) = (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    have h := hent 0 0
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, smul_eq_mul] at h
    norm_num at h
    linear_combination h
  have h01 : -(y * b) = (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
    have h := hent 0 1
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, smul_eq_mul] at h
    norm_num at h
    linear_combination h
  refine ⟨x, y, ?_, ⟨(δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, by linear_combination h11⟩⟩
  have hδ10 : ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) = y := by
    have h : (s : ℤ) * ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) = (s : ℤ) * y := by linear_combination -h10
    exact mul_left_cancel₀ (by exact_mod_cast hs0) h

  linear_combination (s : ℤ) * hδ + (s : ℤ) * ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * h00
    + (x + y * (t - l)) * h11 - (s : ℤ) * ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) * h01
    - (s : ℤ) * y * b * hδ10 + y ^ 2 * hb

end Arithmetic

section Cyclic

variable {G : Type*} [AddCommGroup G]

private theorem mem_zmultiples_of_smul_eq_zero {H : AddSubgroup G} (hH : IsAddCyclic H) {M s : ℕ} (hM : M ≠ 0)
    (hs : s ≠ 0) (hcard : Nat.card H = M * s) {Q : G} (hQ : Q ∈ H) (hQord : addOrderOf Q = s)
    {P : G} (hP : P ∈ H) (hsP : (s : ℤ) • P = 0) : P ∈ AddSubgroup.zmultiples Q := by
  obtain ⟨R, hR⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp hH
  have hRord : addOrderOf R = M * s := by rw [← Nat.card_zmultiples R, hR, hcard]
  have hdivR : ∀ {T : G}, T ∈ H → (s : ℤ) • T = 0 → ∃ a : ℤ, T = a • ((M : ℤ) • R) := by
    intro T hT hsT
    rw [← hR] at hT
    obtain ⟨c, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
    have hc : ((M * s : ℕ) : ℤ) ∣ s * c := by
      rw [← hRord, addOrderOf_dvd_iff_zsmul_eq_zero, mul_zsmul]
      exact hsT
    have hc' : (M : ℤ) ∣ c := by
      rw [Nat.cast_mul, mul_comm (M : ℤ)] at hc
      exact (mul_dvd_mul_iff_left (by exact_mod_cast hs)).mp hc
    obtain ⟨a, rfl⟩ := hc'
    exact ⟨a, by rw [mul_comm, mul_zsmul]⟩
  have hQs : (s : ℤ) • Q = 0 := by
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hQord]
  obtain ⟨a, ha⟩ := hdivR hP hsP
  obtain ⟨b, hbQ⟩ := hdivR hQ hQs
  set R₁ : G := (M : ℤ) • R with hR₁
  have hMdvd : M ∣ addOrderOf R := by rw [hRord]; exact Dvd.intro s rfl
  have hR₁ord : addOrderOf R₁ = s := by
    rw [hR₁, natCast_zsmul, addOrderOf_nsmul_of_dvd hM hMdvd, hRord, Nat.mul_div_cancel_left s (Nat.pos_of_ne_zero hM)]
  have hle : AddSubgroup.zmultiples Q ≤ AddSubgroup.zmultiples R₁ := by
    rw [AddSubgroup.zmultiples_le, hbQ]
    exact AddSubgroup.zsmul_mem_zmultiples R₁ b
  haveI : Finite (AddSubgroup.zmultiples R₁) := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_zmultiples, hR₁ord]
    exact hs
  have heq : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples R₁ :=
    AddSubgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zmultiples, Nat.card_zmultiples, hQord, hR₁ord])
  rw [heq, ha]
  exact AddSubgroup.zsmul_mem_zmultiples R₁ a

private theorem exists_eq_smul_of_smul_eq_zero {H : AddSubgroup G} (hH : IsAddCyclic H) {M s : ℕ} (hM : M ≠ 0)
    (hcard : Nat.card H = M * s) {P : G} (hP : P ∈ H) (hMP : M • P = 0) : ∃ T ∈ H, P = s • T := by
  obtain ⟨R, hR⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp hH
  have hRord : addOrderOf R = M * s := by rw [← Nat.card_zmultiples R, hR, hcard]
  have hP' := hP
  rw [← hR] at hP'
  obtain ⟨c, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hP'
  have hc : ((M * s : ℕ) : ℤ) ∣ M * c := by
    rw [← hRord, addOrderOf_dvd_iff_zsmul_eq_zero, mul_zsmul, natCast_zsmul]
    exact hMP
  have hc' : (s : ℤ) ∣ c := by
    rw [Nat.cast_mul] at hc
    exact (mul_dvd_mul_iff_left (by exact_mod_cast hM)).mp hc
  obtain ⟨a, rfl⟩ := hc'
  refine ⟨a • R, hR ▸ AddSubgroup.zsmul_mem_zmultiples R a, ?_⟩
  rw [mul_zsmul, natCast_zsmul]

end Cyclic

section Engine

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]

omit [IsAlgClosed k] in

private theorem stabEnd_mem_rationalHomSet (E : WeierstrassCurve k) (γ : MulAction.stabilizer (VariableChange k) E) :
    (stabEnd E γ : E.toAffine.Point →+ E.toAffine.Point) ∈ rationalHomSet k E E := by
  refine Or.inr ?_
  refine ⟨Polynomial.C (Polynomial.C ((((γ : VariableChange k).u⁻¹ : kˣ) : k) ^ 2) *
      (Polynomial.X - Polynomial.C (γ : VariableChange k).r)), 1,
    Polynomial.C (Polynomial.C ((((γ : VariableChange k).u⁻¹ : kˣ) : k) ^ 3)) * Polynomial.X +
      Polynomial.C (Polynomial.C ((((γ : VariableChange k).u⁻¹ : kˣ) : k) ^ 3) *
        (-Polynomial.C (γ : VariableChange k).t -
          Polynomial.C (γ : VariableChange k).s * (Polynomial.X - Polynomial.C (γ : VariableChange k).r))),
    1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC k (1 : Polynomial (Polynomial k)) x y = 1 := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  rw [e0, div_one, div_one]
  suffices H : ∀ a b : k, a = vcXInv (γ : VariableChange k) x → b = vcYInv (γ : VariableChange k) x y →
      ∃ h', (stabEnd E γ : E.toAffine.Point →+ E.toAffine.Point) (.some x y h) = .some a b h' by
    refine H _ _ ?_ ?_
    · simp [evalEvalBC, Polynomial.evalEval, vcXInv]
    · simp [evalEvalBC, Polynomial.evalEval, vcYInv]
      ring
  rintro a b rfl rfl
  exact exists_eq_some_of_ptCoords_eq (by rw [stabEnd_apply, ptCoords_stabAut]; rfl)

omit [IsAlgClosed k] in

private theorem neg_id_mem_rationalHomSet (E : WeierstrassCurve k) :
    (-(AddMonoidHom.id _) : E.toAffine.Point →+ E.toAffine.Point) ∈ rationalHomSet k E E := by
  refine Or.inr ⟨Polynomial.C Polynomial.X, 1,
    -Polynomial.X - Polynomial.C (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃), 1, ∅, Set.finite_empty,
    fun x y h _ => ?_⟩
  have e0 : evalEvalBC k (1 : Polynomial (Polynomial k)) x y = 1 := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  rw [e0, div_one, div_one]
  suffices H : ∀ a b : k, a = x → b = -y - E.a₁ * x - E.a₃ →
      ∃ h', (-(AddMonoidHom.id _) : E.toAffine.Point →+ E.toAffine.Point) (.some x y h) = .some a b h' by
    refine H _ _ ?_ ?_
    · simp [evalEvalBC, Polynomial.evalEval]
    · simp [evalEvalBC, Polynomial.evalEval]
      ring
  rintro a b rfl rfl
  exact ⟨_, by rw [AddMonoidHom.neg_apply, AddMonoidHom.id_apply, Affine.Point.neg_some]; rfl⟩

private theorem add_mem_rationalHomSet' (E : WeierstrassCurve k) [E.IsElliptic]
    {α β : E.toAffine.Point →+ E.toAffine.Point} (hα : α ∈ rationalHomSet k E E) (hβ : β ∈ rationalHomSet k E E) :
    α + β ∈ rationalHomSet k E E :=
  WeierstrassCurve.add_mem_rationalHomSet k E E hα hβ

private theorem variableChange_eq_of_forall_equivOfVariableChangeEq_eq' (E : WeierstrassCurve k) [E.IsElliptic]
    {C C' : VariableChange k} (hC : C • E = E) (hC' : C' • E = E)
    (h : ∀ P : E.toAffine.Point, Point.equivOfVariableChangeEq hC P = Point.equivOfVariableChangeEq hC' P) :
    C = C' :=
  WeierstrassCurve.Affine.variableChange_eq_of_forall_equivOfVariableChangeEq_eq hC hC' h

private theorem nsmul_mem_rationalHomSet (E : WeierstrassCurve k) [E.IsElliptic]
    {α : E.toAffine.Point →+ E.toAffine.Point} (hα : α ∈ rationalHomSet k E E) :
    ∀ m : ℕ, m • α ∈ rationalHomSet k E E
  | 0 => by rw [zero_nsmul]; exact zero_mem_rationalHomSet k E E
  | m + 1 => by rw [succ_nsmul]; exact add_mem_rationalHomSet' E (nsmul_mem_rationalHomSet E hα m) hα

private theorem zsmul_id_mem_rationalHomSet (E : WeierstrassCurve k) [E.IsElliptic] (m : ℤ) :
    m • (AddMonoidHom.id _ : E.toAffine.Point →+ E.toAffine.Point) ∈ rationalHomSet k E E := by
  induction m using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet k E E
  | succ i ih => rw [add_zsmul, one_zsmul]; exact add_mem_rationalHomSet' E ih (id_mem_rationalHomSet k E)
  | pred i ih =>
      rw [sub_zsmul, one_zsmul]
      exact add_mem_rationalHomSet' E ih (neg_id_mem_rationalHomSet E)

private theorem stabEnd_injective (E : WeierstrassCurve k) [E.IsElliptic] : Function.Injective (stabEnd E) := by
  intro γ γ' hγ
  apply Subtype.ext
  apply variableChange_eq_of_forall_equivOfVariableChangeEq_eq' E (MulAction.mem_stabilizer_iff.mp γ.2)
    (MulAction.mem_stabilizer_iff.mp γ'.2)
  intro P
  obtain ⟨P₀, rfl⟩ : ∃ P₀, stabAut E γ P₀ = P := ⟨(stabAut E γ).symm P, AddEquiv.apply_symm_apply _ _⟩
  have h' : stabAut E γ P₀ = stabAut E γ' P₀ := by
    rw [← stabEnd_apply, ← stabEnd_apply, hγ]
  conv_rhs => rw [h']
  rw [equivOfVariableChangeEq_stabAut, equivOfVariableChangeEq_stabAut]

private theorem finite_stabilizer (E : WeierstrassCurve k) [E.IsElliptic] :
    Finite (MulAction.stabilizer (VariableChange k) E) := by
  have hfin := WeierstrassCurve.finite_rationalHomSet_units k E
  let f : MulAction.stabilizer (VariableChange k) E →
      {u : E.toAffine.Point →+ E.toAffine.Point | u ∈ rationalHomSet k E E ∧
        ∃ v ∈ rationalHomSet k E E, u.comp v = AddMonoidHom.id _ ∧ v.comp u = AddMonoidHom.id _} :=
    fun γ => ⟨(stabEnd E γ : E.toAffine.Point →+ E.toAffine.Point), stabEnd_mem_rationalHomSet E γ,
      (stabEnd E γ⁻¹ : E.toAffine.Point →+ E.toAffine.Point), stabEnd_mem_rationalHomSet E γ⁻¹,
      by
        show (stabEnd E γ * stabEnd E γ⁻¹ : AddMonoid.End E.toAffine.Point) = 1
        rw [← map_mul, mul_inv_cancel, map_one],
      by
        show (stabEnd E γ⁻¹ * stabEnd E γ : AddMonoid.End E.toAffine.Point) = 1
        rw [← map_mul, inv_mul_cancel, map_one]⟩
  haveI : Finite {u : E.toAffine.Point →+ E.toAffine.Point | u ∈ rationalHomSet k E E ∧
      ∃ v ∈ rationalHomSet k E E, u.comp v = AddMonoidHom.id _ ∧ v.comp u = AddMonoidHom.id _} := hfin
  refine Finite.of_injective f ?_
  intro γ γ' h
  exact stabEnd_injective E (congrArg Subtype.val h)

private theorem end_mul_apply {X : Type*} [AddCommGroup X] (f g : AddMonoid.End X) (x : X) : (f * g) x = f (g x) :=
  rfl

private theorem exists_variableChange_veluQuotient_of_two_lt_natCard_pairStabilizer
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (M n : ℕ) [NeZero M]
    (hMs : ((M * (2 * n + 1) : ℕ) : k) ≠ 0) (hs : (2 * n + 1).Prime) (hsM : ¬ (2 * n + 1) ∣ M)
    (H : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = M * (2 * n + 1)})
    (hstab : 2 < Nat.card {γ : VariableChange k // γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'})
    (Q : E₀.toAffine.Point) (hQ : Q ∈ H.1) (hQord : addOrderOf Q = 2 * n + 1)
    (hΔ : (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).Δ ≠ 0)
    (φ : E₀.toAffine.Point →+ (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ (x y : k) (h : E₀.toAffine.Nonsingular x y),
      (.some x y h : E₀.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (E₀.veluX (E₀.oddOrderSummingSet Q n) x)
          (E₀.veluY (E₀.oddOrderSummingSet Q n) x y) h') :
    ∃ γ₀ : VariableChange k, γ₀ • E₀.veluQuotient (E₀.oddOrderSummingSet Q n) = E₀ ∧
      ∀ T ∈ H.1, ∃ T' ∈ H.1,
        HEq (Point.vcInvFun γ₀ (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine (φ T))
          ((2 * n + 1) • T') := by
  have _ := hsM
  have _ := hΔ
  have hM : M ≠ 0 := NeZero.ne M
  have hs0 : 2 * n + 1 ≠ 0 := hs.ne_zero
  have hsk : ((2 * n + 1 : ℕ) : k) ≠ 0 := by
    intro h
    apply hMs
    rw [Nat.cast_mul, h, mul_zero]
  have hQ0 : Q ≠ 0 := by
    intro h
    rw [h, addOrderOf_zero] at hQord
    exact hs.one_lt.ne hQord

  let ι : {γ : VariableChange k // γ • E₀ = E₀ ∧ ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'} →
      MulAction.stabilizer (VariableChange k) E₀ := fun γ => ⟨γ.1, MulAction.mem_stabilizer_iff.mpr γ.2.1⟩
  have hι : Function.Injective ι := fun γ γ' h =>
    Subtype.ext (congrArg (fun δ : MulAction.stabilizer (VariableChange k) E₀ => (δ : VariableChange k)) h)
  have hB : Function.Injective (fun γ => stabEnd E₀ (ι γ)) := (stabEnd_injective E₀).comp hι

  obtain ⟨u, hu1, hum1⟩ : ∃ u, stabEnd E₀ (ι u) ≠ 1 ∧ stabEnd E₀ (ι u) ≠ -1 := by
    haveI : Finite {γ : VariableChange k // γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'} := Nat.finite_of_card_ne_zero (by omega)
    haveI : Fintype {γ : VariableChange k // γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at hstab
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hstab
    by_cases ha : stabEnd E₀ (ι a) ≠ 1 ∧ stabEnd E₀ (ι a) ≠ -1
    · exact ⟨a, ha⟩
    by_cases hb : stabEnd E₀ (ι b) ≠ 1 ∧ stabEnd E₀ (ι b) ≠ -1
    · exact ⟨b, hb⟩
    by_cases hc : stabEnd E₀ (ι c) ≠ 1 ∧ stabEnd E₀ (ι c) ≠ -1
    · exact ⟨c, hc⟩
    exfalso
    simp only [not_and_or, not_not] at ha hb hc
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
    all_goals first
      | exact hab (hB (ha.trans hb.symm))
      | exact hac (hB (ha.trans hc.symm))
      | exact hbc (hB (hb.trans hc.symm))

  set βA : AddMonoid.End E₀.toAffine.Point := stabEnd E₀ (ι u) with hβA
  set β : E₀.toAffine.Point →+ E₀.toAffine.Point := (stabAut E₀ (ι u) : E₀.toAffine.Point →+ E₀.toAffine.Point)
    with hβ
  have hβA_apply : ∀ P, βA P = β P := fun _ => rfl
  have hβmem : β ∈ rationalHomSet k E₀ E₀ := stabEnd_mem_rationalHomSet E₀ (ι u)
  have hβH : ∀ T ∈ H.1, β T ∈ H.1 := by
    intro T hT
    obtain ⟨T', hT', he⟩ := u.2.2 T hT
    have he' : stabAut E₀ (ι u) T = T' := (heq_vcInvFun_iff E₀ (ι u) T T').mp he
    show stabAut E₀ (ι u) T ∈ H.1
    rw [he']
    exact hT'
  have hβinj : Function.Injective β := (stabAut E₀ (ι u)).injective
  have hβ0 : β ≠ 0 := by
    intro h
    have h1 : β Q = 0 := by rw [h]; rfl
    exact hQ0 (hβinj (h1.trans (map_zero β).symm))

  obtain ⟨σ, -, t, m, -, hdual, hsum⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id k E₀ hβmem hβ0
  let σ' : E₀.toAffine.Point →+ E₀.toAffine.Point := σ
  have hrelP : ∀ P, β (β P) - t • β P + m • P = 0 := by
    intro P
    have h1 : σ' (β P) = m • P := hdual.comp_left P
    have h2 : (β + σ') (β P) = (t • AddMonoidHom.id _ : E₀.toAffine.Point →+ E₀.toAffine.Point) (β P) :=
      congrArg (fun f : E₀.toAffine.Point →+ E₀.toAffine.Point => f (β P)) hsum
    have h3 : β (β P) + σ' (β P) = t • β P := h2
    rw [← h3, h1]
    abel
  have hrel : βA * βA - (t : AddMonoid.End E₀.toAffine.Point) * βA + (m : AddMonoid.End E₀.toAffine.Point) = 0 := by
    apply AddMonoidHom.ext
    intro P
    exact hrelP P
  haveI : Finite (MulAction.stabilizer (VariableChange k) E₀) := finite_stabilizer E₀
  have he : orderOf (ι u) ≠ 0 := (orderOf_pos (ι u)).ne'
  have hβe : βA ^ orderOf (ι u) = 1 := by
    rw [hβA, ← map_pow, pow_orderOf_eq_one, map_one]

  have htf : ∀ c : ℤ, (c : AddMonoid.End E₀.toAffine.Point) = 0 → c = 0 := by
    intro c hc
    by_contra hc0
    obtain ⟨r, hr, hrp⟩ := Nat.exists_infinite_primes (max (c.natAbs + 1) (ringChar k + 1))
    have hrc : ¬ (r : ℤ) ∣ c := by
      intro h
      have h1 : r ≤ c.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hc0) (Int.natCast_dvd.mp h)
      omega
    have hrk : (r : k) ≠ 0 := by
      intro h
      have hdvd : ringChar k ∣ r := (ringChar.spec k r).mp h
      rcases (Nat.dvd_prime hrp).mp hdvd with h1 | h1
      · exact CharP.ringChar_ne_one h1
      · omega
    obtain ⟨T, hT⟩ := WeierstrassCurve.exists_addOrderOf_eq_prime_of_isAlgClosed E₀ r hrp hrk
    have h1 : c • T = 0 := by
      have h := congrArg (fun f : AddMonoid.End E₀.toAffine.Point => f T) hc
      simpa using h
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hT] at h1
    exact hrc h1

  have hsubmem : ∀ a : ℤ, ((βA - (a : AddMonoid.End E₀.toAffine.Point) : AddMonoid.End E₀.toAffine.Point) :
      E₀.toAffine.Point →+ E₀.toAffine.Point) ∈ rationalHomSet k E₀ E₀ := by
    intro a
    have h : ((βA - (a : AddMonoid.End E₀.toAffine.Point) : AddMonoid.End E₀.toAffine.Point) :
        E₀.toAffine.Point →+ E₀.toAffine.Point) = β + (-a) • AddMonoidHom.id _ := by
      apply AddMonoidHom.ext
      intro P
      show β P - a • P = β P + (-a) • P
      rw [neg_smul, sub_eq_add_neg]
    rw [h]
    exact add_mem_rationalHomSet' E₀ hβmem (zsmul_id_mem_rationalHomSet E₀ (-a))
  have hdom : ∀ a b : ℤ, (βA - a) * (βA - b) = 0 → βA = a ∨ βA = b := by
    intro a b hab
    by_cases hb : βA = b
    · exact Or.inr hb
    left
    have hb0 : ((βA - (b : AddMonoid.End E₀.toAffine.Point) : AddMonoid.End E₀.toAffine.Point) :
        E₀.toAffine.Point →+ E₀.toAffine.Point) ≠ 0 := fun h => hb (sub_eq_zero.mp h)
    have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet k (hsubmem b) hb0
    refine sub_eq_zero.mp (AddMonoidHom.ext fun P => ?_)
    obtain ⟨P', rfl⟩ := hsurj P
    have h := congrArg (fun f : AddMonoid.End E₀.toAffine.Point => f P') hab
    exact h
  obtain ⟨hm1, ht⟩ := norm_eq_one_and_trace_of_pow_eq_one βA he hβe t m hrel htf hdom hu1 hum1
  subst hm1

  have hQs : ((2 * n + 1 : ℕ) : ℤ) • Q = 0 := by rw [← hQord, natCast_zsmul, addOrderOf_nsmul_eq_zero]
  have hβQmem : β Q ∈ AddSubgroup.zmultiples Q := by
    refine mem_zmultiples_of_smul_eq_zero H.2.1 hM hs0 H.2.2 hQ hQord (hβH Q hQ) ?_
    rw [← map_zsmul, hQs, map_zero]
  obtain ⟨lam, hlam⟩ := AddSubgroup.mem_zmultiples_iff.mp hβQmem
  have hcong : ((2 * n + 1 : ℕ) : ℤ) ∣ lam ^ 2 - t * lam + 1 := by
    rw [← hQord, addOrderOf_dvd_iff_zsmul_eq_zero]
    have h := hrelP Q
    rw [← hlam, map_zsmul, ← hlam, smul_smul, smul_smul, one_zsmul] at h
    rw [add_zsmul, sub_zsmul, one_zsmul, sq]
    exact h

  obtain ⟨x, y, hxy, hdvd, hy⟩ : ∃ x y : ℤ, x ^ 2 + t * x * y + y ^ 2 = (2 * n + 1 : ℕ) ∧
      ((2 * n + 1 : ℕ) : ℤ) ∣ x + y * lam ∧ 0 < y := by
    obtain ⟨x, y, hxy, hdvd⟩ := exists_norm_eq_and_dvd (2 * n + 1) hs0 t lam ht hcong
    have hy : y ≠ 0 := by
      rintro rfl
      have h1 : x ^ 2 = (2 * n + 1 : ℕ) := by simpa using hxy
      have hx : x.natAbs * x.natAbs = 2 * n + 1 := by
        have h : ((x.natAbs : ℤ)) ^ 2 = (2 * n + 1 : ℕ) := by rw [Int.natAbs_sq]; exact h1
        have h' : x.natAbs ^ 2 = 2 * n + 1 := by exact_mod_cast h
        rw [sq] at h'
        exact h'
      rw [← hx] at hs
      rcases Nat.prime_mul_iff.mp hs with ⟨hp, h1⟩ | ⟨hp, h1⟩ <;> rw [h1] at hp <;> exact Nat.not_prime_one hp
    rcases lt_or_gt_of_ne hy with hy | hy
    · refine ⟨-x, -y, by linear_combination hxy, ?_, by linarith⟩
      rw [show -x + -y * lam = -(x + y * lam) by ring]
      exact (dvd_neg).mpr hdvd
    · exact ⟨x, y, hxy, hdvd, hy⟩

  set πA : AddMonoid.End E₀.toAffine.Point :=
    Polynomial.aeval βA (Polynomial.C x + Polynomial.C y * Polynomial.X : Polynomial ℤ) with hπA
  set π : E₀.toAffine.Point →+ E₀.toAffine.Point := x • AddMonoidHom.id _ + y.toNat • β with hπ
  have hπapply : ∀ P, π P = x • P + y • β P := by
    intro P
    show x • P + y.toNat • β P = x • P + y • β P
    rw [← natCast_zsmul, Int.toNat_of_nonneg hy.le]
  have hπA_eq : πA = (x : AddMonoid.End E₀.toAffine.Point) + (y : AddMonoid.End E₀.toAffine.Point) * βA := by
    rw [hπA]
    simp
  have hπA_apply : ∀ P, πA P = π P := by
    intro P
    rw [hπapply, hπA_eq]
    show ((x : AddMonoid.End E₀.toAffine.Point)) P + ((y : AddMonoid.End E₀.toAffine.Point) * βA) P = _
    rw [end_mul_apply, AddMonoid.End.intCast_apply, AddMonoid.End.intCast_apply, hβA_apply]
  have hπmem : π ∈ rationalHomSet k E₀ E₀ :=
    add_mem_rationalHomSet' E₀ (zsmul_id_mem_rationalHomSet E₀ x) (nsmul_mem_rationalHomSet E₀ hβmem _)
  have hπQ : π Q = 0 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hπapply, ← hlam, smul_smul, ← add_zsmul, hc, mul_comm, mul_zsmul, hQs, zsmul_zero]
  have hπH : ∀ T ∈ H.1, π T ∈ H.1 := fun T hT => by
    rw [hπapply]
    exact H.1.add_mem (H.1.zsmul_mem hT x) (H.1.zsmul_mem (hβH T hT) y)

  have hquad : Polynomial.aeval βA
      (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C 1 : Polynomial ℤ) = 0 := by
    rw [aeval_quad]
    simpa using hrel
  have hπrel : πA * πA + (((2 * n + 1 : ℕ) : ℤ) : AddMonoid.End E₀.toAffine.Point) =
      ((2 * x + t * y : ℤ) : AddMonoid.End E₀.toAffine.Point) * πA := by
    have hid2 : (Polynomial.C x + Polynomial.C y * Polynomial.X : Polynomial ℤ) *
          (Polynomial.C x + Polynomial.C y * Polynomial.X) + Polynomial.C ((2 * n + 1 : ℕ) : ℤ) -
          Polynomial.C (2 * x + t * y) * (Polynomial.C x + Polynomial.C y * Polynomial.X) =
        Polynomial.C (y ^ 2) * (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C 1) := by
      rw [← hxy]
      simp only [map_add, map_mul, map_pow, map_one, map_ofNat]
      ring
    have h := congrArg (Polynomial.aeval βA) hid2
    rw [map_mul (Polynomial.aeval βA) (Polynomial.C (y ^ 2)), hquad, mul_zero, map_sub, map_add, map_mul,
      map_mul, ← hπA, Polynomial.aeval_C, Polynomial.aeval_C, eq_intCast, eq_intCast] at h
    exact sub_eq_zero.mp h
  have hchar : π.comp π + ((2 * n + 1 : ℕ) : ℤ) • AddMonoidHom.id _ = (2 * x + t * y) • π := by
    apply AddMonoidHom.ext
    intro P
    have h := congrArg (fun f : AddMonoid.End E₀.toAffine.Point => f P) hπrel
    change πA (πA P) + ((2 * n + 1 : ℕ) : ℤ) • P = (2 * x + t * y) • πA P at h
    rw [hπA_apply, hπA_apply] at h
    show π (π P) + ((2 * n + 1 : ℕ) : ℤ) • P = (2 * x + t * y) • π P
    exact h
  have hirr : ∀ z : ℤ, z ^ 2 - (2 * x + t * y) * z + (2 * n + 1 : ℕ) ≠ 0 := by
    intro z hz
    rw [← hxy] at hz
    rcases ht with rfl | rfl | rfl
    · nlinarith [sq_nonneg (z - x)]
    · nlinarith [sq_nonneg (2 * z - 2 * x - y)]
    · nlinarith [sq_nonneg (2 * z - 2 * x + y)]
  have hprim : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ 2 * x + t * y → ¬ (ℓ : ℤ) ^ 2 ∣ ((2 * n + 1 : ℕ) : ℤ) := by
    intro ℓ hℓ _ hsq
    have h1 : ℓ ^ 2 ∣ 2 * n + 1 := by exact_mod_cast hsq
    have h2 : ℓ ∣ 2 * n + 1 := (Dvd.intro_left _ (sq ℓ).symm).trans h1
    rcases (Nat.dvd_prime hs).mp h2 with h3 | h3
    · exact hℓ.one_lt.ne' h3
    · rw [h3] at h1
      have h4 := Nat.le_of_dvd hs.pos h1
      nlinarith [hs.one_lt]

  obtain ⟨γ₀, hγ₀, hfac⟩ :=
    WeierstrassCurve.exists_variableChange_smul_eq_veluQuotient_forall_apply_eq_of_comp_self_add_smul_eq_smul E₀ hπmem
      (2 * x + t * y) n hchar hirr hprim hsk Q hQord hπQ φ hφker hφ
  have hE : γ₀⁻¹ • E₀.veluQuotient (E₀.oddOrderSummingSet Q n) = E₀ := by rw [← hγ₀, inv_smul_smul]
  refine ⟨γ₀⁻¹, hE, fun T hT => ?_⟩

  have hMπ : M • π T = 0 := by
    have hMT : M • T ∈ H.1 := H.1.nsmul_mem hT M
    have hsMT : ((2 * n + 1 : ℕ) : ℤ) • (M • T) = 0 := by
      rw [natCast_zsmul, ← mul_nsmul, ← H.2.2]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (H.1.addOrderOf_dvd_natCard hT)
    obtain ⟨c, hc⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (mem_zmultiples_of_smul_eq_zero H.2.1 hM hs0 H.2.2 hQ hQord hMT hsMT)
    rw [← map_nsmul, ← hc, map_zsmul, hπQ, zsmul_zero]
  obtain ⟨T', hT', hπT⟩ := exists_eq_smul_of_smul_eq_zero H.2.1 hM H.2.2 (hπH T hT) hMπ
  refine ⟨T', hT', ?_⟩
  rw [heq_iff_ptCoords_eq hE, ptCoords_vcInvFun, invCoords_inv, ← ptCoords_equivOfVariableChangeEq hγ₀ (φ T),
    ← hfac T, ← hπT]

end Engine

section EngineTwo

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]

private theorem exists_variableChange_smul_eq_veluQuotient2_forall_apply_eq_of_comp_self_add_two_smul_eq_smul'
    (h2 : (2 : k) ≠ 0) (W : WeierstrassCurve k) [W.IsElliptic]
    {β : W.toAffine.Point →+ W.toAffine.Point} (hβ : β ∈ WeierstrassCurve.rationalHomSet k W W)
    (s : ℤ) (hchar : β.comp β + (2 : ℤ) • AddMonoidHom.id _ = s • β)
    (hirr : ∀ x : ℤ, x ^ 2 - s * x + 2 ≠ 0)
    {x₀ y₀ : k} (hns : W.toAffine.Nonsingular x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (hQβ : β (.some x₀ y₀ hns) = 0)
    (φ₀ : W.toAffine.Point →+ (W.veluQuotient2 x₀ y₀).toAffine.Point)
    (hφ₀ : ⇑φ₀ = WeierstrassCurve.veluPointMap2 h2 hns.1 hgy hΔ) :
    ∃ (γ₀ : WeierstrassCurve.VariableChange k) (hγ₀ : γ₀ • W = W.veluQuotient2 x₀ y₀),
      ∀ P, β P = WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ₀ (φ₀ P) := by
  obtain ⟨γ₀, hγ₀, h⟩ :=
    WeierstrassCurve.exists_variableChange_smul_eq_veluQuotient2_forall_apply_eq_of_comp_self_add_two_smul_eq_smul
      W hβ s hchar hirr h2 hns hgy hΔ hQβ
  exact ⟨γ₀, hγ₀, fun P => by rw [hφ₀]; exact h P⟩

private theorem exists_variableChange_fullKernelQuotient_two_of_two_lt_natCard_pairStabilizer
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (M : ℕ) [NeZero M]
    (hM2 : ((M * 2 : ℕ) : k) ≠ 0) (h2M : ¬ 2 ∣ M)
    (H : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = M * 2})
    (hstab : 2 < Nat.card {γ : VariableChange k // γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'})
    (Q : E₀.toAffine.Point) (hQ : Q ∈ H.1) (hQord : addOrderOf Q = 2)
    (hΔ : (E₀.fullKernelQuotient Q 2).Δ ≠ 0)
    (φ : E₀.toAffine.Point →+ (E₀.fullKernelQuotient Q 2).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : E₀.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ i ∈ Finset.Icc 1 (2 - 1),
            ((P + i • Q).coordsOrZero.1 - (i • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ i ∈ Finset.Icc 1 (2 - 1),
            ((P + i • Q).coordsOrZero.2 - (i • Q).coordsOrZero.2))) :
    ∃ γ₀ : VariableChange k, γ₀ • E₀.fullKernelQuotient Q 2 = E₀ ∧
      ∀ T ∈ H.1, ∃ T' ∈ H.1,
        HEq (Point.vcInvFun γ₀ (E₀.fullKernelQuotient Q 2).toAffine (φ T)) (2 • T') := by
  have _ := h2M
  have hM : M ≠ 0 := NeZero.ne M
  have hs0 : (2 : ℕ) ≠ 0 := two_ne_zero
  have hsk : ((2 : ℕ) : k) ≠ 0 := by
    intro h
    apply hM2
    rw [Nat.cast_mul, h, mul_zero]
  have h2k : (2 : k) ≠ 0 := by
    intro h
    apply hsk
    rw [Nat.cast_ofNat, h]
  have hQ0 : Q ≠ 0 := by
    intro h
    rw [h, addOrderOf_zero] at hQord
    exact absurd hQord (by decide)

  let ι : {γ : VariableChange k // γ • E₀ = E₀ ∧ ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'} →
      MulAction.stabilizer (VariableChange k) E₀ := fun γ => ⟨γ.1, MulAction.mem_stabilizer_iff.mpr γ.2.1⟩
  have hι : Function.Injective ι := fun γ γ' h =>
    Subtype.ext (congrArg (fun δ : MulAction.stabilizer (VariableChange k) E₀ => (δ : VariableChange k)) h)
  have hB : Function.Injective (fun γ => stabEnd E₀ (ι γ)) := (stabEnd_injective E₀).comp hι

  obtain ⟨u, hu1, hum1⟩ : ∃ u, stabEnd E₀ (ι u) ≠ 1 ∧ stabEnd E₀ (ι u) ≠ -1 := by
    haveI : Finite {γ : VariableChange k // γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'} := Nat.finite_of_card_ne_zero (by omega)
    haveI : Fintype {γ : VariableChange k // γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at hstab
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hstab
    by_cases ha : stabEnd E₀ (ι a) ≠ 1 ∧ stabEnd E₀ (ι a) ≠ -1
    · exact ⟨a, ha⟩
    by_cases hb : stabEnd E₀ (ι b) ≠ 1 ∧ stabEnd E₀ (ι b) ≠ -1
    · exact ⟨b, hb⟩
    by_cases hc : stabEnd E₀ (ι c) ≠ 1 ∧ stabEnd E₀ (ι c) ≠ -1
    · exact ⟨c, hc⟩
    exfalso
    simp only [not_and_or, not_not] at ha hb hc
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
    all_goals first
      | exact hab (hB (ha.trans hb.symm))
      | exact hac (hB (ha.trans hc.symm))
      | exact hbc (hB (hb.trans hc.symm))

  set βA : AddMonoid.End E₀.toAffine.Point := stabEnd E₀ (ι u) with hβA
  set β : E₀.toAffine.Point →+ E₀.toAffine.Point := (stabAut E₀ (ι u) : E₀.toAffine.Point →+ E₀.toAffine.Point)
    with hβ
  have hβA_apply : ∀ P, βA P = β P := fun _ => rfl
  have hβmem : β ∈ rationalHomSet k E₀ E₀ := stabEnd_mem_rationalHomSet E₀ (ι u)
  have hβH : ∀ T ∈ H.1, β T ∈ H.1 := by
    intro T hT
    obtain ⟨T', hT', he⟩ := u.2.2 T hT
    have he' : stabAut E₀ (ι u) T = T' := (heq_vcInvFun_iff E₀ (ι u) T T').mp he
    show stabAut E₀ (ι u) T ∈ H.1
    rw [he']
    exact hT'
  have hβinj : Function.Injective β := (stabAut E₀ (ι u)).injective
  have hβ0 : β ≠ 0 := by
    intro h
    have h1 : β Q = 0 := by rw [h]; rfl
    exact hQ0 (hβinj (h1.trans (map_zero β).symm))

  obtain ⟨σ, -, t, m, -, hdual, hsum⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id k E₀ hβmem hβ0
  let σ' : E₀.toAffine.Point →+ E₀.toAffine.Point := σ
  have hrelP : ∀ P, β (β P) - t • β P + m • P = 0 := by
    intro P
    have h1 : σ' (β P) = m • P := hdual.comp_left P
    have h2 : (β + σ') (β P) = (t • AddMonoidHom.id _ : E₀.toAffine.Point →+ E₀.toAffine.Point) (β P) :=
      congrArg (fun f : E₀.toAffine.Point →+ E₀.toAffine.Point => f (β P)) hsum
    have h3 : β (β P) + σ' (β P) = t • β P := h2
    rw [← h3, h1]
    abel
  have hrel : βA * βA - (t : AddMonoid.End E₀.toAffine.Point) * βA + (m : AddMonoid.End E₀.toAffine.Point) = 0 := by
    apply AddMonoidHom.ext
    intro P
    exact hrelP P
  haveI : Finite (MulAction.stabilizer (VariableChange k) E₀) := finite_stabilizer E₀
  have he : orderOf (ι u) ≠ 0 := (orderOf_pos (ι u)).ne'
  have hβe : βA ^ orderOf (ι u) = 1 := by
    rw [hβA, ← map_pow, pow_orderOf_eq_one, map_one]

  have htf : ∀ c : ℤ, (c : AddMonoid.End E₀.toAffine.Point) = 0 → c = 0 := by
    intro c hc
    by_contra hc0
    obtain ⟨r, hr, hrp⟩ := Nat.exists_infinite_primes (max (c.natAbs + 1) (ringChar k + 1))
    have hrc : ¬ (r : ℤ) ∣ c := by
      intro h
      have h1 : r ≤ c.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hc0) (Int.natCast_dvd.mp h)
      omega
    have hrk : (r : k) ≠ 0 := by
      intro h
      have hdvd : ringChar k ∣ r := (ringChar.spec k r).mp h
      rcases (Nat.dvd_prime hrp).mp hdvd with h1 | h1
      · exact CharP.ringChar_ne_one h1
      · omega
    obtain ⟨T, hT⟩ := WeierstrassCurve.exists_addOrderOf_eq_prime_of_isAlgClosed E₀ r hrp hrk
    have h1 : c • T = 0 := by
      have h := congrArg (fun f : AddMonoid.End E₀.toAffine.Point => f T) hc
      simpa using h
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hT] at h1
    exact hrc h1

  have hsubmem : ∀ a : ℤ, ((βA - (a : AddMonoid.End E₀.toAffine.Point) : AddMonoid.End E₀.toAffine.Point) :
      E₀.toAffine.Point →+ E₀.toAffine.Point) ∈ rationalHomSet k E₀ E₀ := by
    intro a
    have h : ((βA - (a : AddMonoid.End E₀.toAffine.Point) : AddMonoid.End E₀.toAffine.Point) :
        E₀.toAffine.Point →+ E₀.toAffine.Point) = β + (-a) • AddMonoidHom.id _ := by
      apply AddMonoidHom.ext
      intro P
      show β P - a • P = β P + (-a) • P
      rw [neg_smul, sub_eq_add_neg]
    rw [h]
    exact add_mem_rationalHomSet' E₀ hβmem (zsmul_id_mem_rationalHomSet E₀ (-a))
  have hdom : ∀ a b : ℤ, (βA - a) * (βA - b) = 0 → βA = a ∨ βA = b := by
    intro a b hab
    by_cases hb : βA = b
    · exact Or.inr hb
    left
    have hb0 : ((βA - (b : AddMonoid.End E₀.toAffine.Point) : AddMonoid.End E₀.toAffine.Point) :
        E₀.toAffine.Point →+ E₀.toAffine.Point) ≠ 0 := fun h => hb (sub_eq_zero.mp h)
    have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet k (hsubmem b) hb0
    refine sub_eq_zero.mp (AddMonoidHom.ext fun P => ?_)
    obtain ⟨P', rfl⟩ := hsurj P
    have h := congrArg (fun f : AddMonoid.End E₀.toAffine.Point => f P') hab
    exact h
  obtain ⟨hm1, ht⟩ := norm_eq_one_and_trace_of_pow_eq_one βA he hβe t m hrel htf hdom hu1 hum1
  subst hm1

  have hQ2 : (2 : ℕ) • Q = 0 := by rw [← hQord]; exact addOrderOf_nsmul_eq_zero Q
  have hQs : ((2 : ℕ) : ℤ) • Q = 0 := by rw [natCast_zsmul]; exact hQ2
  have hβQmem : β Q ∈ AddSubgroup.zmultiples Q := by
    refine mem_zmultiples_of_smul_eq_zero H.2.1 hM hs0 H.2.2 hQ hQord (hβH Q hQ) ?_
    rw [← map_zsmul, hQs, map_zero]
  obtain ⟨lam, hlam⟩ := AddSubgroup.mem_zmultiples_iff.mp hβQmem
  have hcong : ((2 : ℕ) : ℤ) ∣ lam ^ 2 - t * lam + 1 := by
    have h' : (addOrderOf Q : ℤ) ∣ lam ^ 2 - t * lam + 1 := by
      rw [addOrderOf_dvd_iff_zsmul_eq_zero]
      have h := hrelP Q
      rw [← hlam, map_zsmul, ← hlam, smul_smul, smul_smul, one_zsmul] at h
      rw [add_zsmul, sub_zsmul, one_zsmul, sq]
      exact h
    rwa [hQord] at h'
  have hlam2 : Odd lam := by
    refine Int.not_even_iff_odd.mp fun ⟨c, hc⟩ => hQ0 (hβinj ?_)
    rw [map_zero, ← hlam, hc, add_zsmul, ← two_zsmul, smul_smul, mul_comm, mul_zsmul]
    show c • ((2 : ℕ) : ℤ) • Q = 0
    rw [hQs, zsmul_zero]
  obtain ⟨c, hc⟩ := hlam2
  have ht0 : t = 0 := by
    have h2t : (2 : ℤ) ∣ t := by
      have e : t = 2 * (2 * c ^ 2 + 2 * c + 1 - t * c) - (lam ^ 2 - t * lam + 1) := by
        rw [hc]
        ring
      rw [e]
      exact dvd_sub (dvd_mul_right 2 _) (by exact_mod_cast hcong)
    rcases ht with h | h | h
    · exact h
    · exfalso
      rw [h] at h2t
      omega
    · exfalso
      rw [h] at h2t
      omega
  subst ht0
  have hββ : ∀ P, β (β P) = -P := by
    intro P
    have h := hrelP P
    have h' : β (β P) + P = 0 := by simpa using h
    exact eq_neg_of_add_eq_zero_left h'

  set π : E₀.toAffine.Point →+ E₀.toAffine.Point := AddMonoidHom.id _ + β with hπ
  have hπapply : ∀ P, π P = P + β P := fun _ => rfl
  have hπmem : π ∈ rationalHomSet k E₀ E₀ := add_mem_rationalHomSet' E₀ (id_mem_rationalHomSet k E₀) hβmem
  have hπQ : π Q = 0 := by
    rw [hπapply, ← hlam, hc]
    calc Q + (2 * c + 1) • Q = (1 : ℤ) • Q + (2 * c + 1) • Q := by rw [one_zsmul]
      _ = ((c + 1) * ((2 : ℕ) : ℤ)) • Q := by rw [← add_zsmul]; congr 1; push_cast; ring
      _ = 0 := by rw [mul_zsmul, hQs, zsmul_zero]
  have hπH : ∀ T ∈ H.1, π T ∈ H.1 := fun T hT => by
    rw [hπapply]
    exact H.1.add_mem hT (hβH T hT)
  have hchar : π.comp π + (2 : ℤ) • AddMonoidHom.id _ = (2 : ℤ) • π := by
    apply AddMonoidHom.ext
    intro P
    show π (π P) + (2 : ℤ) • P = (2 : ℤ) • π P
    rw [hπapply, hπapply, map_add, hββ]
    abel
  have hirr : ∀ z : ℤ, z ^ 2 - 2 * z + 2 ≠ 0 := fun z hz => by nlinarith [sq_nonneg (z - 1)]

  have h1k : ((0 + 1 : ℕ) : k) ≠ 0 := by norm_num
  have hord2 : addOrderOf (2 • Q) = 0 + 1 := by rw [hQ2, addOrderOf_zero]
  obtain ⟨ρ, hρker, hρ⟩ := WeierstrassCurve.exists_fullKernelHom E₀ (N := 0 + 1) h1k (2 • Q) hord2
  have hNk : ((2 * (0 + 1) : ℕ) : k) ≠ 0 := by norm_num; exact h2k
  have hQord' : addOrderOf Q = 2 * (0 + 1) := hQord
  have hΔ' : (E₀.fullKernelQuotient Q (2 * (0 + 1))).Δ ≠ 0 := hΔ
  obtain ⟨x₁, y₁, h₁, hgy₁, hΔ₁, E, hE, hρQ, hφE⟩ :=
    WeierstrassCurve.fullKernelHom_eq_veluPointMap2_comp_of_stage_last E₀ (m := 0) hNk h2k Q hQord' hΔ'
      φ hφker hφ ρ hρker hρ

  have hI : Finset.Icc 1 (0 + 1 - 1) = (∅ : Finset ℕ) := by decide
  have hV : E₀.fullKernelQuotient (2 • Q) (0 + 1) = E₀ := by
    ext <;> simp [fullKernelQuotient, veluQuotientOfSums, oddOrderSummingSet]
  have hρ0 : ∀ P : E₀.toAffine.Point, ρ P = 0 → P = 0 := by
    intro P hP
    have hP' : P ∈ ρ.ker := hP
    rw [hρker] at hP'
    obtain ⟨d, hd⟩ := AddSubgroup.mem_zmultiples_iff.mp hP'
    rw [← hd, hQ2, zsmul_zero]
  have hρc : ∀ P, ptCoords (ρ P) = ptCoords P := by
    intro P
    by_cases hP : P = 0
    · rw [hP, map_zero]
      rfl
    have hPn : P ∉ AddSubgroup.zmultiples (2 • Q) := by
      intro hmem
      obtain ⟨d, hd⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
      rw [hQ2, zsmul_zero] at hd
      exact hP hd.symm
    have hco := hρ P hPn
    simp only [hI, Finset.sum_empty, add_zero, Prod.mk.eta] at hco
    rw [ptCoords_eq_some_coordsOrZero (fun h => hP (hρ0 P h)), ptCoords_eq_some_coordsOrZero hP, hco]
  obtain ⟨h₁', hgy', hΔ'', hE', hQpt, hφ'⟩ :=
    fullKernel_seam h2k hV ρ hρc h₁ hgy₁ hΔ₁ E hE φ hφE Q hρQ
  have hE2 : E • E₀.fullKernelQuotient Q 2 = E₀.veluQuotient2 x₁ y₁ := hE'
  have hφ2 : ∀ P, φ P = Point.equivOfVariableChangeEq hE2 (veluPointMap2 h2k h₁'.1 hgy' hΔ'' P) := hφ'

  let φ₀ : E₀.toAffine.Point →+ (E₀.veluQuotient2 x₁ y₁).toAffine.Point :=
    (ptCastOfEq hE2).toAddMonoidHom.comp
      ((AddEquiv.mk' (Point.variableChangeEquiv E (E₀.fullKernelQuotient Q 2).toAffine).symm
          (Point.vcInvFun_add E (E₀.fullKernelQuotient Q 2).toAffine)).toAddMonoidHom.comp φ)
  have hφ₀P : ∀ P, φ₀ P = veluPointMap2 h2k h₁'.1 hgy' hΔ'' P := by
    intro P
    apply eq_of_ptCoords_eq
    have e1 : φ₀ P = ptCastOfEq hE2 (Point.vcInvFun E (E₀.fullKernelQuotient Q 2).toAffine (φ P)) := rfl
    rw [e1, ptCoords_ptCastOfEq, ptCoords_vcInvFun, hφ2 P, ptCoords_equivOfVariableChangeEq, invCoords_fwdCoords]
  have hφ₀ : ⇑φ₀ = veluPointMap2 h2k h₁'.1 hgy' hΔ'' := funext hφ₀P

  have hπQ' : π (.some x₁ y₁ h₁') = 0 := by rw [← hQpt]; exact hπQ
  obtain ⟨γ₁, hγ₁, hfac⟩ :=
    exists_variableChange_smul_eq_veluQuotient2_forall_apply_eq_of_comp_self_add_two_smul_eq_smul' h2k E₀ hπmem
      2 hchar hirr h₁' hgy' hΔ'' hπQ' φ₀ hφ₀
  have hE0 : (γ₁⁻¹ * E) • E₀.fullKernelQuotient Q 2 = E₀ := by rw [mul_smul, hE2, ← hγ₁, inv_smul_smul]
  refine ⟨γ₁⁻¹ * E, hE0, fun T hT => ?_⟩
  have hMπ : M • π T = 0 := by
    have hMT : M • T ∈ H.1 := H.1.nsmul_mem hT M
    have hsMT : ((2 : ℕ) : ℤ) • (M • T) = 0 := by
      rw [natCast_zsmul, ← mul_nsmul, ← H.2.2]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (H.1.addOrderOf_dvd_natCard hT)
    obtain ⟨d, hd⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (mem_zmultiples_of_smul_eq_zero H.2.1 hM hs0 H.2.2 hQ hQord hMT hsMT)
    rw [← map_nsmul, ← hd, map_zsmul, hπQ, zsmul_zero]
  obtain ⟨T', hT', hπT⟩ := exists_eq_smul_of_smul_eq_zero H.2.1 hM H.2.2 (hπH T hT) hMπ
  refine ⟨T', hT', ?_⟩
  rw [heq_iff_ptCoords_eq hE0, ptCoords_vcInvFun, invCoords_mul, invCoords_inv, hφ2 T,
    ptCoords_equivOfVariableChangeEq, invCoords_fwdCoords, ← hφ₀P T, ← ptCoords_equivOfVariableChangeEq hγ₁ (φ₀ T),
    ← hfac T, ← hπT]

end EngineTwo

end Absorption

section AutCount

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

section Quarry

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K]

private abbrev Aut (W : WeierstrassCurve K) : Subgroup (VariableChange K) :=
  MulAction.stabilizer (VariableChange K) W

omit [DecidableEq K] in
private theorem smul_eq_of_mem_Aut {W : WeierstrassCurve K} (γ : Aut W) : (γ : VariableChange K) • W = W :=
  MulAction.mem_stabilizer_iff.mp γ.2

section Two

private abbrev modelTwo (K : Type*) [Field K] : WeierstrassCurve K := ⟨0, 0, 1, 0, 0⟩

omit [DecidableEq K] in
private theorem two_eq_zero'' [CharP K 2] : (2 : K) = 0 := by
  have := CharP.cast_eq_zero K 2
  exact_mod_cast this

omit [DecidableEq K] in

private theorem smul_modelTwo_eq_iff [CharP K 2] (γ : VariableChange K) :
    γ • modelTwo K = modelTwo K ↔
      ((γ.u : K)) ^ 3 = 1 ∧ γ.r = γ.s ^ 2 ∧ γ.s = γ.r ^ 2 ∧ γ.t ^ 2 + γ.t = γ.r ^ 3 := by
  have h2 : (2 : K) = 0 := two_eq_zero''
  have hw : ((γ.u⁻¹ : Kˣ) : K) * (γ.u : K) = 1 := Units.inv_mul γ.u
  have hwne : ((γ.u⁻¹ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  constructor
  · intro h
    have h₂ := congrArg WeierstrassCurve.a₂ h
    have h₃ := congrArg WeierstrassCurve.a₃ h
    have h₄ := congrArg WeierstrassCurve.a₄ h
    have h₆ := congrArg WeierstrassCurve.a₆ h
    rw [variableChange_a₂] at h₂
    rw [variableChange_a₃] at h₃
    rw [variableChange_a₄] at h₄
    rw [variableChange_a₆] at h₆
    simp only at h₂ h₃ h₄ h₆
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (-((γ.u : K)) ^ 3) * h₃
        + (1 + 2 * γ.t) * (((γ.u⁻¹ : Kˣ) : K) ^ 2 * ((γ.u : K)) ^ 2 + ((γ.u⁻¹ : Kˣ) : K) * (γ.u : K) + 1) * hw
        + γ.t * h2
    · rcases mul_eq_zero.mp h₂ with h' | h'
      · exact absurd h' (pow_ne_zero _ hwne)
      · linear_combination h' - γ.r * h2
    · rcases mul_eq_zero.mp h₄ with h' | h'
      · exact absurd h' (pow_ne_zero _ hwne)
      · linear_combination -h' + (γ.r ^ 2 - γ.s * γ.t) * h2
    · rcases mul_eq_zero.mp h₆ with h' | h'
      · exact absurd h' (pow_ne_zero _ hwne)
      · linear_combination -h'
  · rintro ⟨hu3, hr, hs, ht⟩
    have hw3 : ((γ.u⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      linear_combination (-(((γ.u⁻¹ : Kˣ) : K)) ^ 3) * hu3
        + (((γ.u⁻¹ : Kˣ) : K) ^ 2 * ((γ.u : K)) ^ 2 + ((γ.u⁻¹ : Kˣ) : K) * (γ.u : K) + 1) * hw
    rw [WeierstrassCurve.ext_iff]
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆,
      modelTwo]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linear_combination ((γ.u⁻¹ : Kˣ) : K) * γ.s * h2
    · linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 2 * (hr + γ.r * h2)
    · linear_combination hw3 + ((γ.u⁻¹ : Kˣ) : K) ^ 3 * γ.t * h2
    · linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 4 * (-hs + (γ.r ^ 2 - γ.s * γ.t) * h2)
    · linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 6 * (-ht)

omit [DecidableEq K] in
private def cubeRootsEquiv : {u : Kˣ // ((u : K)) ^ 3 = 1} ≃ rootsOfUnity 3 K :=
  Equiv.subtypeEquivRight fun u => by
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]

omit [DecidableEq K] in

private theorem natCard_cubeRoots_dvd : Nat.card {u : Kˣ // ((u : K)) ^ 3 = 1} ∣ 3 := by
  rw [Nat.card_congr (cubeRootsEquiv (K := K))]
  have hexp : Monoid.exponent (rootsOfUnity 3 K) ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun ζ =>
      Subtype.ext (by simpa using (mem_rootsOfUnity 3 ζ.1).mp ζ.2)
  exact (IsCyclic.exponent_eq_card (α := rootsOfUnity 3 K)) ▸ hexp

private def fourthFixedEquiv : {r : K // r ^ 4 = r} ≃ {u : Kˣ // ((u : K)) ^ 3 = 1} ⊕ Unit where
  toFun r :=
    if h : (r : K) = 0 then Sum.inr () else
      Sum.inl ⟨Units.mk0 (r : K) h, by
        have hr : (r : K) ^ 4 = (r : K) := r.2
        have hfac : (r : K) * ((r : K) ^ 3 - 1) = 0 := by linear_combination hr
        rcases mul_eq_zero.mp hfac with h' | h'
        · exact absurd h' h
        · rw [Units.val_mk0]
          exact sub_eq_zero.mp h'⟩
  invFun p :=
    match p with
    | Sum.inl u => ⟨(u.1 : K), by
        have h3 : ((u.1 : K)) ^ 3 = 1 := u.2
        calc ((u.1 : K)) ^ 4 = ((u.1 : K)) ^ 3 * (u.1 : K) := by ring
          _ = (u.1 : K) := by rw [h3, one_mul]⟩
    | Sum.inr _ => ⟨0, by simp⟩
  left_inv r := by
    by_cases h : (r : K) = 0
    · simp only [h, dite_true]
      exact Subtype.ext h.symm
    · simp only [h, dite_false]
      exact Subtype.ext (by simp)
  right_inv p := by
    rcases p with u | u
    · have hne : (u.1 : K) ≠ 0 := u.1.ne_zero
      simp only [hne, dite_false]
      congr 1
      exact Subtype.ext (Units.ext (by simp))
    · simp

private theorem natCard_fourthFixed_dvd : Nat.card {r : K // r ^ 4 = r} ∣ 4 := by
  haveI : Finite {u : Kˣ // ((u : K)) ^ 3 = 1} := Finite.of_equiv _ (cubeRootsEquiv (K := K)).symm
  have hdvd : Nat.card {u : Kˣ // ((u : K)) ^ 3 = 1} ∣ 3 := natCard_cubeRoots_dvd
  have h1 : Nat.card Unit = 1 := Nat.card_unique
  rw [Nat.card_congr (fourthFixedEquiv (K := K)), Nat.card_sum, h1]
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;> rw [h] <;> norm_num

omit [DecidableEq K] in

private theorem exists_root_quadratic [IsAlgClosed K] (c : K) : ∃ t : K, t ^ 2 + t = c := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c : Polynomial K)
    (by
      have hdeg : (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c : Polynomial K).degree = 2 := by
        compute_degree!
      rw [hdeg]
      decide)
  refine ⟨t, ?_⟩
  rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at ht
  linear_combination ht

omit [DecidableEq K] in

private theorem eq_or_eq_add_one_of_sq_add [CharP K 2] {c t₀ t : K} (h₀ : t₀ ^ 2 + t₀ = c)
    (h : t ^ 2 + t = c) : t = t₀ ∨ t = t₀ + 1 := by
  have h2 : (2 : K) = 0 := two_eq_zero''
  have hfac : (t - t₀) * (t - t₀ - 1) = 0 := by
    linear_combination h - h₀ + (t₀ ^ 2 + t₀ - t * t₀ - t) * h2
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (by linear_combination h')

omit [DecidableEq K] in
private theorem ne_add_one' (x : K) : x ≠ x + 1 := by
  intro h
  have : (1 : K) = 0 := by linear_combination -h
  exact one_ne_zero this

private noncomputable def root0 [IsAlgClosed K] (c : K) : K :=
  Classical.choose (exists_root_quadratic (K := K) c)

omit [DecidableEq K] in
private theorem root0_spec [IsAlgClosed K] (c : K) : root0 (K := K) c ^ 2 + root0 (K := K) c = c :=
  Classical.choose_spec (exists_root_quadratic (K := K) c)

private noncomputable def autModelTwoEquiv [CharP K 2] [IsAlgClosed K] :
    Aut (modelTwo K) ≃ ({u : Kˣ // ((u : K)) ^ 3 = 1} × {r : K // r ^ 4 = r}) × Bool where
  toFun γ :=
    ((⟨γ.1.u, ((smul_modelTwo_eq_iff γ.1).mp (smul_eq_of_mem_Aut γ)).1⟩,
      ⟨γ.1.r, by
        obtain ⟨-, hr, hs, -⟩ := (smul_modelTwo_eq_iff γ.1).mp (smul_eq_of_mem_Aut γ)
        calc γ.1.r ^ 4 = (γ.1.r ^ 2) ^ 2 := by ring
          _ = γ.1.r := by rw [← hs, ← hr]⟩),
      decide (γ.1.t = root0 (K := K) (γ.1.r ^ 3) + 1))
  invFun := fun ⟨⟨u, r⟩, b⟩ =>
    ⟨⟨u.1, r.1, r.1 ^ 2, if b then root0 (K := K) (r.1 ^ 3) + 1 else root0 (K := K) (r.1 ^ 3)⟩,
      MulAction.mem_stabilizer_iff.mpr ((smul_modelTwo_eq_iff _).mpr ⟨u.2, by
        show r.1 = (r.1 ^ 2) ^ 2
        calc r.1 = r.1 ^ 4 := r.2.symm
          _ = (r.1 ^ 2) ^ 2 := by ring, rfl, by
        have h2 : (2 : K) = 0 := two_eq_zero''
        have h0 := root0_spec (K := K) (r.1 ^ 3)
        cases b
        · show root0 (K := K) (r.1 ^ 3) ^ 2 + root0 (K := K) (r.1 ^ 3) = r.1 ^ 3
          exact h0
        · show (root0 (K := K) (r.1 ^ 3) + 1) ^ 2 + (root0 (K := K) (r.1 ^ 3) + 1) = r.1 ^ 3
          linear_combination h0 + (root0 (K := K) (r.1 ^ 3) + 1) * h2⟩)⟩
  left_inv γ := by
    obtain ⟨-, -, hs, ht⟩ := (smul_modelTwo_eq_iff γ.1).mp (smul_eq_of_mem_Aut γ)
    refine Subtype.ext (VariableChange.ext rfl rfl hs.symm ?_)
    show (if decide (γ.1.t = root0 (K := K) (γ.1.r ^ 3) + 1) = true then root0 (K := K) (γ.1.r ^ 3) + 1
        else root0 (K := K) (γ.1.r ^ 3)) = γ.1.t
    rcases eq_or_eq_add_one_of_sq_add (root0_spec (K := K) (γ.1.r ^ 3)) ht with h | h
    · have hb : decide (γ.1.t = root0 (K := K) (γ.1.r ^ 3) + 1) = false :=
        decide_eq_false (by rw [h]; exact ne_add_one' _)
      rw [hb]
      exact h.symm
    · have hb : decide (γ.1.t = root0 (K := K) (γ.1.r ^ 3) + 1) = true := decide_eq_true h
      rw [hb]
      exact h.symm
  right_inv := fun ⟨⟨u, r⟩, b⟩ => by
    refine Prod.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)) ?_
    cases b
    · show decide (root0 (K := K) (r.1 ^ 3) = root0 (K := K) (r.1 ^ 3) + 1) = false
      exact decide_eq_false (ne_add_one' _)
    · show decide (root0 (K := K) (r.1 ^ 3) + 1 = root0 (K := K) (r.1 ^ 3) + 1) = true
      exact decide_eq_true rfl

private theorem natCard_aut_modelTwo_dvd [CharP K 2] [IsAlgClosed K] : Nat.card (Aut (modelTwo K)) ∣ 24 := by
  rw [Nat.card_congr (autModelTwoEquiv (K := K)), Nat.card_prod, Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  have h : (24 : ℕ) = 3 * 4 * 2 := by norm_num
  rw [h]
  exact Nat.mul_dvd_mul (Nat.mul_dvd_mul natCard_cubeRoots_dvd natCard_fourthFixed_dvd) (dvd_refl 2)

omit [DecidableEq K] in

private theorem natCard_cubeRoots_eq [CharP K 2] [IsAlgClosed K] :
    Nat.card {u : Kˣ // ((u : K)) ^ 3 = 1} = 3 := by
  haveI : NeZero ((3 : ℕ) : K) := ⟨by
    have h2 : (2 : K) = 0 := two_eq_zero''
    have h3 : ((3 : ℕ) : K) = 1 := by push_cast; linear_combination h2
    rw [h3]; exact one_ne_zero⟩
  rw [Nat.card_congr (cubeRootsEquiv (K := K))]
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity K 3

private theorem natCard_fourthFixed_eq [CharP K 2] [IsAlgClosed K] : Nat.card {r : K // r ^ 4 = r} = 4 := by
  haveI : Finite {u : Kˣ // ((u : K)) ^ 3 = 1} := Finite.of_equiv _ (cubeRootsEquiv (K := K)).symm
  have h1 : Nat.card Unit = 1 := Nat.card_unique
  rw [Nat.card_congr (fourthFixedEquiv (K := K)), Nat.card_sum, h1, natCard_cubeRoots_eq]

private theorem natCard_stabilizer_modelTwo [CharP K 2] [IsAlgClosed K] :
    Nat.card (MulAction.stabilizer (VariableChange K) (modelTwo K)) = 24 := by
  change Nat.card (Aut (modelTwo K)) = 24
  rw [Nat.card_congr (autModelTwoEquiv (K := K)), Nat.card_prod, Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, natCard_cubeRoots_eq, natCard_fourthFixed_eq]

end Two

section Three

private abbrev modelThree (K : Type*) [Field K] : WeierstrassCurve K := ⟨0, 0, 0, -1, 0⟩

omit [DecidableEq K] in
private theorem three_eq_zero' [CharP K 3] : (3 : K) = 0 := by
  have := CharP.cast_eq_zero K 3
  exact_mod_cast this

omit [DecidableEq K] in
private theorem two_ne_zero' [CharP K 3] : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K 3] at h'
  omega

omit [DecidableEq K] in

private theorem smul_modelThree_eq_iff [CharP K 3] (γ : VariableChange K) :
    γ • modelThree K = modelThree K ↔
      γ.s = 0 ∧ γ.t = 0 ∧ ((γ.u : K)) ^ 4 = 1 ∧ γ.r ^ 3 = γ.r := by
  have hu : (γ.u : K) ≠ 0 := γ.u.ne_zero
  have h3 : (3 : K) = 0 := three_eq_zero'
  have h2 : (2 : K) ≠ 0 := two_ne_zero'
  rw [WeierstrassCurve.ext_iff]
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆,
    Units.val_inv_eq_inv_val, h3]

  simp only [zero_add, add_zero, mul_zero, zero_mul, sub_zero, zero_sub, mul_one, mul_neg]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₆⟩
    have hs : γ.s = 0 := by
      have := h₁
      field_simp at this
      rcases mul_eq_zero.mp (by linear_combination this : (2 : K) * γ.s = 0) with h | h
      · exact absurd h h2
      · exact h
    have ht : γ.t = 0 := by
      have := h₃
      field_simp at this
      rcases mul_eq_zero.mp (by linear_combination this : (2 : K) * γ.t = 0) with h | h
      · exact absurd h h2
      · exact h
    refine ⟨hs, ht, ?_, ?_⟩
    · have := h₄
      rw [hs, ht] at this
      field_simp at this
      linear_combination this
    · have := h₆
      rw [ht] at this
      field_simp at this
      linear_combination this
  · rintro ⟨hs, ht, hu4, hr⟩
    rw [hs, ht]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · field_simp
      rw [hu4]
      ring
    · field_simp
      linear_combination hr

private def autModelThreeEquiv [CharP K 3] :
    Aut (modelThree K) ≃ {u : Kˣ // ((u : K)) ^ 4 = 1} × {r : K // r ^ 3 = r} where
  toFun γ :=
    (⟨γ.1.u, ((smul_modelThree_eq_iff γ.1).mp (smul_eq_of_mem_Aut γ)).2.2.1⟩,
      ⟨γ.1.r, ((smul_modelThree_eq_iff γ.1).mp (smul_eq_of_mem_Aut γ)).2.2.2⟩)
  invFun p :=
    ⟨⟨p.1.1, p.2.1, 0, 0⟩, MulAction.mem_stabilizer_iff.mpr
      ((smul_modelThree_eq_iff _).mpr ⟨rfl, rfl, p.1.2, p.2.2⟩)⟩
  left_inv γ := by
    obtain ⟨hs, ht, -, -⟩ := (smul_modelThree_eq_iff γ.1).mp (smul_eq_of_mem_Aut γ)
    exact Subtype.ext (VariableChange.ext rfl rfl hs.symm ht.symm)
  right_inv p := rfl

omit [DecidableEq K] in

private theorem natCard_fourthRoots_dvd : Nat.card {u : Kˣ // ((u : K)) ^ 4 = 1} ∣ 4 := by
  have e : {u : Kˣ // ((u : K)) ^ 4 = 1} ≃ rootsOfUnity 4 K :=
    Equiv.subtypeEquivRight fun u => by
      rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
  rw [Nat.card_congr e]
  have hexp : Monoid.exponent (rootsOfUnity 4 K) ∣ 4 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun ζ =>
      Subtype.ext (by simpa using (mem_rootsOfUnity 4 ζ.1).mp ζ.2)
  exact (IsCyclic.exponent_eq_card (α := rootsOfUnity 4 K)) ▸ hexp

omit [DecidableEq K] in

private theorem natCard_cubeRoots [CharP K 3] : Nat.card {r : K // r ^ 3 = r} = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let φ : ZMod 3 → {r : K // r ^ 3 = r} := fun z =>
    ⟨ZMod.castHom (dvd_refl 3) K z, by
      rw [← map_pow, ZMod.pow_card z]⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      exact ZMod.castHom_injective K (congrArg Subtype.val hab)
    · rintro ⟨r, hr⟩
      have h3 : (3 : K) = 0 := three_eq_zero'
      have hfac : r * (r - 1) * (r + 1) = 0 := by linear_combination hr
      rcases mul_eq_zero.mp hfac with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact ⟨0, Subtype.ext (by simp [φ, h])⟩
        · exact ⟨1, Subtype.ext (by simp [φ, sub_eq_zero.mp h])⟩
      · refine ⟨2, Subtype.ext ?_⟩
        have hr' : r = -1 := by linear_combination h
        simp only [φ, map_ofNat]
        rw [hr']
        linear_combination h3
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_zmod]

omit [DecidableEq K] in

private theorem natCard_aut_modelThree_dvd [CharP K 3] : Nat.card (Aut (modelThree K)) ∣ 12 := by
  rw [Nat.card_congr autModelThreeEquiv, Nat.card_prod, natCard_cubeRoots]
  exact Nat.mul_dvd_mul_right natCard_fourthRoots_dvd 3

omit [DecidableEq K] in

private theorem natCard_fourthRoots_eq [CharP K 3] [IsAlgClosed K] :
    Nat.card {u : Kˣ // ((u : K)) ^ 4 = 1} = 4 := by
  haveI : NeZero ((4 : ℕ) : K) := ⟨by
    have h3 : (3 : K) = 0 := three_eq_zero'
    have h4 : ((4 : ℕ) : K) = 1 := by push_cast; linear_combination h3
    rw [h4]; exact one_ne_zero⟩
  have e : {u : Kˣ // ((u : K)) ^ 4 = 1} ≃ rootsOfUnity 4 K :=
    Equiv.subtypeEquivRight fun u => by
      rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
  rw [Nat.card_congr e]
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity K 4

omit [DecidableEq K] in

private theorem natCard_stabilizer_modelThree [CharP K 3] [IsAlgClosed K] :
    Nat.card (MulAction.stabilizer (VariableChange K) (modelThree K)) = 12 := by
  change Nat.card (Aut (modelThree K)) = 12
  rw [Nat.card_congr autModelThreeEquiv, Nat.card_prod, natCard_cubeRoots, natCard_fourthRoots_eq]

end Three

end Quarry

section Models

variable {K : Type*} [Field K]

private theorem modelTwo_Δ [CharP K 2] : (modelTwo K).Δ = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]
  linear_combination (-14 : K) * h2

private scoped instance instIsEllipticModelTwo [CharP K 2] : (modelTwo K).IsElliptic :=
  ⟨by rw [modelTwo_Δ]; exact isUnit_one⟩

private theorem modelTwo_j [CharP K 2] : (modelTwo K).j = 0 := by
  simp [WeierstrassCurve.j, c₄, b₂, b₄]

private theorem modelThree_Δ [CharP K 3] : (modelThree K).Δ = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]
  linear_combination (21 : K) * h3

private scoped instance instIsEllipticModelThree [CharP K 3] : (modelThree K).IsElliptic :=
  ⟨by rw [modelThree_Δ]; exact isUnit_one⟩

private theorem modelThree_j [CharP K 3] : (modelThree K).j = 0 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h24 : (24 : K) = 0 := by linear_combination (8 : K) * h3
  simp [WeierstrassCurve.j, c₄, b₂, b₄, h24]

private theorem natCard_stabilizer_eq_of_smul_eq {W W' : WeierstrassCurve K} (γ : VariableChange K)
    (h : γ • W = W') :
    Nat.card (MulAction.stabilizer (VariableChange K) W') = Nat.card (MulAction.stabilizer (VariableChange K) W) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (G := VariableChange K) h.symm).toEquiv).symm

end Models

private theorem natCard_stabilizer_variableChange_eq_two_mul_jWidthChar
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (q' : ℕ) [Fact q'.Prime] [CharP k q']
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] :
    Nat.card (MulAction.stabilizer (VariableChange k) E₀) = 2 * jWidthChar q' E₀.j := by
  have hchar : ringChar k = q' := ringChar.eq k q'
  rcases eq_or_ne q' 2 with rfl | hq2
  ·
    by_cases hj : E₀.j = 0
    · obtain ⟨C, hC⟩ := exists_variableChange_of_j_eq (modelTwo k) E₀ (by rw [modelTwo_j, hj])
      rw [natCard_stabilizer_eq_of_smul_eq C hC, natCard_stabilizer_modelTwo, jWidthChar_two_of_eq_zero hj]
    · rw [natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three (Or.inl hchar) E₀ hj,
        jWidthChar_two_of_ne_zero hj]
  rcases eq_or_ne q' 3 with rfl | hq3
  ·
    by_cases hj : E₀.j = 0
    · obtain ⟨C, hC⟩ := exists_variableChange_of_j_eq (modelThree k) E₀ (by rw [modelThree_j, hj])
      rw [natCard_stabilizer_eq_of_smul_eq C hC, natCard_stabilizer_modelThree, jWidthChar_three_of_eq_zero hj]
    · rw [natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three (Or.inr hchar) E₀ hj,
        jWidthChar_three_of_ne_zero hj]

  rw [jWidthChar_of_ne hq2 hq3, card_stabilizer_variableChange_eq_two_mul_jWidth (by rw [hchar]; exact hq2)
    (by rw [hchar]; exact hq3) E₀]

end AutCount

section Currency

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

private theorem placeRamificationJ_dvd_jWidthChar_of_pos
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (q' : ℕ) [Fact q'.Prime] [CharP k q']
    (N : ℕ) [NeZero N] (hN : ¬ q' ∣ N)
    (p : Place k ↥(modularFunctionFieldC k N)) (hp : 0 < placeRamificationJ N p) :
    placeRamificationJ N p ∣ jWidthChar q' (p.evalAt (jGeomGen k N)) := by
  have hq : q'.Prime := Fact.out
  by_cases hq5 : 5 ≤ q'
  · rw [jWidthChar_of_five_le hq5]
    exact placeRamificationJ_dvd_jWidth_of_ord_pos hq5 hN hp
  · have hlt : q' < 5 := not_le.mp hq5
    have h4 : q' ≠ 4 := fun h => by subst h; exact absurd hq (by decide)
    have h2 := hq.two_le

    have haff : IsAffineGeomPlace k N p := by
      by_contra hcon
      have hpole : p.ord (jGeomGen k N) < 0 :=
        (isAffineGeomPlace_or_ord_jGeomGen_lt_zero k N p).resolve_left hcon
      have hneg :
          p.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (p.evalAt (jGeomGen k N))) < 0 := by
        by_contra hcon'
        have hmem := p.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N _) (not_lt.mp hcon')
        have hj : jGeomGen k N ∈ p.toValuationSubring := by
          have := add_mem hmem (p.algebraMap_mem' (p.evalAt (jGeomGen k N)))
          simpa using this
        exact absurd (p.ord_nonneg_of_mem hj) (not_le.mpr hpole)
      unfold placeRamificationJ at hp
      omega
    have hrat : p.IsRational :=
      (Place.isRational_iff_deg_eq_one p).mpr (place_deg_eq_one_of_isAlgClosed k N p)
    by_cases hj : p.evalAt (jGeomGen k N) = 0
    ·
      have hss : p ∈ ssPlaces q' N k := by
        show IsSupersingularPlace q' N k p
        refine ⟨hrat, haff, ?_⟩
        rw [hj]
        exact zero_mem_ssJSet_of_lt_five hlt
      obtain rfl | rfl : q' = 2 ∨ q' = 3 := by omega
      · exact placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces hN hss
      · exact placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces hN hss
    ·
      have h1728 : (1728 : k) = 0 := by
        obtain rfl | rfl : q' = 2 ∨ q' = 3 := by omega
        · exact_mod_cast (CharP.cast_eq_zero_iff k 2 1728).mpr (by norm_num)
        · exact_mod_cast (CharP.cast_eq_zero_iff k 3 1728).mpr (by norm_num)
      have h := ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq q' k N hN p _ rfl hj (by rw [h1728]; exact hj)
      have h1 : placeRamificationJ N p = 1 := by
        unfold placeRamificationJ
        rw [h]
        rfl
      rw [h1]
      exact one_dvd _

end Currency

section OrbitStabiliser

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

private theorem natCard_stabilizer_eq_natCard_orbit_mul_natCard_pairStabilizer
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0)
    (H : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    Nat.card (MulAction.stabilizer (VariableChange k) E₀) =
      Nat.card {H' : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} //
          ∃ γ : VariableChange k, γ • E₀ = E₀ ∧
            ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'} *
        Nat.card {γ : VariableChange k // γ • E₀ = E₀ ∧
          ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'} := by
  have _ := hN
  have hfin : ∀ H' : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}, Finite H'.1 :=
    fun H' => Nat.finite_of_card_ne_zero (by rw [H'.2.2]; exact NeZero.ne N)
  haveI : Finite H.1 := hfin H
  haveI : IsAddCyclic H.1 := H.2.1

  have horb : ∀ K ∈ MulAction.orbit (MulAction.stabilizer (VariableChange k) E₀) H.1,
      (IsAddCyclic K ∧ Nat.card K = N) ∧ ∃ γ : VariableChange k, γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ K, HEq (Point.vcInvFun γ E₀.toAffine T) T' := by
    intro K hK
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp hK
    have hc : Nat.card ↥(γ • H.1) = N := (natCard_stabSmul E₀ γ H.1).trans H.2.2
    haveI : Finite ↥(γ • H.1) := Nat.finite_of_card_ne_zero (by rw [hc]; exact NeZero.ne N)
    exact ⟨⟨isAddCyclic_stabSmul E₀ γ H.1, hc⟩, γ, MulAction.mem_stabilizer_iff.mp γ.2,
      (stabSmul_eq_iff E₀ γ H.1 (γ • H.1) (H.2.2.trans hc.symm)).mp rfl⟩
  have hback : ∀ H' : {H' : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} //
      ∃ γ : VariableChange k, γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'},
      H'.1.1 ∈ MulAction.orbit (MulAction.stabilizer (VariableChange k) E₀) H.1 := by
    intro H'
    obtain ⟨γ, hγ, hcar⟩ := H'.2
    haveI : Finite H'.1.1 := hfin H'.1
    exact MulAction.mem_orbit_iff.mpr ⟨⟨γ, MulAction.mem_stabilizer_iff.mpr hγ⟩,
      (stabSmul_eq_iff E₀ ⟨γ, MulAction.mem_stabilizer_iff.mpr hγ⟩ H.1 H'.1.1 (H.2.2.trans H'.1.2.2.symm)).mpr hcar⟩
  have e3 : MulAction.orbit (MulAction.stabilizer (VariableChange k) E₀) H.1 ≃
      {H' : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} //
          ∃ γ : VariableChange k, γ • E₀ = E₀ ∧
            ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'} :=
    { toFun := fun K => ⟨⟨K.1, (horb K.1 K.2).1⟩, (horb K.1 K.2).2⟩
      invFun := fun H' => ⟨H'.1.1, hback H'⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

  have e4 : MulAction.stabilizer (MulAction.stabilizer (VariableChange k) E₀) H.1 ≃
      {γ : VariableChange k // γ • E₀ = E₀ ∧
          ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'} :=
    { toFun := fun γ => ⟨((γ : MulAction.stabilizer (VariableChange k) E₀) : VariableChange k),
        MulAction.mem_stabilizer_iff.mp (γ : MulAction.stabilizer (VariableChange k) E₀).2,
        (stabSmul_eq_iff E₀ (γ : MulAction.stabilizer (VariableChange k) E₀) H.1 H.1 rfl).mp
          (MulAction.mem_stabilizer_iff.mp γ.2)⟩
      invFun := fun γ => ⟨⟨γ.1, MulAction.mem_stabilizer_iff.mpr γ.2.1⟩,
        MulAction.mem_stabilizer_iff.mpr
          ((stabSmul_eq_iff E₀ ⟨γ.1, MulAction.mem_stabilizer_iff.mpr γ.2.1⟩ H.1 H.1 rfl).mpr γ.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MulAction.stabilizer (MulAction.stabilizer (VariableChange k) E₀) H.1),
    ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (MulAction.stabilizer (VariableChange k) E₀) H.1),
    Nat.card_congr e3, Nat.card_congr e4]

end OrbitStabiliser

section Assembly

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

private theorem natCard_map_mul_natCard_inf_ker (ψ : A →+ B) (H : AddSubgroup A) :
    Nat.card (H.map ψ) * Nat.card ↥(H ⊓ ψ.ker) = Nat.card H := by
  have hrange : (ψ.comp H.subtype).range = H.map ψ := by
    rw [← AddMonoidHom.map_range, AddSubgroup.range_subtype]
  have hker : (ψ.comp H.subtype).ker = ψ.ker.addSubgroupOf H := (AddMonoidHom.comap_ker ψ H.subtype).symm
  have h1 : Nat.card H = Nat.card (H ⧸ (ψ.comp H.subtype).ker) * Nat.card (ψ.comp H.subtype).ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h2 : Nat.card (H ⧸ (ψ.comp H.subtype).ker) = Nat.card (H.map ψ) := by
    rw [← hrange]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (ψ.comp H.subtype)).toEquiv
  have h3 : Nat.card (ψ.comp H.subtype).ker = Nat.card ↥(ψ.ker ⊓ H) := by
    rw [hker, ← AddSubgroup.addSubgroupOf_map_subtype, AddSubgroup.card_map_of_injective H.subtype_injective]
  rw [h1, h2, h3, inf_comm]

private theorem isAddCyclic_map (ψ : A →+ B) (H : AddSubgroup A) [IsAddCyclic H] : IsAddCyclic (H.map ψ) := by
  have hrange : (ψ.comp H.subtype).range = H.map ψ := by
    rw [← AddMonoidHom.map_range, AddSubgroup.range_subtype]
  rw [← hrange]
  exact isAddCyclic_of_surjective _ (AddMonoidHom.rangeRestrict_surjective (ψ.comp H.subtype))

private theorem restrictAlong_eq_restrictAlong_of_placeWidthChar_ne_one
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
    (p : Place k ↥(modularFunctionFieldC k (M * s)))
    (hr : 0 < placeRamificationJ (M * s) p) (hw : placeWidthChar q' (M * s) p ≠ 1) :
    Place.restrictAlong (φ 1) (hφ 1) p = Place.restrictAlong (φ 0) (hφ 0) p := by
  have hq' : q'.Prime := Fact.out
  have hq'Ms : ¬ q' ∣ M * s := fun h =>
    (hq'.dvd_mul.mp h).elim hq'M fun h' => hsq' ((Nat.prime_dvd_prime_iff_eq hq' hs).mp h').symm
  have hMs : ((M * s : ℕ) : k) ≠ 0 := fun h => hq'Ms ((CharP.cast_eq_zero_iff k q' (M * s)).mp h)
  have hsk : ((s : ℕ) : k) ≠ 0 := fun h => hMs (by rw [Nat.cast_mul, h, mul_zero])
  have hM : M ≠ 0 := NeZero.ne M

  set j₀ : k := p.evalAt (jGeomGen k (M * s)) with hj₀
  obtain ⟨E₀, hell, hE₀⟩ : ∃ (E₀ : WeierstrassCurve k) (_ : E₀.IsElliptic), E₀.j = j₀ :=
    ⟨WeierstrassCurve.ofJ j₀, inferInstance, WeierstrassCurve.ofJ_j j₀⟩
  haveI := hell

  have hroof : charLDegeneracyRoof k M s = modularFunctionFieldC k (M * s) :=
    (charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q' M s hq'Ms).trans
      (modularFunctionFieldC_eq_modularFunctionFieldFullC k q' (M * s) hq'Ms).symm
  have hD := fun (hα : (heckeAlphaC k M s).toRingHom.IsIntegral) (hβ : (heckeBetaC k M s).toRingHom.IsIntegral) =>
    exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq k M s hs hMs hα hβ j₀ E₀ hE₀
  have hA : ∀ x : ↥(modularFunctionFieldC k M),
      ((heckeAlphaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) = x := by
    intro x
    simp
  have hB : ∀ x : ↥(modularFunctionFieldC k M),
      ((heckeBetaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) = qExpand k s x := by
    intro x
    simp
  generalize heckeAlphaC k M s = α at hD hA
  generalize heckeBetaC k M s = β at hD hB
  generalize charLDegeneracyRoof k M s = R at hroof α β hD hA hB
  subst hroof
  obtain rfl : α = φ 0 := AlgHom.ext fun x => Subtype.ext ((hA x).trans (hφα x).symm)
  obtain rfl : β = φ 1 := AlgHom.ext fun x => Subtype.ext ((hB x).trans (hφβ x).symm)
  obtain ⟨g, f, -, -, hg3, -, -, hf2, hf3, hf4, hfα, hfβ, hfβ'⟩ := hD (hφ 0) (hφ 1)

  have hjg : φ 0 (jGeomGen k M) = jGeomGen k (M * s) :=
    Subtype.ext (by rw [hφα, coe_jGeomGen, coe_jGeomGen])

  have he_def : placeRamificationJ (M * s) p =
      (p.ord (jGeomGen k (M * s) - algebraMap k ↥(modularFunctionFieldC k (M * s)) j₀)).toNat := rfl
  have hpos : 0 < p.ord (jGeomGen k (M * s) - algebraMap k ↥(modularFunctionFieldC k (M * s)) j₀) := by
    have h := hr
    rw [he_def] at h
    exact_mod_cast Int.lt_toNat.mp h
  obtain ⟨H, hH⟩ := hf2 p (by rw [hjg]; exact hpos)
  have he : placeRamificationJ (M * s) p = Nat.card {C' // f C' = f H} := by
    have h4 := hf4 H
    rw [hjg] at h4
    have h : ((placeRamificationJ (M * s) p : ℕ) : ℤ) = Nat.card {C' // f C' = f H} := by
      rw [he_def, Int.toNat_of_nonneg hpos.le, ← h4, hH]
    exact_mod_cast h
  have hFib : Nat.card {C' // f C' = f H} =
      Nat.card {H' : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s} //
        ∃ γ : VariableChange k, γ • E₀ = E₀ ∧
          ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun C' => eq_comm.trans (hf3 H C'))

  have hC4 := natCard_stabilizer_eq_natCard_orbit_mul_natCard_pairStabilizer E₀ (M * s) hMs H
  have hC3 := natCard_stabilizer_variableChange_eq_two_mul_jWidthChar q' E₀
  rw [hE₀] at hC3
  rw [hC3, ← hFib, ← he] at hC4
  have hcur := placeRamificationJ_dvd_jWidthChar_of_pos q' (M * s) hq'Ms p hr
  have hwpos : 0 < jWidthChar q' j₀ := jWidthChar_pos q' j₀
  have hew : placeRamificationJ (M * s) p ≠ jWidthChar q' j₀ := by
    intro h
    apply hw
    show jWidthChar q' j₀ / placeRamificationJ (M * s) p = 1
    rw [h, Nat.div_self hwpos]
  have hlt : placeRamificationJ (M * s) p < jWidthChar q' j₀ := lt_of_le_of_ne (Nat.le_of_dvd hwpos hcur) hew
  have hS : 2 < Nat.card {γ : VariableChange k // γ • E₀ = E₀ ∧
      ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'} := by
    rcases Nat.lt_or_ge 2 (Nat.card {γ : VariableChange k // γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'}) with h | h
    · exact h
    · exfalso
      have h' := Nat.mul_le_mul_left (placeRamificationJ (M * s) p) h
      omega

  haveI : Fact s.Prime := ⟨hs⟩
  haveI hHc : IsAddCyclic H.1 := H.2.1
  haveI : Finite H.1 := Nat.finite_of_card_ne_zero (by rw [H.2.2]; exact mul_ne_zero hM hs.ne_zero)
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := H.1) s (by rw [H.2.2]; exact Dvd.intro_left M rfl)
  have hQ : (x : E₀.toAffine.Point) ∈ H.1 := x.2
  have hQord : addOrderOf (x : E₀.toAffine.Point) = s := (AddSubgroup.addOrderOf_coe x).trans hx
  generalize (x : E₀.toAffine.Point) = Q at hQ hQord
  have hsQ : s • Q = 0 := by
    rw [← hQord]
    exact addOrderOf_nsmul_eq_zero Q
  have hcardQ : Nat.card (AddSubgroup.zmultiples Q) = s := (Nat.card_zmultiples Q).trans hQord
  let ν : E₀.toAffine.Point →+ E₀.toAffine.Point := s • AddMonoidHom.id _
  have hinf : H.1 ⊓ ν.ker = AddSubgroup.zmultiples Q := by
    refine le_antisymm (fun T hT => ?_) (le_inf (AddSubgroup.zmultiples_le.mpr hQ) (AddSubgroup.zmultiples_le.mpr hsQ))
    exact mem_zmultiples_of_smul_eq_zero H.2.1 hM hs.ne_zero H.2.2 hQ hQord hT.1 (by rw [natCast_zsmul]; exact hT.2)
  have hsH_card : Nat.card (H.1.map ν) = M := by
    have h := natCard_map_mul_natCard_inf_ker ν H.1
    rw [hinf, hcardQ, H.2.2] at h
    exact Nat.eq_of_mul_eq_mul_right hs.pos h
  let sH : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M} :=
    ⟨H.1.map ν, isAddCyclic_map ν H.1, hsH_card⟩
  have hsH : ∀ T ∈ H.1, s • T ∈ sH.1 := fun T hT => AddSubgroup.mem_map.mpr ⟨T, hT, rfl⟩
  have hαv : (f H).restrictAlong (φ 0) (hφ 0) = g E₀ sH := hfα H sH hsH

  rcases hs.eq_two_or_odd' with hs2 | hodd
  · subst hs2
    obtain ⟨ρ, hρker, hρ⟩ := exists_fullKernelHom E₀ (N := 2) hsk Q hQord
    have hΔ := fullKernelQuotient_discriminant_ne_zero 2 E₀ hsk Q hQord
    obtain ⟨γ₀, hγ₀, hcar⟩ :=
      exists_variableChange_fullKernelQuotient_two_of_two_lt_natCard_pairStabilizer E₀ M hMs hsM H hS Q hQ hQord hΔ
        ρ hρker hρ
    have hkle : ρ.ker ≤ H.1 := by
      rw [hρker]
      exact AddSubgroup.zmultiples_le.mpr hQ
    have hcard'' : Nat.card (H.1.map ρ) = M := by
      have h := natCard_map_mul_natCard_inf_ker ρ H.1
      rw [inf_eq_right.mpr hkle, hρker, hcardQ, H.2.2] at h
      exact Nat.eq_of_mul_eq_mul_right hs.pos h
    let C'' : {C : AddSubgroup (E₀.fullKernelQuotient Q 2).toAffine.Point // IsAddCyclic C ∧ Nat.card C = M} :=
      ⟨H.1.map ρ, isAddCyclic_map ρ H.1, hcard''⟩
    have hC'' : ∀ T ∈ H.1, ρ T ∈ C''.1 := fun T hT => AddSubgroup.mem_map.mpr ⟨T, hT, rfl⟩
    have hβv := hfβ' H Q hQ hQord hΔ ρ hρker hρ C'' hC''
    haveI : (E₀.fullKernelQuotient Q 2).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    rw [← hH, hβv, hαv]
    refine (hg3 _ E₀ C'' sH).mpr ⟨γ₀, hγ₀, fun T hT => ?_⟩
    obtain ⟨T₀, hT₀, rfl⟩ := AddSubgroup.mem_map.mp hT
    obtain ⟨T', hT', hheq⟩ := hcar T₀ hT₀
    exact ⟨2 • T', hsH T' hT', hheq⟩
  · obtain ⟨n, rfl⟩ := hodd
    obtain ⟨φ₀, hφker, hφ₀⟩ :=
      exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one E₀ n hsk Q hQord
    have hΔ := veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq E₀ n Q hQord
    obtain ⟨γ₀, hγ₀, hcar⟩ :=
      exists_variableChange_veluQuotient_of_two_lt_natCard_pairStabilizer E₀ M n hMs hs hsM H hS Q hQ hQord hΔ φ₀ hφker
        hφ₀
    have hkle : φ₀.ker ≤ H.1 := by
      rw [hφker]
      exact AddSubgroup.zmultiples_le.mpr hQ
    have hcard'' : Nat.card (H.1.map φ₀) = M := by
      have h := natCard_map_mul_natCard_inf_ker φ₀ H.1
      rw [inf_eq_right.mpr hkle, hφker, hcardQ, H.2.2] at h
      exact Nat.eq_of_mul_eq_mul_right hs.pos h
    let C'' : {C : AddSubgroup (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point //
        IsAddCyclic C ∧ Nat.card C = M} :=
      ⟨H.1.map φ₀, isAddCyclic_map φ₀ H.1, hcard''⟩
    have hC'' : ∀ T ∈ H.1, φ₀ T ∈ C''.1 := fun T hT => AddSubgroup.mem_map.mpr ⟨T, hT, rfl⟩
    have hβv := hfβ H n Q rfl hQ hQord hΔ φ₀ hφker hφ₀ C'' hC''
    haveI : (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    rw [← hH, hβv, hαv]
    refine (hg3 _ E₀ C'' sH).mpr ⟨γ₀, hγ₀, fun T hT => ?_⟩
    obtain ⟨T₀, hT₀, rfl⟩ := AddSubgroup.mem_map.mp hT
    obtain ⟨T', hT', hheq⟩ := hcar T₀ hT₀
    exact ⟨(2 * n + 1) • T', hsH T' hT', hheq⟩

end Assembly

end

end CyclicLevelOrbit
p2m_reactivate "P2MW.S_ModularCurve_placeWidthChar_eq_one_of_restrictAlong_ne.CyclicLevelOrbit"

open AlgebraicCurve ModularCurve

theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    ∀ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x),
    ∀ p : Place k ↥(modularFunctionFieldC k (M * s)),
      Place.restrictAlong (φ 1) (hφ 1) p ≠ Place.restrictAlong (φ 0) (hφ 0) p →
      0 < placeRamificationJ (M * s) p →
      placeWidthChar q' (M * s) p = 1 := by
  intro φ hφ hφα hφβ p hne hr
  by_contra hw
  exact hne (CyclicLevelOrbit.restrictAlong_eq_restrictAlong_of_placeWidthChar_ne_one M s q' hs hsq' hq'M hsM φ hφ
    hφα hφβ p hr hw)

end S_ModularCurve_placeWidthChar_eq_one_of_restrictAlong_ne
end P2MW
export P2MW.S_ModularCurve_placeWidthChar_eq_one_of_restrictAlong_ne (solution)
