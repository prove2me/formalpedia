-- Prove2me | solution 1 for ModularCurve.reducedRootFunction_genOpH_T_eq_smul_pow_mul_norm_heckeBetaModLH_of_abelJacobiPin_tauFree_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/387a3fc4-1e09-5f4e-92ef-20dfefa53963

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar
import Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_of_charP_of_dvd_div
import Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_of_dvd
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd
import Theorems.Thm_ModularCurve_heckeBetaModLHDefined
import Theorems.Thm_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_heckeOperatorHAlong_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
import Theorems.Thm_ModularCurve_exists_eq_add_ord_and_eq_algebraMap_mul_mul_smul_pow_of_pic0Mk_eq
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_norm_mem_integers_and_residue_norm_eq_norm_residue
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_add_one_of_charP_of_dvd
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup_inf_gamma0_mul_of_charP
import Theorems.Thm_ModularCurve_coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup
import Theorems.Thm_ModularCurve_exists_ofAlgAut_smul_norm_heckeBetaHBar_inv_smul_eq_algebraMap_mul_norm_heckeBetaHBar_of_ne
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_reducedRootFunction_genOpH_T_eq_smul_pow_mul_norm_heckeBetaModLH_of_abelJacobiPin_tauFree_of_algEquiv
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "instance" "WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun"
p2m_attr_erase "simp" "KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11"
p2m_attr_erase "simp" "CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_jqNGen ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 1600000

namespace NormReduceMod

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
  (Pl : ValuationSubring (AlgebraicClosure ℚ))

noncomputable def iota : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) →+* ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) :=
  (IntermediateField.inclusion (qExpFunctionFieldC_mono (IsLocalRing.ResidueField ↥Pl) (inf_le_left : (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) ≤ (CohCarrier.GammaH M H)))).toRingHom

@[scoped simp] theorem coe_iota (r : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : ((iota M H ℓ Pl r : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = (r : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) :=
  IntermediateField.coe_inclusion _ r

noncomputable def alpha : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) →ₐ[(AlgebraicClosure ℚ)] ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) := heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ

theorem coe_alpha (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) : ((alpha M H ℓ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))) : LaurentSeries (AlgebraicClosure ℚ)) = (f : LaurentSeries (AlgebraicClosure ℚ)) :=
  coe_heckeAlphaHBar M H ℓ f

variable (R : RegularProlongation Pl ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) (R' : RegularProlongation Pl ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))

  (hR₁ : ∀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), f ∈ R.integers ↔ ∃ x y : LaurentSeries ↥Pl, coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap Pl.subtype y = coeffMap Pl.subtype x)
  (hR'₁ : ∀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))), f ∈ R'.integers ↔ ∃ x y : LaurentSeries ↥Pl, coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap Pl.subtype y = coeffMap Pl.subtype x)

  (hR₃ : ∀ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (hf : f ∈ R.integers) (x y : LaurentSeries ↥Pl), coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 →
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap Pl.subtype y = coeffMap Pl.subtype x →
      ((R.residue ⟨f, hf⟩ : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * coeffMap (IsLocalRing.residue ↥Pl) y = coeffMap (IsLocalRing.residue ↥Pl) x)
  (hR'₃ : ∀ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))) (hf : f ∈ R'.integers) (x y : LaurentSeries ↥Pl), coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 →
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap Pl.subtype y = coeffMap Pl.subtype x →
      ((R'.residue ⟨f, hf⟩ : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * coeffMap (IsLocalRing.residue ↥Pl) y = coeffMap (IsLocalRing.residue ↥Pl) x)

include hR₁ hR'₁ in

theorem hint : ∀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), alpha M H ℓ f ∈ R'.integers ↔ f ∈ R.integers := by
  intro f
  rw [hR₁, hR'₁, coe_alpha]

include hR₁ hR₃ hR'₃ in

theorem hres : ∀ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (hf : f ∈ R.integers) (hf' : alpha M H ℓ f ∈ R'.integers),
    R'.residue ⟨alpha M H ℓ f, hf'⟩ = iota M H ℓ Pl (R.residue ⟨f, hf⟩) := by
  intro f hf hf'
  obtain ⟨x, y, hy, hxy⟩ := (hR₁ f).mp hf
  have h1 := hR₃ f hf x y hy hxy
  have h2 := hR'₃ (alpha M H ℓ f) hf' x y hy (by rw [coe_alpha]; exact hxy)
  apply Subtype.ext
  rw [coe_iota]
  exact mul_right_cancel₀ hy (h2.trans h1.symm)

set_option maxHeartbeats 3200000 in
include hR₁ hR'₁ hR₃ hR'₃ in

theorem normReduce_T
    (hdeg0 : AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (alpha M H ℓ) = ℓ + 1)
    (hdegκ : letI := (iota M H ℓ Pl).toAlgebra; Module.finrank ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) = ℓ + 1)
    (h : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))) (hh : h ∈ R'.integers) :
    ∃ hN : (letI := AlgebraicCurve.algebraAlong (alpha M H ℓ); Algebra.norm ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) h) ∈ R.integers,
      R.residue ⟨_, hN⟩ = (letI := (iota M H ℓ Pl).toAlgebra; Algebra.norm ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) (R'.residue ⟨h, hh⟩)) := by
  classical
  letI instk : Algebra ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) := (iota M H ℓ Pl).toAlgebra

  haveI : Module.Finite _ _ := Module.finite_of_finrank_eq_succ hdegκ
  let Bk : Module.Basis (Fin (ℓ + 1)) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) := Module.finBasisOfFinrankEq ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) hdegκ
  have hlift : ∀ i : Fin (ℓ + 1), ∃ x : ↥R'.integers, R'.residue x = Bk i := fun i => R'.residue_surjective (Bk i)
  choose xs hxs using hlift
  refine AlgebraicCurve.RegularProlongation.exists_norm_mem_integers_and_residue_norm_eq_norm_residue
    Pl R R' (alpha M H ℓ) (iota M H ℓ Pl) (hint M H ℓ Pl R R' hR₁ hR'₁) (hres M H ℓ Pl R R' hR₁ hR₃ hR'₃)
    (ℓ + 1) hdeg0 (fun i => (xs i : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))))) (fun i => (xs i).2) ?_ ?_ h hh
  ·
    have : (fun i => R'.residue ⟨(xs i : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))), (xs i).2⟩) = Bk := by
      funext i; rw [← hxs i]
    rw [this]; exact Bk.linearIndependent
  · have : (fun i => R'.residue ⟨(xs i : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))), (xs i).2⟩) = Bk := by
      funext i; rw [← hxs i]
    rw [this]; exact Bk.span_eq

set_option maxHeartbeats 3200000 in
include hR₁ hR'₁ hR₃ hR'₃ in

theorem normReduce_gen (n : ℕ) (hn : 0 < n)
    (hdeg0 : AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (alpha M H ℓ) = n)
    (hdegκ : letI := (iota M H ℓ Pl).toAlgebra; Module.finrank ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) = n)
    (h : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))) (hh : h ∈ R'.integers) :
    ∃ hN : (letI := AlgebraicCurve.algebraAlong (alpha M H ℓ); Algebra.norm ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) h) ∈ R.integers,
      R.residue ⟨_, hN⟩ = (letI := (iota M H ℓ Pl).toAlgebra; Algebra.norm ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) (R'.residue ⟨h, hh⟩)) := by
  classical
  letI instk : Algebra ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) := (iota M H ℓ Pl).toAlgebra

  haveI : Module.Finite _ _ := Module.finite_of_finrank_pos (by rw [hdegκ]; exact hn)
  let Bk : Module.Basis (Fin (n)) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) := Module.finBasisOfFinrankEq ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) hdegκ
  have hlift : ∀ i : Fin (n), ∃ x : ↥R'.integers, R'.residue x = Bk i := fun i => R'.residue_surjective (Bk i)
  choose xs hxs using hlift
  refine AlgebraicCurve.RegularProlongation.exists_norm_mem_integers_and_residue_norm_eq_norm_residue
    Pl R R' (alpha M H ℓ) (iota M H ℓ Pl) (hint M H ℓ Pl R R' hR₁ hR'₁) (hres M H ℓ Pl R R' hR₁ hR₃ hR'₃)
    (n) hdeg0 (fun i => (xs i : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))))) (fun i => (xs i).2) ?_ ?_ h hh
  ·
    have : (fun i => R'.residue ⟨(xs i : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))), (xs i).2⟩) = Bk := by
      funext i; rw [← hxs i]
    rw [this]; exact Bk.linearIndependent
  · have : (fun i => R'.residue ⟨(xs i : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))), (xs i).2⟩) = Bk := by
      funext i; rw [← hxs i]
    rw [this]; exact Bk.span_eq

end NormReduceMod
p2m_reactivate "P2MW.S_ModularCurve_reducedRootFunction_genOpH_T_eq_smul_pow_mul_norm_heckeBetaModLH_of_abelJacobiPin_tauFree_of_algEquiv.NormReduceMod"

namespace D6aT

theorem mem_of_pow_mem {F : Type*} [Field F] (V : ValuationSubring F) {x : F} {n : ℕ} (hn : 0 < n) (hx : x ^ n ∈ V) : x ∈ V := by
  rcases V.mem_or_inv_mem x with h | h
  · exact h
  · have key : x = x ^ n * (x⁻¹) ^ (n - 1) := by
      rcases eq_or_ne x 0 with rfl | hx0
      · simp [zero_pow hn.ne']
      · rw [inv_pow, ← pow_sub₀ _ hx0 (Nat.sub_le n 1), Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr hn.ne'), pow_one]
    rw [key]
    exact V.toSubring.mul_mem hx (V.toSubring.pow_mem h _)

theorem translation_mem_roof (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) :
    ModularGroup.T ∈ CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) := by
  refine Subgroup.mem_inf.mpr ⟨ModularCurve.translation_mem_GammaH M H, ?_⟩
  show ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (M * ℓ)
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [ModularGroup.T]

theorem coe_norm_along_inclusion_congr {K L : Type*} [Field K] [Field L] [Algebra K L]
    {B₁ B₂ T₁ T₂ : IntermediateField K L} (hB : B₁ = B₂) (hT : T₁ = T₂) (h₁ : B₁ ≤ T₁) (h₂ : B₂ ≤ T₂)
    (x₁ : ↥T₁) (x₂ : ↥T₂) (hx : (x₁ : L) = x₂) :
    ((letI := AlgebraicCurve.algebraAlong (IntermediateField.inclusion h₁); Algebra.norm ↥B₁ x₁ : ↥B₁) : L) =
      ((letI := AlgebraicCurve.algebraAlong (IntermediateField.inclusion h₂); Algebra.norm ↥B₂ x₂ : ↥B₂) : L) := by
  subst hB; subst hT
  obtain rfl : x₁ = x₂ := Subtype.ext hx
  rfl

end D6aT
p2m_reactivate "P2MW.S_ModularCurve_reducedRootFunction_genOpH_T_eq_smul_pow_mul_norm_heckeBetaModLH_of_abelJacobiPin_tauFree_of_algEquiv.NormReduceMod"

open D6aT ModularCurve in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem D6aT.conj_T
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]

    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (R : Type) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    [Algebra R (AlgebraicClosure ℚ)] [FaithfulSMul R (AlgebraicClosure ℚ)]
    (hRA : ∀ x : R, algebraMap R (AlgebraicClosure ℚ) x ∈ Pl)
    (hRdvr : IsDiscreteValuationRing R) (hRirr : Irreducible ((p : ℕ) : R))
    (hRfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ Pl.inertiaSubgroupIn ℚ ↔ ∀ x : R, σ (algebraMap R (AlgebraicClosure ℚ) x) = algebraMap R (AlgebraicClosure ℚ) x)
    (hRmax : ∀ y ∈ Pl, (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : R, algebraMap R (AlgebraicClosure ℚ) x = y)

    {h : ℕ} (𝒢 : PDivisibleGroup R p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[R] 𝒢.level v,
        (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
        ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[R] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))

    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwθ : wgen = SemilinearAut.ofAlgAut θ)

    (ιK : ↥Pl →+* K) (hιK : ∀ y : ↥Pl, ιK y = 0 ↔ Pl.valuation (y : AlgebraicClosure ℚ) < 1)

    (Ψ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) → ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hΨ : ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ∃ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∧ f ≠ 0 ∧
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
        ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ιK y)
    :
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
      ((y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) = ModularCurve.genOpH M H S (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) →
      ∃ (c : K) (g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), c ≠ 0 ∧
        Ψ y = algebraMap K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) c * g ^ p *
          (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            @Algebra.norm (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 ((M / p) * ℓ))) _ _
              ((ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ).toRingHom.toAlgebra)
              (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ (Ψ x)))) := by
  classical
  haveI hMp : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩
  have hpMp : ¬ p ∣ M / p := fun h => hpM2 (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h)
  intro ℓ hℓ hℓS hℓM x y hyx
  haveI hℓ0 : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓp : ℓ ≠ p := fun h => hℓM (h ▸ hpM)

  obtain ⟨Rg, hRg₁, hRg₂, hRg₃⟩ := ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
    (AlgebraicClosure ℚ) Pl (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)
  obtain ⟨Rg', hRg'₁, hRg'₂, hRg'₃⟩ := ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
    (AlgebraicClosure ℚ) Pl (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) (D6aT.translation_mem_roof M H ℓ)

  obtain ⟨D, f, yx, hDx, hf0, hdivf, hfy, hyx0, hΨx⟩ := hΨ x
  obtain ⟨D', f', yy, hDy, hf0', hdivf', hfy', hyy0, hΨy⟩ := hΨ y

  obtain ⟨hα, hβ, hPD, hfin, hN, D_ℓ, hDℓ, hcls, hfℓ0, hdivℓ⟩ :=
    ModularCurve.exists_coe_eq_correspondence_and_mk_eq_heckeOperatorHAlong_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord p M H ℓ hℓ hin wgen D f hf0 hdivf
  have hDD' : (AlgebraicCurve.Pic0.mk D_ℓ : ModularCurve.JH M H) = AlgebraicCurve.Pic0.mk D' := by
    rw [hcls, hDx, ← ModularCurve.genOpH_T (M := M) (H := H) (S := S) ℓ hℓ hℓS hℓM, ← hyx, hDy]

  obtain ⟨h, c₀, hh0, hc0, -, hff'⟩ := ModularCurve.exists_eq_add_ord_and_eq_algebraMap_mul_mul_smul_pow_of_pic0Mk_eq
    p M H wgen D_ℓ D' hDD' (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H))) f' hfℓ0 hf0' hdivℓ hdivf'

  obtain ⟨cW, hcW, hWT⟩ := ModularCurve.exists_ofAlgAut_smul_norm_heckeBetaHBar_inv_smul_eq_algebraMap_mul_norm_heckeBetaHBar_of_ne p M hpM hpM2 H hHp hin θ hθ ℓ hℓ hℓp f
  have hfℓ : (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H))) = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) cW * (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) := by
    rw [hwθ]; exact hWT

  have hfO : ((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers :=
    (hRg₁ _).mpr ⟨yx, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]; exact hfy⟩
  have hf'O : ((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers :=
    (hRg₁ _).mpr ⟨yy, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]; exact hfy'⟩
  have hβdef : ModularCurve.HeckeBetaHDefined M H ℓ := (hin.1 ℓ hℓ).betaHDefined
  have hβO : ((heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))))) ∈ Rg'.integers := by
    refine (hRg'₁ _).mpr ⟨qExpand ↥Pl ℓ yx, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
    rw [map_one, mul_one, coe_heckeBetaHBar M H ℓ hβdef, hfy, ModularCurve.coeffMap_qExpand]
  have hβres : ((Rg'.residue ⟨_, hβO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = qExpand (IsLocalRing.ResidueField ↥Pl) ℓ (coeffMap (IsLocalRing.residue ↥Pl) yx) := by
    have h1 := hRg'₃ _ hβO (qExpand ↥Pl ℓ yx) 1 (by rw [map_one]; exact one_ne_zero)
      (by rw [map_one, mul_one, coe_heckeBetaHBar M H ℓ hβdef, hfy, ModularCurve.coeffMap_qExpand])
    rw [map_one, mul_one, ModularCurve.coeffMap_qExpand] at h1; exact h1
  have hyx1 : ((Rg.residue ⟨((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hfO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = coeffMap (IsLocalRing.residue ↥Pl) yx := by
    have h1 := hRg₃ _ hfO yx 1 (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact hfy)
    rw [map_one, mul_one] at h1; exact h1
  have hyy1 : ((Rg.residue ⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = coeffMap (IsLocalRing.residue ↥Pl) yy := by
    have h1 := hRg₃ _ hf'O yy 1 (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact hfy')
    rw [map_one, mul_one] at h1; exact h1

  have hdeg0 : AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (NormReduceMod.alpha M H ℓ) = ℓ + 1 := by
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    exact ModularCurve.finrankAlong_heckeAlphaHBar (AlgebraicClosure ℚ) M H hℓM
  have hdegκ : letI := (NormReduceMod.iota M H ℓ Pl).toAlgebra;
      Module.finrank ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) = ℓ + 1 := by
    obtain ⟨-, h2⟩ := ModularCurve.finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_add_one_of_charP_of_dvd (IsLocalRing.ResidueField ↥Pl) p M hpM hpM2 H hHp ℓ hℓ hℓM hℓp
    rw [IntermediateField.relfinrank_eq_finrank_of_le (ModularCurve.qExpFunctionFieldC_mono (IsLocalRing.ResidueField ↥Pl) inf_le_left)] at h2
    exact h2
  obtain ⟨hNO, hNres⟩ := NormReduceMod.normReduce_T M H ℓ Pl Rg Rg' hRg₁ hRg'₁ hRg₃ hRg'₃ hdeg0 hdegκ _ hβO

  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq (c₀ * cW) (Fact.out : p.Prime).pos
  set k : ↥(ModularCurve.xHFunctionFieldBar M H) := algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lam * (wgen • h) with hkdef
  have hk : f' = (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) * k ^ p := by
    rw [hff', hfℓ, hkdef, mul_pow, ← map_pow, hlam, map_mul]; ring

  have hres0' : Rg.residue ⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ ≠ 0 := by
    intro h0; apply hyy0; rw [← hyy1, h0]; rfl
  have hβres0 : Rg'.residue ⟨_, hβO⟩ ≠ 0 := by
    intro h0; apply hyx0
    have h1 : qExpand (IsLocalRing.ResidueField ↥Pl) ℓ (coeffMap (IsLocalRing.residue ↥Pl) yx) = 0 := by rw [← hβres, h0]; rfl
    exact ModularCurve.qExpand_injective ℓ (h1.trans (map_zero _).symm)
  have hNres0 : Rg.residue ⟨_, hNO⟩ ≠ 0 := by
    rw [hNres]
    letI := (NormReduceMod.iota M H ℓ Pl).toAlgebra
    haveI : Module.Finite ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) := Module.finite_of_finrank_eq_succ hdegκ
    exact Algebra.norm_ne_zero_iff.mpr hβres0
  obtain ⟨uN, huNeq⟩ := Rg.isUnit_of_residue_ne_zero hNres0

  have hN0 : ((letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) : ↥(ModularCurve.xHFunctionFieldBar M H)) ≠ 0 := by
    intro h0; apply hNres0
    have : (⟨_, hNO⟩ : ↥Rg.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hinvN : ((((uN⁻¹ : (↥Rg.integers)ˣ) : ↥Rg.integers) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) = ((((letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have : (((uN⁻¹ : (↥Rg.integers)ˣ) : ↥Rg.integers) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) * (((uN : (↥Rg.integers)ˣ) : ↥Rg.integers) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one]
    rw [huNeq] at this
    exact this
  have hkpO : (((k : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ^ p ∈ Rg.integers := by
    have e1 : (((k : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ^ p = (((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) * ((((letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))⁻¹ := by
      have hne : ((((letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ≠ 0 := by exact_mod_cast hN0
      rw [eq_mul_inv_iff_mul_eq₀ hne]
      have := congrArg (fun z : ↥(ModularCurve.xHFunctionFieldBar M H) => ((z : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) hk
      simp only [this, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      exact mul_comm _ _
    rw [e1, ← hinvN]
    exact Rg.integers.toSubring.mul_mem hf'O ((uN⁻¹ : (↥Rg.integers)ˣ) : ↥Rg.integers).2
  have hkO : ((k : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers := D6aT.mem_of_pow_mem Rg.integers (Fact.out : p.Prime).pos hkpO

  have hprod : (⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ : ↥Rg.integers) = ⟨_, hNO⟩ * ⟨_, hkO⟩ ^ p := by
    apply Subtype.ext
    show (((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) = ((((letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) * (((k : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ^ p
    have := congrArg (fun z : ↥(ModularCurve.xHFunctionFieldBar M H) => ((z : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) hk
    simp only [this, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have hresf' : Rg.residue ⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ =
      (letI := (NormReduceMod.iota M H ℓ Pl).toAlgebra; Algebra.norm ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) (Rg'.residue ⟨_, hβO⟩)) * (Rg.residue ⟨_, hkO⟩) ^ p := by
    rw [hprod, map_mul, map_pow, hNres]

  have hker : ∀ a ∈ IsLocalRing.maximalIdeal ↥Pl, ιK a = 0 := fun a ha =>
    (hιK a).mpr ((ValuationSubring.valuation_lt_one_iff Pl a).mp ha)
  let j : (IsLocalRing.ResidueField ↥Pl) →+* K := Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥Pl) ιK hker
  have hjι : j.comp (IsLocalRing.residue ↥Pl) = ιK := RingHom.ext fun a => rfl
  have hcoe : ∀ z : LaurentSeries ↥Pl, coeffMap ιK z = coeffMap j (coeffMap (IsLocalRing.residue ↥Pl) z) := fun z => by
    rw [coeffMap_coeffMap, hjι]
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hκN : ((M / p : ℕ) : (IsLocalRing.ResidueField ↥Pl)) ≠ 0 := by rw [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥Pl) p]; exact hpMp
  have hKN : ((M / p : ℕ) : K) ≠ 0 := by rw [Ne, CharP.cast_eq_zero_iff K p]; exact hpMp
  have hKℓ : ((ℓ : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p]
    intro h; exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).mp h).symm
  have hΨx' : ((Ψ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) = coeffMap j ((Rg.residue ⟨((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hfO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) := by
    rw [hΨx, hcoe, hyx1]

  obtain ⟨hdκ1, -⟩ := ModularCurve.finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_add_one_of_charP_of_dvd (IsLocalRing.ResidueField ↥Pl) p M hpM hpM2 H hHp ℓ hℓ hℓM hℓp
  obtain ⟨hdK1, hdK2⟩ := ModularCurve.finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_add_one_of_charP_of_dvd K p M hpM hpM2 H hHp ℓ hℓ hℓM hℓp
  have hfink : AlgebraicCurve.FiniteAlong (IsLocalRing.ResidueField ↥Pl) (heckeAlphaModLH (IsLocalRing.ResidueField ↥Pl) M H ℓ) := by
    letI := AlgebraicCurve.algebraAlong (heckeAlphaModLH (IsLocalRing.ResidueField ↥Pl) M H ℓ)
    have h := hdκ1
    unfold AlgebraicCurve.finrankAlong at h
    unfold AlgebraicCurve.FiniteAlong
    exact Module.finite_of_finrank_eq_succ h
  have hfinK : AlgebraicCurve.FiniteAlong K (heckeAlphaModLH K M H ℓ) := by
    letI := AlgebraicCurve.algebraAlong (heckeAlphaModLH K M H ℓ)
    have h := hdK1
    unfold AlgebraicCurve.finrankAlong at h
    unfold AlgebraicCurve.FiniteAlong
    exact Module.finite_of_finrank_eq_succ h
  have hKK := ModularCurve.coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap (IsLocalRing.ResidueField ↥Pl) K j M H ℓ hfink hfinK (by rw [hdκ1, hdK1]) (Rg'.residue ⟨_, hβO⟩)

  have hle : (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) ≤ (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :=
    ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup p M hpM hpM2 H hHp K
  have hT : (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) = (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * ℓ))) := ModularCurve.qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup_inf_gamma0_mul_of_charP K p M hpM hpM2 H hHp ℓ hℓ hℓp
  have hcop : ℓ.Coprime (M / p) := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr (fun h => hℓM (h.trans (Nat.div_dvd_of_dvd hpM)))
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hr2 : IntermediateField.relfinrank (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * ℓ))) = ℓ + 1 :=
    ModularCurve.relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ hcop hKN hKℓ
  have hB : (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) = (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := by
    apply le_antisymm hle
    have hmul := IntermediateField.relfinrank_mul_relfinrank hle (ModularCurve.qExpFunctionFieldC_mono K (inf_le_left : CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * ℓ) ≤ _))
    rw [hr2, ← hT, hdK2] at hmul
    have h1 : IntermediateField.relfinrank (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) = 1 := by
      have := Nat.eq_of_mul_eq_mul_right (Nat.succ_pos ℓ) (hmul.trans (one_mul _).symm)
      exact this
    exact IntermediateField.relfinrank_eq_one_iff.mp h1

  have hβdefK := ModularCurve.heckeBetaModLHDefined K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ
  have hx12 : ((⟨coeffMap j ((Rg'.residue ⟨_, hβO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)),
      ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem j (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) (Rg'.residue ⟨_, hβO⟩).2⟩ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries K) =
      ((heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ (Ψ x) : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * ℓ)))) : LaurentSeries K) := by
    show coeffMap j ((Rg'.residue ⟨_, hβO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = _
    rw [coe_heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ hβdefK, hΨx', hβres, ModularCurve.coeffMap_qExpand, hyx1]
  have hnorm := D6aT.coe_norm_along_inclusion_congr hB hT (ModularCurve.qExpFunctionFieldC_mono K inf_le_left) (ModularCurve.qExpFunctionFieldC_mono K inf_le_left) _ _ hx12

  let gk : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := ⟨coeffMap j ((Rg.residue ⟨_, hkO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)),
    hle (ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem j _ (Rg.residue ⟨_, hkO⟩).2)⟩
  refine ⟨1, gk, one_ne_zero, ?_⟩
  apply Subtype.ext
  have final : ((Ψ y : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) =
      ((gk : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) ^ p *
        (((letI := AlgebraicCurve.algebraAlong (heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ);
            Algebra.norm ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ (Ψ x))) : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) := by

    have e1 : ((Ψ y : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) =
        coeffMap j (((letI := (NormReduceMod.iota M H ℓ Pl).toAlgebra; Algebra.norm ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) (Rg'.residue ⟨_, hβO⟩)) : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) *
          (coeffMap j ((Rg.residue ⟨_, hkO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl))) ^ p := by
      rw [hΨy, hcoe, ← hyy1, hresf', MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]

    have e2 : coeffMap j (((letI := (NormReduceMod.iota M H ℓ Pl).toAlgebra; Algebra.norm ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) (Rg'.residue ⟨_, hβO⟩)) : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
        (((letI := AlgebraicCurve.algebraAlong (heckeAlphaModLH K M H ℓ); Algebra.norm ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) (⟨coeffMap j ((Rg'.residue ⟨_, hβO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)), ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem j (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) (Rg'.residue ⟨_, hβO⟩).2⟩ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))) : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))) : LaurentSeries K) :=
      hKK
    have e3 : (((letI := AlgebraicCurve.algebraAlong (heckeAlphaModLH K M H ℓ); Algebra.norm ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) (⟨coeffMap j ((Rg'.residue ⟨_, hβO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)), ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem j (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) (Rg'.residue ⟨_, hβO⟩).2⟩ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))) : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))) : LaurentSeries K) =
        (((letI := AlgebraicCurve.algebraAlong (heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ);
            Algebra.norm ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ (Ψ x))) : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) :=
      hnorm
    rw [e1, e2, e3, mul_comm]
  rw [map_one, one_mul, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  exact final

open D6aT ModularCurve in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem D6aT.conj_U
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]

    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (R : Type) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    [Algebra R (AlgebraicClosure ℚ)] [FaithfulSMul R (AlgebraicClosure ℚ)]
    (hRA : ∀ x : R, algebraMap R (AlgebraicClosure ℚ) x ∈ Pl)
    (hRdvr : IsDiscreteValuationRing R) (hRirr : Irreducible ((p : ℕ) : R))
    (hRfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ Pl.inertiaSubgroupIn ℚ ↔ ∀ x : R, σ (algebraMap R (AlgebraicClosure ℚ) x) = algebraMap R (AlgebraicClosure ℚ) x)
    (hRmax : ∀ y ∈ Pl, (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : R, algebraMap R (AlgebraicClosure ℚ) x = y)

    {h : ℕ} (𝒢 : PDivisibleGroup R p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[R] 𝒢.level v,
        (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
        ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[R] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))

    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwθ : wgen = SemilinearAut.ofAlgAut θ)

    (ιK : ↥Pl →+* K) (hιK : ∀ y : ↥Pl, ιK y = 0 ↔ Pl.valuation (y : AlgebraicClosure ℚ) < 1)

    (Ψ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) → ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hΨ : ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ∃ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∧ f ≠ 0 ∧
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
        ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ιK y)
    :
    (∀ (q' : ℕ) (hq : q'.Prime) (hqM : q' ∣ M) (_ : q' ≠ p) (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
      ((y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) = ModularCurve.genOpH M H S (CohCarrier.Gen.U q' hq hqM) ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) →
      ∃ (c : K) (g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), c ≠ 0 ∧
        Ψ y = algebraMap K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) c * g ^ p *
          (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            haveI : NeZero q' := ⟨hq.ne_zero⟩;
            @Algebra.norm (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 ((M / p) * q'))) _ _
              ((ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q').toRingHom.toAlgebra)
              (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q' (Ψ x)))) := by
  classical
  haveI hMp : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩
  have hpMp : ¬ p ∣ M / p := fun h => hpM2 (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h)
  intro ℓ hℓ hℓMd hℓp x y hyx
  haveI hℓ0 : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓM : ℓ ∣ M / p := by
    have hcp : Nat.Coprime ℓ p := (Nat.coprime_primes hℓ (Fact.out)).mpr hℓp
    have : ℓ ∣ p * (M / p) := by rw [Nat.mul_div_cancel' hpM]; exact hℓMd
    exact hcp.dvd_of_dvd_mul_left this

  obtain ⟨Rg, hRg₁, hRg₂, hRg₃⟩ := ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
    (AlgebraicClosure ℚ) Pl (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)
  obtain ⟨Rg', hRg'₁, hRg'₂, hRg'₃⟩ := ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
    (AlgebraicClosure ℚ) Pl (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) (D6aT.translation_mem_roof M H ℓ)

  obtain ⟨D, f, yx, hDx, hf0, hdivf, hfy, hyx0, hΨx⟩ := hΨ x
  obtain ⟨D', f', yy, hDy, hf0', hdivf', hfy', hyy0, hΨy⟩ := hΨ y

  obtain ⟨hα, hβ, hPD, hfin, hN, D_ℓ, hDℓ, hcls, hfℓ0, hdivℓ⟩ :=
    ModularCurve.exists_coe_eq_correspondence_and_mk_eq_heckeOperatorHAlong_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord p M H ℓ hℓ hin wgen D f hf0 hdivf
  have hDD' : (AlgebraicCurve.Pic0.mk D_ℓ : ModularCurve.JH M H) = AlgebraicCurve.Pic0.mk D' := by
    rw [hcls, hDx, ← ModularCurve.genOpH_U (M := M) (H := H) (S := S) ℓ hℓ hℓMd, ← hyx, hDy]

  obtain ⟨h, c₀, hh0, hc0, -, hff'⟩ := ModularCurve.exists_eq_add_ord_and_eq_algebraMap_mul_mul_smul_pow_of_pic0Mk_eq
    p M H wgen D_ℓ D' hDD' (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H))) f' hfℓ0 hf0' hdivℓ hdivf'

  obtain ⟨cW, hcW, hWT⟩ := ModularCurve.exists_ofAlgAut_smul_norm_heckeBetaHBar_inv_smul_eq_algebraMap_mul_norm_heckeBetaHBar_of_ne p M hpM hpM2 H hHp hin θ hθ ℓ hℓ hℓp f
  have hfℓ : (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H))) = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) cW * (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) := by
    rw [hwθ]; exact hWT

  have hfO : ((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers :=
    (hRg₁ _).mpr ⟨yx, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]; exact hfy⟩
  have hf'O : ((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers :=
    (hRg₁ _).mpr ⟨yy, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]; exact hfy'⟩
  have hβdef : ModularCurve.HeckeBetaHDefined M H ℓ := (hin.1 ℓ hℓ).betaHDefined
  have hβO : ((heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))))) ∈ Rg'.integers := by
    refine (hRg'₁ _).mpr ⟨qExpand ↥Pl ℓ yx, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
    rw [map_one, mul_one, coe_heckeBetaHBar M H ℓ hβdef, hfy, ModularCurve.coeffMap_qExpand]
  have hβres : ((Rg'.residue ⟨_, hβO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = qExpand (IsLocalRing.ResidueField ↥Pl) ℓ (coeffMap (IsLocalRing.residue ↥Pl) yx) := by
    have h1 := hRg'₃ _ hβO (qExpand ↥Pl ℓ yx) 1 (by rw [map_one]; exact one_ne_zero)
      (by rw [map_one, mul_one, coe_heckeBetaHBar M H ℓ hβdef, hfy, ModularCurve.coeffMap_qExpand])
    rw [map_one, mul_one, ModularCurve.coeffMap_qExpand] at h1; exact h1
  have hyx1 : ((Rg.residue ⟨((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hfO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = coeffMap (IsLocalRing.residue ↥Pl) yx := by
    have h1 := hRg₃ _ hfO yx 1 (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact hfy)
    rw [map_one, mul_one] at h1; exact h1
  have hyy1 : ((Rg.residue ⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = coeffMap (IsLocalRing.residue ↥Pl) yy := by
    have h1 := hRg₃ _ hf'O yy 1 (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact hfy')
    rw [map_one, mul_one] at h1; exact h1

  have hdeg0 : AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (NormReduceMod.alpha M H ℓ) = ℓ := by
    exact ModularCurve.finrankAlong_heckeAlphaHBar_of_dvd (AlgebraicClosure ℚ) M H ℓ hℓMd
  have hdegκ : letI := (NormReduceMod.iota M H ℓ Pl).toAlgebra;
      Module.finrank ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) = ℓ := by
    obtain ⟨-, h2⟩ := ModularCurve.finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_of_charP_of_dvd_div (IsLocalRing.ResidueField ↥Pl) p M hpM hpM2 H hHp ℓ hℓ hℓM hℓp
    rw [IntermediateField.relfinrank_eq_finrank_of_le (ModularCurve.qExpFunctionFieldC_mono (IsLocalRing.ResidueField ↥Pl) inf_le_left)] at h2
    exact h2
  obtain ⟨hNO, hNres⟩ := NormReduceMod.normReduce_gen M H ℓ Pl Rg Rg' hRg₁ hRg'₁ hRg₃ hRg'₃ ℓ hℓ.pos hdeg0 hdegκ _ hβO

  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq (c₀ * cW) (Fact.out : p.Prime).pos
  set k : ↥(ModularCurve.xHFunctionFieldBar M H) := algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lam * (wgen • h) with hkdef
  have hk : f' = (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) * k ^ p := by
    rw [hff', hfℓ, hkdef, mul_pow, ← map_pow, hlam, map_mul]; ring

  have hres0' : Rg.residue ⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ ≠ 0 := by
    intro h0; apply hyy0; rw [← hyy1, h0]; rfl
  have hβres0 : Rg'.residue ⟨_, hβO⟩ ≠ 0 := by
    intro h0; apply hyx0
    have h1 : qExpand (IsLocalRing.ResidueField ↥Pl) ℓ (coeffMap (IsLocalRing.residue ↥Pl) yx) = 0 := by rw [← hβres, h0]; rfl
    exact ModularCurve.qExpand_injective ℓ (h1.trans (map_zero _).symm)
  have hNres0 : Rg.residue ⟨_, hNO⟩ ≠ 0 := by
    rw [hNres]
    letI := (NormReduceMod.iota M H ℓ Pl).toAlgebra
    haveI : Module.Finite ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) := Module.finite_of_finrank_pos (by rw [hdegκ]; exact hℓ.pos)
    exact Algebra.norm_ne_zero_iff.mpr hβres0
  obtain ⟨uN, huNeq⟩ := Rg.isUnit_of_residue_ne_zero hNres0

  have hN0 : ((letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) : ↥(ModularCurve.xHFunctionFieldBar M H)) ≠ 0 := by
    intro h0; apply hNres0
    have : (⟨_, hNO⟩ : ↥Rg.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hinvN : ((((uN⁻¹ : (↥Rg.integers)ˣ) : ↥Rg.integers) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) = ((((letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have : (((uN⁻¹ : (↥Rg.integers)ˣ) : ↥Rg.integers) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) * (((uN : (↥Rg.integers)ˣ) : ↥Rg.integers) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one]
    rw [huNeq] at this
    exact this
  have hkpO : (((k : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ^ p ∈ Rg.integers := by
    have e1 : (((k : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ^ p = (((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) * ((((letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))⁻¹ := by
      have hne : ((((letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ≠ 0 := by exact_mod_cast hN0
      rw [eq_mul_inv_iff_mul_eq₀ hne]
      have := congrArg (fun z : ↥(ModularCurve.xHFunctionFieldBar M H) => ((z : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) hk
      simp only [this, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      exact mul_comm _ _
    rw [e1, ← hinvN]
    exact Rg.integers.toSubring.mul_mem hf'O ((uN⁻¹ : (↥Rg.integers)ˣ) : ↥Rg.integers).2
  have hkO : ((k : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers := D6aT.mem_of_pow_mem Rg.integers (Fact.out : p.Prime).pos hkpO

  have hprod : (⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ : ↥Rg.integers) = ⟨_, hNO⟩ * ⟨_, hkO⟩ ^ p := by
    apply Subtype.ext
    show (((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) = ((((letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ); (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) * (((k : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ^ p
    have := congrArg (fun z : ↥(ModularCurve.xHFunctionFieldBar M H) => ((z : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) hk
    simp only [this, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have hresf' : Rg.residue ⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ =
      (letI := (NormReduceMod.iota M H ℓ Pl).toAlgebra; Algebra.norm ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) (Rg'.residue ⟨_, hβO⟩)) * (Rg.residue ⟨_, hkO⟩) ^ p := by
    rw [hprod, map_mul, map_pow, hNres]

  have hker : ∀ a ∈ IsLocalRing.maximalIdeal ↥Pl, ιK a = 0 := fun a ha =>
    (hιK a).mpr ((ValuationSubring.valuation_lt_one_iff Pl a).mp ha)
  let j : (IsLocalRing.ResidueField ↥Pl) →+* K := Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥Pl) ιK hker
  have hjι : j.comp (IsLocalRing.residue ↥Pl) = ιK := RingHom.ext fun a => rfl
  have hcoe : ∀ z : LaurentSeries ↥Pl, coeffMap ιK z = coeffMap j (coeffMap (IsLocalRing.residue ↥Pl) z) := fun z => by
    rw [coeffMap_coeffMap, hjι]
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hκN : ((M / p : ℕ) : (IsLocalRing.ResidueField ↥Pl)) ≠ 0 := by rw [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥Pl) p]; exact hpMp
  have hKN : ((M / p : ℕ) : K) ≠ 0 := by rw [Ne, CharP.cast_eq_zero_iff K p]; exact hpMp
  have hKℓ : ((ℓ : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p]
    intro h; exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).mp h).symm
  have hΨx' : ((Ψ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) = coeffMap j ((Rg.residue ⟨((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hfO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) := by
    rw [hΨx, hcoe, hyx1]

  obtain ⟨hdκ1, -⟩ := ModularCurve.finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_of_charP_of_dvd_div (IsLocalRing.ResidueField ↥Pl) p M hpM hpM2 H hHp ℓ hℓ hℓM hℓp
  obtain ⟨hdK1, hdK2⟩ := ModularCurve.finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_of_charP_of_dvd_div K p M hpM hpM2 H hHp ℓ hℓ hℓM hℓp
  have hfink : AlgebraicCurve.FiniteAlong (IsLocalRing.ResidueField ↥Pl) (heckeAlphaModLH (IsLocalRing.ResidueField ↥Pl) M H ℓ) := by
    letI := AlgebraicCurve.algebraAlong (heckeAlphaModLH (IsLocalRing.ResidueField ↥Pl) M H ℓ)
    have h := hdκ1
    unfold AlgebraicCurve.finrankAlong at h
    unfold AlgebraicCurve.FiniteAlong
    exact Module.finite_of_finrank_pos (by rw [h]; exact hℓ.pos)
  have hfinK : AlgebraicCurve.FiniteAlong K (heckeAlphaModLH K M H ℓ) := by
    letI := AlgebraicCurve.algebraAlong (heckeAlphaModLH K M H ℓ)
    have h := hdK1
    unfold AlgebraicCurve.finrankAlong at h
    unfold AlgebraicCurve.FiniteAlong
    exact Module.finite_of_finrank_pos (by rw [h]; exact hℓ.pos)
  have hKK := ModularCurve.coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap (IsLocalRing.ResidueField ↥Pl) K j M H ℓ hfink hfinK (by rw [hdκ1, hdK1]) (Rg'.residue ⟨_, hβO⟩)

  have hle : (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) ≤ (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :=
    ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup p M hpM hpM2 H hHp K
  have hT : (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) = (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * ℓ))) := ModularCurve.qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup_inf_gamma0_mul_of_charP K p M hpM hpM2 H hHp ℓ hℓ hℓp
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hr2 : IntermediateField.relfinrank (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * ℓ))) = ℓ :=
    ModularCurve.relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_of_dvd K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ hℓM hKN hKℓ
  have hB : (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) = (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := by
    apply le_antisymm hle
    have hmul := IntermediateField.relfinrank_mul_relfinrank hle (ModularCurve.qExpFunctionFieldC_mono K (inf_le_left : CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * ℓ) ≤ _))
    rw [hr2, ← hT, hdK2] at hmul
    have h1 : IntermediateField.relfinrank (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) = 1 := by
      have := Nat.eq_of_mul_eq_mul_right hℓ.pos (hmul.trans (one_mul _).symm)
      exact this
    exact IntermediateField.relfinrank_eq_one_iff.mp h1

  have hβdefK := ModularCurve.heckeBetaModLHDefined K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ
  have hx12 : ((⟨coeffMap j ((Rg'.residue ⟨_, hβO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)),
      ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem j (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) (Rg'.residue ⟨_, hβO⟩).2⟩ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries K) =
      ((heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ (Ψ x) : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * ℓ)))) : LaurentSeries K) := by
    show coeffMap j ((Rg'.residue ⟨_, hβO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = _
    rw [coe_heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ hβdefK, hΨx', hβres, ModularCurve.coeffMap_qExpand, hyx1]
  have hnorm := D6aT.coe_norm_along_inclusion_congr hB hT (ModularCurve.qExpFunctionFieldC_mono K inf_le_left) (ModularCurve.qExpFunctionFieldC_mono K inf_le_left) _ _ hx12

  let gk : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := ⟨coeffMap j ((Rg.residue ⟨_, hkO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)),
    hle (ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem j _ (Rg.residue ⟨_, hkO⟩).2)⟩
  refine ⟨1, gk, one_ne_zero, ?_⟩
  apply Subtype.ext
  have final : ((Ψ y : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) =
      ((gk : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) ^ p *
        (((letI := AlgebraicCurve.algebraAlong (heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ);
            Algebra.norm ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ (Ψ x))) : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) := by

    have e1 : ((Ψ y : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) =
        coeffMap j (((letI := (NormReduceMod.iota M H ℓ Pl).toAlgebra; Algebra.norm ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) (Rg'.residue ⟨_, hβO⟩)) : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) *
          (coeffMap j ((Rg.residue ⟨_, hkO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl))) ^ p := by
      rw [hΨy, hcoe, ← hyy1, hresf', MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]

    have e2 : coeffMap j (((letI := (NormReduceMod.iota M H ℓ Pl).toAlgebra; Algebra.norm ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)) (Rg'.residue ⟨_, hβO⟩)) : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
        (((letI := AlgebraicCurve.algebraAlong (heckeAlphaModLH K M H ℓ); Algebra.norm ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) (⟨coeffMap j ((Rg'.residue ⟨_, hβO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)), ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem j (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) (Rg'.residue ⟨_, hβO⟩).2⟩ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))) : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))) : LaurentSeries K) :=
      hKK
    have e3 : (((letI := AlgebraicCurve.algebraAlong (heckeAlphaModLH K M H ℓ); Algebra.norm ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) (⟨coeffMap j ((Rg'.residue ⟨_, hβO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)), ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem j (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) (Rg'.residue ⟨_, hβO⟩).2⟩ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))))) : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))) : LaurentSeries K) =
        (((letI := AlgebraicCurve.algebraAlong (heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ);
            Algebra.norm ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ (Ψ x))) : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) :=
      hnorm
    rw [e1, e2, e3, mul_comm]
  rw [map_one, one_mul, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  exact final

open D6aT ModularCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]

    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (R : Type) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    [Algebra R (AlgebraicClosure ℚ)] [FaithfulSMul R (AlgebraicClosure ℚ)]
    (hRA : ∀ x : R, algebraMap R (AlgebraicClosure ℚ) x ∈ Pl)
    (hRdvr : IsDiscreteValuationRing R) (hRirr : Irreducible ((p : ℕ) : R))
    (hRfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ Pl.inertiaSubgroupIn ℚ ↔ ∀ x : R, σ (algebraMap R (AlgebraicClosure ℚ) x) = algebraMap R (AlgebraicClosure ℚ) x)
    (hRmax : ∀ y ∈ Pl, (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : R, algebraMap R (AlgebraicClosure ℚ) x = y)

    {h : ℕ} (𝒢 : PDivisibleGroup R p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[R] 𝒢.level v,
        (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
        ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[R] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))

    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwθ : wgen = SemilinearAut.ofAlgAut θ)

    (ιK : ↥Pl →+* K) (hιK : ∀ y : ↥Pl, ιK y = 0 ↔ Pl.valuation (y : AlgebraicClosure ℚ) < 1)

    (Ψ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) → ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hΨ : ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ∃ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∧ f ≠ 0 ∧
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
        ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ιK y)
    :
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
      ((y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) = ModularCurve.genOpH M H S (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) →
      ∃ (c : K) (g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), c ≠ 0 ∧
        Ψ y = algebraMap K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) c * g ^ p *
          (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            @Algebra.norm (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 ((M / p) * ℓ))) _ _
              ((ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ).toRingHom.toAlgebra)
              (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ (Ψ x)))) ∧
    (∀ (q' : ℕ) (hq : q'.Prime) (hqM : q' ∣ M) (_ : q' ≠ p) (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
      ((y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) = ModularCurve.genOpH M H S (CohCarrier.Gen.U q' hq hqM) ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) →
      ∃ (c : K) (g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), c ≠ 0 ∧
        Ψ y = algebraMap K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) c * g ^ p *
          (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            haveI : NeZero q' := ⟨hq.ne_zero⟩;
            @Algebra.norm (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 ((M / p) * q'))) _ _
              ((ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q').toRingHom.toAlgebra)
              (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q' (Ψ x))))  := by
  exact ⟨D6aT.conj_T p hp2 M hpM hpM2 H hHp S hin Pl hPl K hj 𝔛 Λ hrepΛ O hD hDQ hsep ajQ kQ ajbar εbar hpoinc hajQε hajQ hkQ₁ hkQ₂ hajbar hajbar_over hεbar hεbar_aj hpts_law hAJ R hRA hRdvr hRirr hRfix hRmax 𝒢 Δ hΔinj hΔlev hΔgal hΔhecke wgen hwgen θ hθ hwθ ιK hιK Ψ hΨ, D6aT.conj_U p hp2 M hpM hpM2 H hHp S hin Pl hPl K hj 𝔛 Λ hrepΛ O hD hDQ hsep ajQ kQ ajbar εbar hpoinc hajQε hajQ hkQ₁ hkQ₂ hajbar hajbar_over hεbar hεbar_aj hpts_law hAJ R hRA hRdvr hRirr hRfix hRmax 𝒢 Δ hΔinj hΔlev hΔgal hΔhecke wgen hwgen θ hθ hwθ ιK hιK Ψ hΨ⟩

#print axioms solution

end S_ModularCurve_reducedRootFunction_genOpH_T_eq_smul_pow_mul_norm_heckeBetaModLH_of_abelJacobiPin_tauFree_of_algEquiv
end P2MW
export P2MW.S_ModularCurve_reducedRootFunction_genOpH_T_eq_smul_pow_mul_norm_heckeBetaModLH_of_abelJacobiPin_tauFree_of_algEquiv (solution)
