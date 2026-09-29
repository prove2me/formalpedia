-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_regularProlongation_sp_gauss_res_qexp_mapDomain_unique_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/96c3f395-a7fb-5db0-beb7-81cc1b14f70e

import Mathlib
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
import Theorems.Thm_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_AlgebraicCurve_RegularProlongation_placeMap_unique_of_forall_mapDomain_eq_ord
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_regularProlongation_sp_gauss_res_qexp_mapDomain_unique_surjective
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

p2m_open "AlgebraicCurve~genus IsLocalRing ModularCurve P2MW.S_ModularCurve_JHPlaceSpecialization_exists_regularProlongation_sp_gauss_res_qexp_mapDomain_unique_surjective.ModularCurve"
open scoped MatrixGroups

open CongruenceSubgroup in
section
namespace ModularCurve
p2m_export "ModularCurve" "JHPlaceSpecialization JHNeronObjectAtP.ΓN JHNeronObjectAtP.Fbar JHNeronObjectAtP jq coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC transcendental_jqModC infSubgroup translation_mem_GammaH Gamma1_le_GammaH GammaH_mono xHFunctionFieldC xHFunctionFieldBar qExpFunctionFieldC intFormRatiosC_subset exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange jqModC_mem_intFormRatiosC"
namespace PlaceSpecHProof
p2m_open "ModularCurve"

theorem mem_or_neg_mem_of_mem_sup_zpowers_neg_one {M : ℕ} (H : Subgroup (ZMod M)ˣ)
    {d : (ZMod M)ˣ} (hd : d ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) : d ∈ H ∨ -d ∈ H := by
  let S : Subgroup (ZMod M)ˣ :=
    { carrier := {x | x = 1 ∨ x = -1}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl) <;> simp
      inv_mem' := by
        rintro a (rfl | rfl) <;> simp }
  have hS : Subgroup.zpowers (-1 : (ZMod M)ˣ) ≤ S := by
    rw [Subgroup.zpowers_le]
    exact Or.inr rfl
  obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup.mp hd
  rcases hS hz with hz1 | hz1
  · left; rw [hz1, mul_one]; exact hh
  · right; rw [hz1]; simpa using hh

theorem neg_mem_Gamma0 {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : -γ ∈ Gamma0 M := by
  have := Gamma0_mem.mp hγ
  rw [Gamma0_mem]
  simp [Matrix.SpecialLinearGroup.coe_neg, this]

theorem gamma0Units_neg {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    CohCarrier.gamma0Units M ⟨-γ, neg_mem_Gamma0 hγ⟩ = -CohCarrier.gamma0Units M ⟨γ, hγ⟩ := by
  ext
  simp [CohCarrier.gamma0Units, Gamma0Map, Matrix.SpecialLinearGroup.coe_neg]

theorem mem_or_neg_mem_gammaH_of_mem_gammaH_sup {M : ℕ} (H : Subgroup (ZMod M)ˣ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ))) :
    γ ∈ CohCarrier.GammaH M H ∨ -γ ∈ CohCarrier.GammaH M H := by
  obtain ⟨hγ0, hd⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  rcases mem_or_neg_mem_of_mem_sup_zpowers_neg_one H hd with h | h
  · exact Or.inl (CohCarrier.mem_GammaH_iff.mpr ⟨hγ0, h⟩)
  · exact Or.inr (CohCarrier.mem_GammaH_iff.mpr ⟨neg_mem_Gamma0 hγ0, by rw [gamma0Units_neg hγ0]; exact h⟩)

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  rw [Gamma1_mem]; simp [ModularGroup.coe_T]

end ModularCurve.PlaceSpecHProof
end

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] :
    ∃ (R : RegularProlongation A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))
          (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
      (sp : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →
        Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),

      (∀ f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), f ∈ R.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
            coeffMap A.subtype x) ∧

      (∀ (f : R.integers) (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
        (((f : R.integers) : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
          coeffMap A.subtype x →
        ((R.residue f : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) *
            coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x) ∧

      (∀ (y : LaurentSeries ↥A)
          (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
            coeffMap (IsLocalRing.residue ↥A) y) ∧

      (∀ f : R.integers, R.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
          (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
          ∀ Q, Finsupp.mapDomain sp D Q = Q.ord (R.residue f)) ∧

      (∀ sp' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →
          Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
        (∀ f : R.integers, R.residue f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
            (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
            ∀ Q, Finsupp.mapDomain sp' D Q = Q.ord (R.residue f)) → sp' = sp) ∧

      (∀ (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (y : LaurentSeries ↥A),
        coeffMap A.subtype y = ((f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) →
        ∀ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A),
          ((g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y →
          g ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ v, D v = v.ord f) →
          ∀ v' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), Finsupp.mapDomain sp D v' = v'.ord g) ∧

      Function.Surjective sp ∧

      (∀ f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ v, D v = v.ord f) →
          ∃ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), g ≠ 0 ∧
            ∀ v' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), Finsupp.mapDomain sp D v' = v'.ord g) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  show
    ∃ (R : RegularProlongation A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM)))
          (↥(qExpFunctionFieldC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM))))
      (sp : Place (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM))) →
        Place (ResidueField ↥A) (↥(qExpFunctionFieldC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM)))),

      (∀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM))), f ∈ R.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM)))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
            coeffMap A.subtype x) ∧

      (∀ (f : R.integers) (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
        (((f : R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM)))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
          coeffMap A.subtype x →
        ((R.residue f : ↥(qExpFunctionFieldC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) *
            coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x) ∧

      (∀ (y : LaurentSeries ↥A)
          (hy : coeffMap A.subtype y ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM))),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM)))) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) =
            coeffMap (IsLocalRing.residue ↥A) y) ∧

      (∀ f : R.integers, R.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM))),
          (∀ P, D P = P.ord (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM))))) →
          ∀ Q, Finsupp.mapDomain sp D Q = Q.ord (R.residue f)) ∧

      (∀ sp' : Place (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM))) →
          Place (ResidueField ↥A) (↥(qExpFunctionFieldC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM))),
        (∀ f : R.integers, R.residue f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM))),
            (∀ P, D P = P.ord (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM))))) →
            ∀ Q, Finsupp.mapDomain sp' D Q = Q.ord (R.residue f)) → sp' = sp) ∧

      (∀ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM)))) (y : LaurentSeries ↥A),
        coeffMap A.subtype y = ((f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM)))) : LaurentSeries (AlgebraicClosure ℚ)) →
        ∀ g : ↥(qExpFunctionFieldC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM)),
          ((g : ↥(qExpFunctionFieldC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y →
          g ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM))), (∀ v, D v = v.ord f) →
          ∀ v' : Place (ResidueField ↥A) (↥(qExpFunctionFieldC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM))), Finsupp.mapDomain sp D v' = v'.ord g) ∧

      Function.Surjective sp ∧

      (∀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM))), f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM))), (∀ v, D v = v.ord f) →
          ∃ g : ↥(qExpFunctionFieldC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM)), g ≠ 0 ∧
            ∀ v' : Place (ResidueField ↥A) (↥(qExpFunctionFieldC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM))), Finsupp.mapDomain sp D v' = v'.ord g)
  set Γ : Subgroup SL(2, ℤ) := JHNeronObjectAtP.ΓN p M H hpM with hΓdef
  set κ := ResidueField ↥A with hκ
  set FMp : Type := ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) with hFMp
  set Fb : Type := ↥(qExpFunctionFieldC κ Γ) with hFb

  have hndvd : ¬ p ∣ M / p := by
    rintro ⟨c, hc⟩
    apply hpM2
    refine ⟨c, ?_⟩
    calc M = M / p * p := (Nat.div_mul_cancel hpM).symm
      _ = p ^ 2 * c := by rw [hc]; ring
  have h1 : CongruenceSubgroup.Gamma1 (M / p) ≤ Γ := Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM)
  have h0 : Γ ≤ CongruenceSubgroup.Gamma0 (M / p) := CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM)
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le h1
  have hT : ModularGroup.T ∈ Γ := translation_mem_GammaH (M / p) (infSubgroup p M H hpM)

  obtain ⟨R, hgauss, hresq, hq⟩ := exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div (AlgebraicClosure ℚ) A Γ hT

  have hjA : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) := by
    show (jqModC ↥A).map A.subtype = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ)
    rw [map_jqModC]
    show jqModC (AlgebraicClosure ℚ) = (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [map_jqModC]
  have hjmem : jqModC ℚ ∈ qExpFunctionFieldC ℚ Γ := intFormRatiosC_subset ℚ Γ (jqModC_mem_intFormRatiosC ℚ Γ)
  have hyjm : coeffMap A.subtype (jqModC ↥A) ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) := by
    rw [hjA]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hjmem
  obtain ⟨hint, hres⟩ := hq (jqModC ↥A) hyjm
  set x : R.integers := ⟨_, hint⟩ with hxdef
  have hresj : ((R.residue x : Fb) : LaurentSeries κ) = jqModC κ := by
    rw [hres]
    show (jqModC ↥A).map (residue ↥A) = jqModC κ
    rw [map_jqModC]
  have hyj : ((x : FMp) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    show coeffMap A.subtype (jqModC ↥A) = jqModC (AlgebraicClosure ℚ)
    show (jqModC ↥A).map A.subtype = jqModC (AlgebraicClosure ℚ)
    rw [map_jqModC]
  obtain ⟨xb, hxb, htrb, hfdb, hleb⟩ :=
    exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField (AlgebraicClosure ℚ) A Γ hT
  have hxres : R.residue x = xb := Subtype.ext (hresj.trans hxb.symm)
  haveI := hfdb
  have htrx : Transcendental κ (R.residue x) := by rw [hxres]; exact htrb
  have htr0 : Transcendental (AlgebraicClosure ℚ) (x : FMp) := by
    intro halg
    apply transcendental_jqModC (AlgebraicClosure ℚ)
    have h := halg.algHom (IntermediateField.val (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
    rw [← hyj]
    exact h
  have hyj' : ((x : FMp) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [hyj]
    show jqModC (AlgebraicClosure ℚ) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ)
    show jqModC (AlgebraicClosure ℚ) = (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [map_jqModC]
  haveI hfdF : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({(x : FMp)} : Set FMp)) FMp :=
    finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange Γ hT (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) rfl _ hyj'
  haveI : IsCurveOver κ Fb := isCurveOver_of_isAlgClosed_of_transcendental xb htrb
  haveI : IsCurveOver (AlgebraicClosure ℚ) FMp := isCurveOver_of_isAlgClosed_of_transcendental _ htr0
  have hfin : 0 < Module.finrank ↥(IntermediateField.adjoin κ ({R.residue x} : Set Fb)) Fb := by
    rw [hxres]; exact Module.finrank_pos
  have hfinF : 0 < Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({(x : FMp)} : Set FMp)) FMp :=
    Module.finrank_pos

  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) FMp :=
    AlgebraicCurve.hasPrincipalDivisors_of_transcendental (AlgebraicClosure ℚ) (x : FMp) htr0

  have hneg : ∀ γ ∈ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM ⊔ Subgroup.zpowers (-1 : (ZMod (M / p))ˣ)), γ ∈ Γ ∨ -γ ∈ Γ :=
    fun γ hγ => ModularCurve.PlaceSpecHProof.mem_or_neg_mem_gammaH_of_mem_gammaH_sup (infSubgroup p M H hpM) hγ
  have hle1 := finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index (AlgebraicClosure ℚ) Γ hT
    (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM ⊔ Subgroup.zpowers (-1 : (ZMod (M / p))ˣ))) (GammaH_mono le_sup_left) hneg
    (x : FMp) hyj
  have hle2 := index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField (M / p) (infSubgroup p M H hpM) hndvd A hA xb hxb
  have hle3 := hleb (x : FMp) hyj
  have hdeg : Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({(x : FMp)} : Set FMp)) FMp =
      Module.finrank ↥(IntermediateField.adjoin κ ({R.residue x} : Set Fb)) Fb := by
    rw [hxres]
    exact le_antisymm (hle1.trans hle2) hle3

  have hgood : genusFF κ Fb = genusFF (AlgebraicClosure ℚ) FMp :=
    genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd (M / p) (infSubgroup p M H hpM) hndvd κ

  have hchart := RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq A R x htrx hfin hdeg hgood
  obtain ⟨r, hdiv⟩ :=
    RegularProlongation.exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective A R x htrx hfin hdeg hchart
  refine ⟨R, r, hgauss, hresq, hq, hdiv, ?_, ?_, ?_, ?_⟩
  ·
    intro sp' hsp'
    exact RegularProlongation.placeMap_unique_of_forall_mapDomain_eq_ord A R x hfin hfinF sp' r hsp' hdiv
  ·
    intro f y hfy g hg hg0 D hD v'
    have hy : coeffMap A.subtype y ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) := by
      rw [hfy]; exact f.2
    obtain ⟨hint', hres'⟩ := hq y hy
    have hfeq : (⟨coeffMap A.subtype y, hy⟩ : FMp) = f := Subtype.ext hfy
    have hgeq : R.residue ⟨_, hint'⟩ = g := Subtype.ext (hres'.trans hg.symm)
    have hne : R.residue ⟨_, hint'⟩ ≠ 0 := by rw [hgeq]; exact hg0
    have := hdiv ⟨_, hint'⟩ hne D (fun P => by rw [hD P]; exact congrArg _ hfeq.symm) v'
    rw [hgeq] at this
    exact this
  ·
    intro Q
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Q.toValuationSubring
    have hordπ : Q.ord ((π : Q.toValuationSubring) : Fb) = 1 := Q.ord_coe_irreducible hπ
    have hπ0 : ((π : Q.toValuationSubring) : Fb) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    obtain ⟨f, hf⟩ := R.residue_surjective ((π : Q.toValuationSubring) : Fb)
    have hf0 : R.residue f ≠ 0 := by rw [hf]; exact hπ0
    have hfF0 : (f : FMp) ≠ 0 := by
      intro h0
      apply hf0
      have : f = 0 := Subtype.ext h0
      rw [this, map_zero]
    obtain ⟨D, hD, -⟩ := hPD.exists_divisor (f : FMp) hfF0
    have hQ : Finsupp.mapDomain r D Q = 1 := by rw [hdiv f hf0 D hD Q, hf, hordπ]
    have hmem : Q ∈ (Finsupp.mapDomain r D).support := by
      rw [Finsupp.mem_support_iff, hQ]; exact one_ne_zero
    obtain ⟨P, -, hP⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
    exact ⟨P, hP⟩
  ·
    intro f hf0 D hD
    obtain ⟨c, hc, hres0⟩ := R.exists_smul_mem f hf0
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hres0
      have : (⟨(0 : AlgebraicClosure ℚ) • f, hc⟩ : R.integers) = 0 := Subtype.ext (zero_smul _ f)
      rw [this, map_zero]
    refine ⟨R.residue ⟨c • f, hc⟩, hres0, fun v' => ?_⟩
    exact hdiv ⟨c • f, hc⟩ hres0 D (fun P => by rw [hD P]; exact (ConstantReduction.ord_smul P hc0 f).symm) v'

#print axioms solution

end S_ModularCurve_JHPlaceSpecialization_exists_regularProlongation_sp_gauss_res_qexp_mapDomain_unique_surjective
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_regularProlongation_sp_gauss_res_qexp_mapDomain_unique_surjective (solution)
