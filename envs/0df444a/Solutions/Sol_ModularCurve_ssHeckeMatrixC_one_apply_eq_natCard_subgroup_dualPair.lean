-- Prove2me | solution 1 for ModularCurve.ssHeckeMatrixC_one_apply_eq_natCard_subgroup_dualPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/9322653c-d265-5886-8118-61feb73d9c76

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq
import Theorems.Thm_ModularCurve_inertiaDegAlong_heckeAlphaC_eq_one
import Theorems.Thm_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_placeRamificationJ_charLGeomPlaceOfPoint_eq_one_and_placeWidth_eq_jWidth
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_exists_fullKernelHom
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
import Theorems.Thm_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_nsmul_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ssHeckeMatrixC_one_apply_eq_natCard_subgroup_dualPair
p2m_attr_erase "instance" "ModularCurve.ModuliTestDatum.isElliptic_reduced ModularCurve.ModuliTestDatum.isElliptic_curve ModularCurve.ModuliTestDatum.isElliptic_generic ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.ComapPlace.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_emb ModularCurve.ModuliTestDatum.restrictLevel_res ModularCurve.ModuliTestDatum.mk.injEq ModularCurve.ModuliTestDatum.restrictLevel_W ModularCurve.ModuliTestDatum.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_curve ModularCurve.ModuliTestDatum.resEquiv_apply ModularCurve.ModuliTestDatum.restrictLevel_gen ModularCurve.ModuliTestDatum.mk.sizeOf_spec ModularCurve.coe_jqNFull ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero"
p2m_attr_erase "simp" "ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun"
p2m_attr_erase "simp" "KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra CerednikDrinfeld ModularCurve P2MW.S_ModularCurve_ssHeckeMatrixC_one_apply_eq_natCard_subgroup_dualPair.ModularCurve AlgebraicCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "ssHeckeMatrixC charLDegeneracyRoof heckeAlphaC coe_heckeAlphaC heckeBetaC coe_heckeBetaC jqModC jqNModC modularFunctionFieldC modularFunctionFieldC_one qExpand placeRamificationJ IsSupersingularPlace ssPlaces IsSupersingularPlace.isCentreOf_evalAt jGeomGen charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq inertiaDegAlong_heckeAlphaC_eq_one exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul hasPrincipalDivisors_charLDegeneracyRoof eq_charLGeomPlaceOfPoint_of_ord_pos placeRamificationJ_charLGeomPlaceOfPoint_eq_one_and_placeWidth_eq_jWidth"
namespace RoofCountE7c
p2m_open "ModularCurve"

section Transport

variable {K F Z : Type*} [Field K] [Field F] [Field Z] [Algebra K F] [Algebra K Z]

def autPlace (σ : Z ≃ₐ[K] Z) : Place K Z ≃ Place K Z :=
  Place.congrEquiv σ.toRingEquiv (fun a => σ.commutes a)

theorem mem_autPlace_iff (σ : Z ≃ₐ[K] Z) (W : Place K Z) (z : Z) :
    z ∈ (autPlace σ W).toValuationSubring ↔ σ.symm z ∈ W.toValuationSubring :=
  Iff.rfl

theorem ord_autPlace (σ : Z ≃ₐ[K] Z) (W : Place K Z) (z : Z) : (autPlace σ W).ord (σ z) = W.ord z :=
  Place.ord_congrRingEquiv σ.toRingEquiv (fun a => σ.commutes a) W z

theorem restrictAlong_autPlace (σ : Z ≃ₐ[K] Z) {φ ψ : F →ₐ[K] Z} (hφ : φ.toRingHom.IsIntegral)
    (hψ : ψ.toRingHom.IsIntegral) (h : ∀ f, σ (ψ f) = φ f) (W : Place K Z) :
    (autPlace σ W).restrictAlong φ hφ = W.restrictAlong ψ hψ := by
  ext f
  show φ f ∈ (autPlace σ W).toValuationSubring ↔ ψ f ∈ W.toValuationSubring
  rw [mem_autPlace_iff, ← h, AlgEquiv.symm_apply_apply]

theorem ramificationIndexAlong_autPlace (σ : Z ≃ₐ[K] Z) {φ ψ : F →ₐ[K] Z} (h : ∀ f, σ (ψ f) = φ f)
    (W : Place K Z) : (autPlace σ W).ramificationIndexAlong φ = W.ramificationIndexAlong ψ := by
  show sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ (autPlace σ W).ord (φ f) = n} =
    sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ W.ord (ψ f) = n}
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => exists_congr fun f => and_congr_right fun _ => ?_
  rw [← h f, ord_autPlace]

end Transport

section Swap

variable (κ : Type*) [Field κ] (q' : ℕ) [CharP κ q'] (ℓ : ℕ) [NeZero ℓ]

theorem jqNModC_congr {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) : jqNModC κ a = jqNModC κ b := by
  subst h; rfl

theorem exists_swap (hq' : ¬ q' ∣ ℓ) (hℓ0 : (ℓ : κ) ≠ 0) :
    ∃ σ : charLDegeneracyRoof κ 1 ℓ ≃ₐ[κ] charLDegeneracyRoof κ 1 ℓ,
      (∀ f, σ (heckeAlphaC κ 1 ℓ f) = heckeBetaC κ 1 ℓ f) ∧
      (∀ f, σ (heckeBetaC κ 1 ℓ f) = heckeAlphaC κ 1 ℓ f) := by
  haveI : NeZero (1 * ℓ) := ⟨by simpa using NeZero.ne ℓ⟩
  have hroof : charLDegeneracyRoof κ 1 ℓ = modularFunctionFieldFullC κ (1 * ℓ) :=
    charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul κ q' 1 ℓ (by simpa using hq')
  obtain ⟨σ₀, h1, h2, -⟩ :=
    exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC κ (1 * ℓ) (by simpa using hℓ0)
  let ι : charLDegeneracyRoof κ 1 ℓ ≃ₐ[κ] modularFunctionFieldFullC κ (1 * ℓ) := IntermediateField.equivOfEq hroof
  let σ : charLDegeneracyRoof κ 1 ℓ ≃ₐ[κ] charLDegeneracyRoof κ 1 ℓ := (ι.trans σ₀).trans ι.symm
  have hιval : ∀ z : charLDegeneracyRoof κ 1 ℓ, ((ι z : modularFunctionFieldFullC κ (1 * ℓ)) : LaurentSeries κ) = z :=
    fun z => rfl
  have hιsval : ∀ z : modularFunctionFieldFullC κ (1 * ℓ), ((ι.symm z : charLDegeneracyRoof κ 1 ℓ) : LaurentSeries κ) = z :=
    fun z => rfl
  have hσval : ∀ z : charLDegeneracyRoof κ 1 ℓ, ((σ z : charLDegeneracyRoof κ 1 ℓ) : LaurentSeries κ) = σ₀ (ι z) := by
    intro z; rfl

  have hj : σ (heckeAlphaC κ 1 ℓ (jGeomGen κ 1)) = heckeBetaC κ 1 ℓ (jGeomGen κ 1) := by
    apply Subtype.ext
    rw [hσval, coe_heckeBetaC]
    have e1 : ι (heckeAlphaC κ 1 ℓ (jGeomGen κ 1)) = ⟨jqModC κ, jqModC_mem_full κ (1 * ℓ)⟩ := Subtype.ext rfl
    rw [e1, h1]
    show jqNModC κ (1 * ℓ) = qExpand κ ℓ (jqModC κ)
    exact jqNModC_congr κ (Nat.one_mul ℓ)
  have hjN : σ (heckeBetaC κ 1 ℓ (jGeomGen κ 1)) = heckeAlphaC κ 1 ℓ (jGeomGen κ 1) := by
    apply Subtype.ext
    rw [hσval, coe_heckeAlphaC]
    have e1 : ι (heckeBetaC κ 1 ℓ (jGeomGen κ 1)) = ⟨jqNModC κ (1 * ℓ), jqModCd_mem_full κ (1 * ℓ) (dvd_refl _)⟩ :=
      Subtype.ext (by rw [hιval, coe_heckeBetaC]; exact (jqNModC_congr κ (Nat.one_mul ℓ)).symm)
    rw [e1, h2]
    rfl

  have hext : ∀ (φ₁ φ₂ : modularFunctionFieldC κ 1 →ₐ[κ] charLDegeneracyRoof κ 1 ℓ),
      φ₁ (jGeomGen κ 1) = φ₂ (jGeomGen κ 1) → φ₁ = φ₂ := by
    intro φ₁ φ₂ hφ
    refine IntermediateField.algHom_ext_of_eq_adjoin κ (modularFunctionFieldC_one κ) fun x hx => ?_
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hφ
  refine ⟨σ, fun f => ?_, fun f => ?_⟩
  · exact AlgHom.congr_fun (hext (σ.toAlgHom.comp (heckeAlphaC κ 1 ℓ)) (heckeBetaC κ 1 ℓ) hj) f
  · exact AlgHom.congr_fun (hext (σ.toAlgHom.comp (heckeBetaC κ 1 ℓ)) (heckeAlphaC κ 1 ℓ) hjN) f

end Swap

section Entry

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
  (q' : ℕ) [Fact q'.Prime] [CharP κ q'] (ℓ : ℕ) [NeZero ℓ]

open Classical in

theorem entry_eq_finsum (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q')
    (hα : (heckeAlphaC κ 1 ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ 1 ℓ).toRingHom.IsIntegral)
    (x y : ↥(ssPlaces q' 1 κ)) :
    ssHeckeMatrixC q' κ 1 ℓ hα hβ y x =
      ∑ᶠ W : Place κ (charLDegeneracyRoof κ 1 ℓ),
        if W.restrictAlong (heckeAlphaC κ 1 ℓ) hα = x.1 ∧ W.restrictAlong (heckeBetaC κ 1 ℓ) hβ = y.1 then
          (W.ramificationIndexAlong (heckeAlphaC κ 1 ℓ) : ℤ) else 0 := by
  have hq'ℓ : ¬ q' ∣ ℓ := fun h => hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).mp h).symm
  have hℓ0 : (ℓ : κ) ≠ 0 := by
    intro h
    exact hq'ℓ ((CharP.cast_eq_zero_iff κ q' ℓ).mp h)
  obtain ⟨σ, hσα, hσβ⟩ := exists_swap κ q' ℓ hq'ℓ hℓ0
  rw [ssHeckeMatrixC, Matrix.of_apply, ← finsum_comp_equiv (autPlace σ)]
  refine finsum_congr fun W => ?_
  rw [restrictAlong_autPlace σ hβ hα hσα W, restrictAlong_autPlace σ hα hβ hσβ W,
    ramificationIndexAlong_autPlace σ hσα W, inertiaDegAlong_heckeAlphaC_eq_one κ 1 ℓ hα, Nat.cast_one, mul_one]

end Entry

section Isogeny

open WeierstrassCurve Polynomial
open scoped Polynomial.Bivariate

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

omit [IsAlgClosed κ] [DecidableEq κ] in
theorem some_eq_some {V : WeierstrassCurve.Affine κ} {x₁ y₁ x₂ y₂ : κ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

theorem nsmul_id_mem_rationalHomSet (W : WeierstrassCurve κ) [W.IsElliptic] (n : ℕ) :
    (n • AddMonoidHom.id _ : (W.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point) ∈
      rationalHomSet κ W W := by
  induction n with
  | zero => rw [zero_nsmul]; exact zero_mem_rationalHomSet κ W W
  | succ n ih => rw [succ_nsmul]; exact add_mem_rationalHomSet κ W W ih (id_mem_rationalHomSet κ W)

omit [IsAlgClosed κ] [DecidableEq κ] in

theorem evalEvalBC_self (p : κ[X][Y]) (x y : κ) : evalEvalBC κ p x y = p.evalEval x y := by
  simp [evalEvalBC, Polynomial.map_id, Algebra.algebraMap_self]

omit [IsAlgClosed κ] in

theorem exists_rational_addEquiv (A : WeierstrassCurve κ) (γ : VariableChange κ) :
    ∃ e : A.toAffine.Point ≃+ (γ • A).toAffine.Point,
      (e.toAddMonoidHom ∈ rationalHomSet κ A (γ • A)) ∧ (e.symm.toAddMonoidHom ∈ rationalHomSet κ (γ • A) A) := by
  obtain ⟨e, he⟩ := exists_addEquiv_point_variableChange A γ
  have e1 : ∀ x y : κ, evalEvalBC κ (1 : κ[X][Y]) x y = 1 := fun x y => by
    rw [evalEvalBC_self]; simp only [evalEval_one]
  refine ⟨e, Or.inr ?_, Or.inr ?_⟩
  ·
    refine ⟨C (C (((γ.u⁻¹ : κˣ) : κ) ^ 2) * (X - C γ.r)), 1,
      C (C (((γ.u⁻¹ : κˣ) : κ) ^ 3)) * (Polynomial.X - C (C γ.s * X) + C (C (γ.s * γ.r - γ.t))), 1,
      ∅, Set.finite_empty, fun x y h _ => ?_⟩
    obtain ⟨h', hh⟩ := he x y h
    have ex : evalEvalBC κ (C (C (((γ.u⁻¹ : κˣ) : κ) ^ 2) * (X - C γ.r)) : κ[X][Y]) x y / evalEvalBC κ (1 : κ[X][Y]) x y =
        ((γ.u⁻¹ : κˣ) : κ) ^ 2 * (x - γ.r) := by
      rw [e1, div_one, evalEvalBC_self]
      simp only [evalEval_C, eval_C, eval_X, eval_mul, eval_sub]
    have ey : evalEvalBC κ (C (C (((γ.u⁻¹ : κˣ) : κ) ^ 3)) * (Polynomial.X - C (C γ.s * X) + C (C (γ.s * γ.r - γ.t))) :
          κ[X][Y]) x y / evalEvalBC κ (1 : κ[X][Y]) x y =
        ((γ.u⁻¹ : κˣ) : κ) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t)) := by
      rw [e1, div_one, evalEvalBC_self]
      simp only [evalEval_C, evalEval_X, evalEval_mul, evalEval_add, evalEval_sub, eval_C, eval_X, eval_mul]
    refine ⟨by rw [e1]; exact one_ne_zero, by rw [e1]; exact one_ne_zero, (by rw [ex, ey]; exact h'), ?_⟩
    show e (Affine.Point.some x y h) = _
    rw [hh]
    exact some_eq_some ex.symm ey.symm
  ·
    have key : ∀ (x' y' : κ) (h' : (γ • A).toAffine.Nonsingular x' y'),
        e.symm (.some x' y' h') = .some (Affine.vcX γ x') (Affine.vcY γ x' y')
          ((Affine.nonsingular_variableChange_iff x' y').mp h') := by
      intro x' y' h'
      apply e.injective
      rw [e.apply_symm_apply]
      obtain ⟨h'', hh⟩ := he (Affine.vcX γ x') (Affine.vcY γ x' y') ((Affine.nonsingular_variableChange_iff x' y').mp h')
      rw [hh]
      have hu : ((γ.u : κˣ) : κ) ≠ 0 := γ.u.ne_zero
      apply some_eq_some
      · simp only [Affine.vcX, Units.val_inv_eq_inv_val]; field_simp; ring
      · simp only [Affine.vcX, Affine.vcY, Units.val_inv_eq_inv_val]; field_simp; ring
    refine ⟨C (C (((γ.u : κˣ) : κ) ^ 2) * X + C γ.r), 1,
      C (C (((γ.u : κˣ) : κ) ^ 3)) * Polynomial.X + C (C (((γ.u : κˣ) : κ) ^ 2 * γ.s) * X + C γ.t), 1,
      ∅, Set.finite_empty, fun x' y' h' _ => ?_⟩
    have ex : evalEvalBC κ (C (C (((γ.u : κˣ) : κ) ^ 2) * X + C γ.r) : κ[X][Y]) x' y' / evalEvalBC κ (1 : κ[X][Y]) x' y' =
        Affine.vcX γ x' := by
      rw [e1, div_one, evalEvalBC_self, Affine.vcX]
      simp only [evalEval_C, eval_C, eval_X, eval_mul, eval_add]
    have ey : evalEvalBC κ (C (C (((γ.u : κˣ) : κ) ^ 3)) * Polynomial.X + C (C (((γ.u : κˣ) : κ) ^ 2 * γ.s) * X + C γ.t) :
          κ[X][Y]) x' y' / evalEvalBC κ (1 : κ[X][Y]) x' y' = Affine.vcY γ x' y' := by
      rw [e1, div_one, evalEvalBC_self, Affine.vcY]
      simp only [evalEval_C, evalEval_X, evalEval_mul, evalEval_add, eval_C, eval_X, eval_mul, eval_add]
      ring
    refine ⟨by rw [e1]; exact one_ne_zero, by rw [e1]; exact one_ne_zero,
      (by rw [ex, ey]; exact (Affine.nonsingular_variableChange_iff x' y').mp h'), ?_⟩
    show e.symm (Affine.Point.some x' y' h') = _
    rw [key x' y' h']
    exact some_eq_some ex.symm ey.symm

theorem surjective_and_exists_dual_of_universal (E A : WeierstrassCurve κ) [E.IsElliptic] [A.IsElliptic]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ0 : (ℓ : κ) ≠ 0) (Q : E.toAffine.Point) (hQ : addOrderOf Q = ℓ)
    (φ : (E.baseChange κ).toAffine.Point →+ (A.baseChange κ).toAffine.Point) (hφ : φ ∈ rationalHomSet κ E A)
    (hker : φ.ker = AddSubgroup.zmultiples Q)
    (huniv : ∀ (V : WeierstrassCurve κ) [V.IsElliptic]
      (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
        α ∈ rationalHomSet κ E V → α Q = 0 → ∃ β ∈ rationalHomSet κ A V, α = β.comp φ) :
    Function.Surjective φ ∧
      ∃ φ' ∈ rationalHomSet κ A E, φ'.comp φ = ℓ • AddMonoidHom.id _ ∧ φ.comp φ' = ℓ • AddMonoidHom.id _ := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hQ
    exact hℓ.one_lt.ne hQ
  have hℓQ : ℓ • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hφ0 : φ ≠ 0 := by
    intro h0
    obtain ⟨T₀, hT₀⟩ := exists_nsmul_eq_of_isAlgClosed E ℓ hℓ0 Q
    let T : (E.baseChange κ).toAffine.Point := T₀
    have hT : ℓ • T = Q := hT₀
    have hTker : T ∈ φ.ker := by rw [h0]; trivial
    rw [hker] at hTker
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hTker
    apply hQ0
    have hkQ : ℓ • (k • Q) = 0 := by rw [smul_comm, hℓQ, smul_zero]
    have hk' : (k • Q : (E.baseChange κ).toAffine.Point) = T := hk
    rw [← hT]
    show ℓ • T = 0
    rw [← hk']
    exact hkQ
  have hsurj : Function.Surjective φ := surjective_of_mem_rationalHomSet κ hφ hφ0
  have hℓQ' : (ℓ • AddMonoidHom.id (E.baseChange κ).toAffine.Point) Q = 0 := hℓQ
  obtain ⟨φ', hφ', hcomp⟩ := huniv E (ℓ • AddMonoidHom.id _) (nsmul_id_mem_rationalHomSet E ℓ) hℓQ'
  refine ⟨hsurj, φ', hφ', hcomp.symm, ?_⟩
  have L : ∀ R : (E.baseChange κ).toAffine.Point, φ' (φ R) = ℓ • R := fun R => (DFunLike.congr_fun hcomp R).symm
  ext P
  obtain ⟨R, rfl⟩ := hsurj P
  show φ (φ' (φ R)) = ℓ • φ R
  rw [L, map_nsmul]

theorem velu_package (E : WeierstrassCurve κ) [E.IsElliptic] {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓ0 : (ℓ : κ) ≠ 0)
    (Q : E.toAffine.Point) (hQ : addOrderOf Q = ℓ) :
    ∃ _ : (E.fullKernelQuotient Q ℓ).Δ ≠ 0,
    ∃ φ : (E.baseChange κ).toAffine.Point →+ ((E.fullKernelQuotient Q ℓ).baseChange κ).toAffine.Point,
      φ ∈ rationalHomSet κ E (E.fullKernelQuotient Q ℓ) ∧
      φ.ker = AddSubgroup.zmultiples Q ∧ Function.Surjective φ ∧
      (∃ φ' ∈ rationalHomSet κ (E.fullKernelQuotient Q ℓ) E,
          φ'.comp φ = ℓ • AddMonoidHom.id _ ∧ φ.comp φ' = ℓ • AddMonoidHom.id _) ∧
      ∀ (V : WeierstrassCurve κ) [V.IsElliptic]
        (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
        α ∈ rationalHomSet κ E V → α Q = 0 →
          ∃ β ∈ rationalHomSet κ (E.fullKernelQuotient Q ℓ) V, α = β.comp φ := by
  have hΔ : (E.fullKernelQuotient Q ℓ).Δ ≠ 0 := fullKernelQuotient_discriminant_ne_zero ℓ E hℓ0 Q hQ
  refine ⟨hΔ, ?_⟩

  suffices H : ∃ φ : (E.baseChange κ).toAffine.Point →+ ((E.fullKernelQuotient Q ℓ).baseChange κ).toAffine.Point,
      φ ∈ rationalHomSet κ E (E.fullKernelQuotient Q ℓ) ∧ φ.ker = AddSubgroup.zmultiples Q ∧
      ∀ (V : WeierstrassCurve κ) [V.IsElliptic]
        (α : (E.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point),
        α ∈ rationalHomSet κ E V → α Q = 0 →
          ∃ β ∈ rationalHomSet κ (E.fullKernelQuotient Q ℓ) V, α = β.comp φ by
    haveI hA : (E.fullKernelQuotient Q ℓ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    obtain ⟨φ, hφ, hker, huniv⟩ := H
    obtain ⟨hsurj, hdual⟩ := surjective_and_exists_dual_of_universal E _ hℓ hℓ0 Q hQ φ hφ hker huniv
    exact ⟨φ, hφ, hker, hsurj, hdual, huniv⟩
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hQ
    exact hℓ.one_lt.ne hQ
  have hℓQ : ℓ • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  rcases hℓ.eq_two_or_odd' with h2 | hodd
  ·
    subst h2
    rcases Q with _ | ⟨x₀, y₀, hns⟩
    · exact absurd rfl hQ0
    have hneg : -(Affine.Point.some x₀ y₀ hns) = Affine.Point.some x₀ y₀ hns := by
      rw [neg_eq_iff_add_eq_zero, ← two_nsmul, hℓQ]
    have hy₀ : E.toAffine.negY x₀ y₀ = y₀ := by
      rw [Affine.Point.neg_some] at hneg
      exact ((Affine.Point.some.injEq _ _ _ _ _ _).mp hneg).2
    have hgy : E.veluGy x₀ y₀ = 0 := E.veluGy_eq_zero_of_negY_eq hy₀
    have hA2 : E.fullKernelQuotient (.some x₀ y₀ hns) 2 = E.veluQuotient2 x₀ y₀ := fullKernelQuotient_two E hns hgy
    have hΔ2 : (E.veluQuotient2 x₀ y₀).Δ ≠ 0 := hA2 ▸ hΔ
    obtain ⟨π₀, hπcoe, hπrat, -, hπuniv⟩ :=
      exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul hℓ0 E hns.1 hgy hΔ2
    rw [hA2]
    let π : (E.baseChange κ).toAffine.Point →+ ((E.veluQuotient2 x₀ y₀).baseChange κ).toAffine.Point := π₀
    have hπapp : ∀ P : E.toAffine.Point, π P = veluPointMap2 hℓ0 hns.1 hgy hΔ2 P := fun P => by
      show π₀ P = _; rw [hπcoe]
    have hπQ : π (.some x₀ y₀ hns) = 0 := by
      rw [hπapp]; exact veluPointMap2_some_of_eq hℓ0 hns.1 hgy hΔ2 hns rfl
    have hπker : π.ker = AddSubgroup.zmultiples (Affine.Point.some x₀ y₀ hns) := by
      refine le_antisymm ?_ ((AddSubgroup.zmultiples_le_of_mem) hπQ)
      intro P hP
      rw [AddMonoidHom.mem_ker] at hP
      rcases P with _ | ⟨x, y, h⟩
      · exact zero_mem _
      · by_cases hx : x = x₀
        · subst hx
          have hy : y = y₀ := by
            rcases eq_or_ne y (E.toAffine.negY x y₀) with h1 | h1
            · rw [h1, hy₀]
            · exact Affine.Y_eq_of_Y_ne h.1 hns.1 rfl h1
          subst hy
          exact AddSubgroup.mem_zmultiples _
        · exfalso
          rw [hπapp] at hP
          exact Affine.Point.some_ne_zero _ ((veluPointMap2_some_of_ne hℓ0 hns.1 hgy hΔ2 h hx).symm.trans hP)
    refine ⟨π, hπrat, hπker, fun V _ α hα hαQ => ?_⟩
    refine hπuniv V inferInstance α hα fun T hT => ?_
    have hT' : T ∈ π.ker := hT
    rw [hπker] at hT'
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT'
    rw [map_zsmul]
    exact (congrArg (k • ·) hαQ).trans (smul_zero k)
  ·
    have hℓ2 : ℓ ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have hℓn : ℓ = 2 * (ℓ / 2) + 1 := (Nat.two_mul_div_two_add_one_of_odd hodd).symm
    have hQ' : addOrderOf Q = 2 * (ℓ / 2) + 1 := hQ.trans hℓn
    have hAv : E.fullKernelQuotient Q ℓ = E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)) := by
      have h := fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet E Q (ℓ / 2) hQ'
      rwa [← hℓn] at h
    obtain ⟨φ₀, hker, hφ₀⟩ := exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed E hℓ hℓ2 hℓ0 Q hQ
    obtain ⟨hφrat, huniv⟩ :=
      veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq E (ℓ / 2) Q hQ' φ₀ hker hφ₀
    rw [hAv]
    exact ⟨φ₀, hφrat, hker, fun V _ α hα hαQ => huniv V α hα hαQ⟩

theorem nonempty_variableChange_iff_exists_dualPair (E E' : WeierstrassCurve κ) [E.IsElliptic] [E'.IsElliptic]
    {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓ0 : (ℓ : κ) ≠ 0) (Q : E.toAffine.Point) (hQ : addOrderOf Q = ℓ) :
    (∃ γ : VariableChange κ, γ • E.fullKernelQuotient Q ℓ = E') ↔
      ∃ ψ ∈ rationalHomSet κ E E', ∃ ψ' ∈ rationalHomSet κ E' E,
        ψ.ker = AddSubgroup.zmultiples Q ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ := by
  obtain ⟨hΔ, φ, hφ, hker, hsurj, ⟨φ', hφ', h1, h2⟩, huniv⟩ := velu_package E hℓ hℓ0 Q hQ
  haveI hA : (E.fullKernelQuotient Q ℓ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have L1 : ∀ R : (E.baseChange κ).toAffine.Point, φ' (φ R) = ℓ • R := fun R => DFunLike.congr_fun h1 R
  have L2 : ∀ P : ((E.fullKernelQuotient Q ℓ).baseChange κ).toAffine.Point, φ (φ' P) = ℓ • P :=
    fun P => DFunLike.congr_fun h2 P
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨e, he, hes⟩ := exists_rational_addEquiv (E.fullKernelQuotient Q ℓ) γ
    let eb : ((E.fullKernelQuotient Q ℓ).baseChange κ).toAffine.Point →+
        ((γ • E.fullKernelQuotient Q ℓ).baseChange κ).toAffine.Point := e.toAddMonoidHom
    let eb' : ((γ • E.fullKernelQuotient Q ℓ).baseChange κ).toAffine.Point →+
        ((E.fullKernelQuotient Q ℓ).baseChange κ).toAffine.Point := e.symm.toAddMonoidHom
    have heb : eb ∈ rationalHomSet κ (E.fullKernelQuotient Q ℓ) (γ • E.fullKernelQuotient Q ℓ) := he
    have heb' : eb' ∈ rationalHomSet κ (γ • E.fullKernelQuotient Q ℓ) (E.fullKernelQuotient Q ℓ) := hes
    have K1 : ∀ R, eb' (eb R) = R := fun R => e.symm_apply_apply R
    have K2 : ∀ P, eb (eb' P) = P := fun P => e.apply_symm_apply P
    have K3 : ∀ R, eb R = 0 ↔ R = 0 := fun R => e.map_eq_zero_iff
    refine ⟨eb.comp φ, comp_mem_rationalHomSet κ _ _ _ hφ heb, φ'.comp eb', comp_mem_rationalHomSet κ _ _ _ heb' hφ',
      ?_, ?_, ?_⟩
    · rw [← hker]
      ext P
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
      exact K3 (φ P)
    · ext P
      show φ' (eb' (eb (φ P))) = ℓ • P
      rw [K1, L1]
    · ext P
      show eb (φ (φ' (eb' P))) = ℓ • P
      rw [L2, map_nsmul, K2]
  · rintro ⟨ψ, hψ, ψ', hψ', hkerψ, hψ'ψ, hψψ'⟩
    have Lψ'ψ : ∀ P : (E.baseChange κ).toAffine.Point, ψ' (ψ P) = ℓ • P := fun P => DFunLike.congr_fun hψ'ψ P
    have Lψψ' : ∀ P' : (E'.baseChange κ).toAffine.Point, ψ (ψ' P') = ℓ • P' := fun P' => DFunLike.congr_fun hψψ' P'
    have hψQ : ψ Q = 0 := by
      rw [← AddMonoidHom.mem_ker, hkerψ]; exact AddSubgroup.mem_zmultiples _
    obtain ⟨β, hβ, hψβ⟩ := huniv E' ψ hψ hψQ
    have Lψ : ∀ P, ψ P = β (φ P) := fun P => by rw [hψβ]; rfl

    have hβd : φ.comp ψ' ∈ rationalHomSet κ E' (E.fullKernelQuotient Q ℓ) := comp_mem_rationalHomSet κ _ _ _ hψ' hφ
    have hkill : ∀ P' : (E'.baseChange κ).toAffine.Point, (ℓ : ℤ) • P' = 0 → (φ.comp ψ') P' = 0 := by
      intro P' hP'
      show φ (ψ' P') = 0
      rw [← AddMonoidHom.mem_ker, hker, ← hkerψ, AddMonoidHom.mem_ker, Lψψ', ← natCast_zsmul, hP']
    obtain ⟨ε, hε, hεeq⟩ :=
      exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ E' (E.fullKernelQuotient Q ℓ) hℓ0 hβd hkill
    have Lε : ∀ P' : (E'.baseChange κ).toAffine.Point, φ (ψ' P') = ℓ • ε P' := fun P' => by
      rw [← natCast_zsmul]; exact hεeq P'

    have hεβ : ε.comp β = AddMonoidHom.id _ := by
      ext P₀
      show ε (β P₀) = P₀
      obtain ⟨R₁, hR₁⟩ := exists_nsmul_eq_of_isAlgClosed (E.fullKernelQuotient Q ℓ) ℓ hℓ0 P₀
      obtain ⟨R₀, hR₀⟩ := hsurj R₁
      have hR : ℓ • φ R₀ = P₀ := by rw [hR₀]; exact hR₁
      rw [← hR, map_nsmul, map_nsmul, ← Lε, ← Lψ, Lψ'ψ, map_nsmul]

    have hβε : β.comp ε = AddMonoidHom.id _ := by
      ext P'
      show β (ε P') = P'
      obtain ⟨R₁, hR₁⟩ := exists_nsmul_eq_of_isAlgClosed E' ℓ hℓ0 P'
      let R' : (E'.baseChange κ).toAffine.Point := R₁
      have hR : ℓ • R' = P' := hR₁
      rw [← hR, map_nsmul, ← Lε, ← Lψ, Lψψ']
    exact exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet κ (E.fullKernelQuotient Q ℓ) E' β hβ ε hε hεβ hβε

end Isogeny

section Dictionary

variable {κ : Type} [Field κ] [DecidableEq κ] (q' : ℕ) (ℓ : ℕ) [NeZero ℓ]

theorem eq_charLGeomPlaceOfPoint_evalAt (x : ↥(ssPlaces q' 1 κ)) :
    x.1 = charLGeomPlaceOfPoint κ ((x.1).evalAt (jGeomGen κ 1)) :=
  ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos (IsSupersingularPlace.isCentreOf_evalAt x.2).1

theorem eq_iff_of_ord_pos {P : Place κ (modularFunctionFieldC κ 1)} {c : κ}
    (h : 0 < P.ord (jGeomGen κ 1 - algebraMap κ (modularFunctionFieldC κ 1) c)) (y : ↥(ssPlaces q' 1 κ)) :
    P = y.1 ↔ c = (y.1).evalAt (jGeomGen κ 1) := by
  have hP := ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos h
  have hy := eq_charLGeomPlaceOfPoint_evalAt q' y
  constructor
  · intro e; exact charLGeomPlaceOfPoint_injective κ (hP.symm.trans (e.trans hy))
  · intro e; rw [hP, e]; exact hy.symm

theorem ord_jGeomGen_sub_evalAt (x : ↥(ssPlaces q' 1 κ)) :
    (x.1).ord (jGeomGen κ 1 - algebraMap κ (modularFunctionFieldC κ 1) ((x.1).evalAt (jGeomGen κ 1))) = 1 := by
  have h := (placeRamificationJ_charLGeomPlaceOfPoint_eq_one_and_placeWidth_eq_jWidth
    ((x.1).evalAt (jGeomGen κ 1))).1
  rw [← eq_charLGeomPlaceOfPoint_evalAt q' x] at h
  unfold placeRamificationJ at h
  omega

omit [DecidableEq κ] in

theorem ord_heckeAlphaC_sub (hα : (heckeAlphaC κ 1 ℓ).toRingHom.IsIntegral) (c : κ)
    (W : Place κ (charLDegeneracyRoof κ 1 ℓ)) :
    W.ord (heckeAlphaC κ 1 ℓ (jGeomGen κ 1) - algebraMap κ (charLDegeneracyRoof κ 1 ℓ) c) =
      W.ramificationIndexAlong (heckeAlphaC κ 1 ℓ) *
        (W.restrictAlong (heckeAlphaC κ 1 ℓ) hα).ord (jGeomGen κ 1 - algebraMap κ (modularFunctionFieldC κ 1) c) := by
  rw [← Place.ord_restrictAlong, map_sub, AlgHom.commutes]

omit [DecidableEq κ] in
theorem ramificationIndexAlong_heckeAlphaC_pos (hα : (heckeAlphaC κ 1 ℓ).toRingHom.IsIntegral)
    (W : Place κ (charLDegeneracyRoof κ 1 ℓ)) : 0 < W.ramificationIndexAlong (heckeAlphaC κ 1 ℓ) := by
  letI := algebraAlong (heckeAlphaC κ 1 ℓ)
  haveI := isIntegral_along (heckeAlphaC κ 1 ℓ) hα
  exact W.ramificationIndex_pos

theorem restrictAlong_heckeAlphaC_eq_iff (hα : (heckeAlphaC κ 1 ℓ).toRingHom.IsIntegral) (x : ↥(ssPlaces q' 1 κ))
    (W : Place κ (charLDegeneracyRoof κ 1 ℓ)) :
    W.restrictAlong (heckeAlphaC κ 1 ℓ) hα = x.1 ↔
      0 < W.ord (heckeAlphaC κ 1 ℓ (jGeomGen κ 1) -
        algebraMap κ (charLDegeneracyRoof κ 1 ℓ) ((x.1).evalAt (jGeomGen κ 1))) := by
  have hepos := ramificationIndexAlong_heckeAlphaC_pos ℓ hα W
  rw [ord_heckeAlphaC_sub ℓ hα]
  constructor
  · intro h
    rw [h, ord_jGeomGen_sub_evalAt q' x, mul_one]
    exact_mod_cast hepos
  · intro h
    apply (eq_iff_of_ord_pos q' ?_ x).mpr rfl
    by_contra hle
    push Not at hle
    have : (W.ramificationIndexAlong (heckeAlphaC κ 1 ℓ) : ℤ) *
        (W.restrictAlong (heckeAlphaC κ 1 ℓ) hα).ord (jGeomGen κ 1 -
          algebraMap κ (modularFunctionFieldC κ 1) ((x.1).evalAt (jGeomGen κ 1))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    omega

theorem ramificationIndexAlong_heckeAlphaC_eq_ord (hα : (heckeAlphaC κ 1 ℓ).toRingHom.IsIntegral)
    (x : ↥(ssPlaces q' 1 κ)) (W : Place κ (charLDegeneracyRoof κ 1 ℓ))
    (hW : W.restrictAlong (heckeAlphaC κ 1 ℓ) hα = x.1) :
    (W.ramificationIndexAlong (heckeAlphaC κ 1 ℓ) : ℤ) =
      W.ord (heckeAlphaC κ 1 ℓ (jGeomGen κ 1) -
        algebraMap κ (charLDegeneracyRoof κ 1 ℓ) ((x.1).evalAt (jGeomGen κ 1))) := by
  rw [ord_heckeAlphaC_sub ℓ hα, hW, ord_jGeomGen_sub_evalAt q' x, mul_one]

end Dictionary

section Subgroups

variable {G : Type*} [AddCommGroup G]

def botOne : {C : AddSubgroup G // IsAddCyclic C ∧ Nat.card C = 1} :=
  ⟨⊥, ⟨inferInstance, AddSubgroup.card_bot⟩⟩

theorem exists_zmultiples_eq (C : AddSubgroup G) (hC : IsAddCyclic C) (n : ℕ) (hn : Nat.card C = n) :
    ∃ Q : G, AddSubgroup.zmultiples Q = C ∧ addOrderOf Q = n := by
  obtain ⟨Q, hQ⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top C).mp hC
  refine ⟨Q, hQ, ?_⟩
  rw [← Nat.card_zmultiples, hQ, hn]

end Subgroups

section Count

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
  (q' : ℕ) [Fact q'.Prime] [CharP κ q']

open WeierstrassCurve

abbrev CycSub (E : WeierstrassCurve κ) (n : ℕ) : Type :=
  {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = n}

set_option maxHeartbeats 6400000 in

theorem ssHeckeMatrixC_one_apply_eq
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q')
    (hα : (heckeAlphaC κ 1 ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ 1 ℓ).toRingHom.IsIntegral)
    (x y : ↥(ssPlaces q' 1 κ))
    (E_x E_y : WeierstrassCurve κ) [E_x.IsElliptic] [E_y.IsElliptic]
    (hx : E_x.j = (x.1).evalAt (jGeomGen κ 1)) (hy : E_y.j = (y.1).evalAt (jGeomGen κ 1)) :
    ssHeckeMatrixC q' κ 1 ℓ hα hβ y x =
      (Nat.card {C : AddSubgroup (E_x.baseChange κ).toAffine.Point //
        Nat.card C = ℓ ∧ ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E_x E_y, ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E_y E_x,
          ψ.ker = C ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _} : ℤ) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hq'ℓ : ¬ q' ∣ ℓ := fun h => hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).mp h).symm
  have hℓ0 : (ℓ : κ) ≠ 0 := fun h => hq'ℓ ((CharP.cast_eq_zero_iff κ q' ℓ).mp h)
  have hℓ1 : ((1 * ℓ : ℕ) : κ) ≠ 0 := by rwa [Nat.one_mul]
  have h10 : ((1 : ℕ) : κ) ≠ 0 := by rw [Nat.cast_one]; exact one_ne_zero
  haveI : HasPrincipalDivisors κ (charLDegeneracyRoof κ 1 ℓ) := hasPrincipalDivisors_charLDegeneracyRoof κ 1 ℓ h10 hℓ0

  obtain ⟨g, f, hg1, -, -, -, hf1, hf2, -, hf4, -, -, hfb⟩ :=
    exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq κ 1 ℓ hℓ hℓ1 hα hβ
      ((x.1).evalAt (jGeomGen κ 1)) E_x hx

  have hfx : ∀ C, (f C).restrictAlong (heckeAlphaC κ 1 ℓ) hα = x.1 := fun C =>
    (restrictAlong_heckeAlphaC_eq_iff q' ℓ hα x (f C)).mpr (hf1 C)

  have hef : ∀ C, ((f C).ramificationIndexAlong (heckeAlphaC κ 1 ℓ) : ℤ) =
      Nat.card {C' : CycSub E_x (1 * ℓ) // f C' = f C} := by
    intro C
    rw [ramificationIndexAlong_heckeAlphaC_eq_ord q' ℓ hα x (f C) (hfx C)]
    exact hf4 C

  have hfsurj : ∀ W : Place κ (charLDegeneracyRoof κ 1 ℓ), W.restrictAlong (heckeAlphaC κ 1 ℓ) hα = x.1 → ∃ C, f C = W :=
    fun W hW => hf2 W ((restrictAlong_heckeAlphaC_eq_iff q' ℓ hα x W).mp hW)

  have hiv : ∀ C : CycSub E_x (1 * ℓ),
      (f C).restrictAlong (heckeBetaC κ 1 ℓ) hβ = y.1 ↔
        ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E_x E_y, ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E_y E_x,
          ψ.ker = C.1 ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ := by
    intro C
    obtain ⟨Q, hQC, hQord⟩ := exists_zmultiples_eq C.1 C.2.1 (1 * ℓ) C.2.2
    rw [Nat.one_mul] at hQord
    have hQmem : Q ∈ C.1 := hQC ▸ AddSubgroup.mem_zmultiples Q
    have hΔ : (E_x.fullKernelQuotient Q ℓ).Δ ≠ 0 := fullKernelQuotient_discriminant_ne_zero ℓ E_x hℓ0 Q hQord
    haveI hA : (E_x.fullKernelQuotient Q ℓ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    obtain ⟨φ, hφker, hφ⟩ := exists_fullKernelHom E_x hℓ0 Q hQord
    have hlaw := hfb C Q hQmem hQord hΔ φ hφker hφ botOne (fun T hT => by
      have hT' : T ∈ φ.ker := by rw [hφker, hQC]; exact hT
      exact (AddSubgroup.mem_bot).mpr hT')
    rw [hlaw, eq_iff_of_ord_pos q' (hg1 (E_x.fullKernelQuotient Q ℓ) botOne) y, show (y.1).evalAt (jGeomGen κ 1) = E_y.j from hy.symm]
    have hj : (E_x.fullKernelQuotient Q ℓ).j = E_y.j ↔ ∃ γ : VariableChange κ, γ • E_x.fullKernelQuotient Q ℓ = E_y := by
      constructor
      · exact WeierstrassCurve.exists_variableChange_of_j_eq _ _
      · rintro ⟨γ, rfl⟩
        exact (WeierstrassCurve.variableChange_j _ γ).symm
    rw [hj, nonempty_variableChange_iff_exists_dualPair E_x E_y hℓ hℓ0 Q hQord]
    refine exists_congr fun ψ => and_congr_right fun _ => exists_congr fun ψ' => and_congr_right fun _ =>
      and_congr_left' ?_
    exact ⟨fun h => h.trans hQC, fun h => h.trans hQC.symm⟩

  set T : Finset (Place κ (charLDegeneracyRoof κ 1 ℓ)) := Place.fiberAlong (heckeAlphaC κ 1 ℓ) hα x.1 with hT
  have hmemT : ∀ W, W ∈ T ↔ W.restrictAlong (heckeAlphaC κ 1 ℓ) hα = x.1 := fun W => Place.mem_fiberAlong
  have hfT : ∀ C, f C ∈ T := fun C => (hmemT _).mpr (hfx C)
  have hfibfin : ∀ W : Place κ (charLDegeneracyRoof κ 1 ℓ),
      Finite {C' : CycSub E_x (1 * ℓ) // f C' = W} := by
    intro W
    by_cases h : ∃ C, f C = W
    · obtain ⟨C, rfl⟩ := h
      apply Nat.finite_of_card_ne_zero
      have := hef C
      have hpos := ramificationIndexAlong_heckeAlphaC_pos ℓ hα (f C)
      omega
    · haveI : IsEmpty {C' : CycSub E_x (1 * ℓ) // f C' = W} :=
        ⟨fun C' => h ⟨C'.1, C'.2⟩⟩
      infer_instance
  haveI hSfin : Finite (CycSub E_x (1 * ℓ)) := by
    haveI : ∀ W : T, Finite {C' : CycSub E_x (1 * ℓ) // f C' = W.1} := fun W => hfibfin W.1
    exact Finite.of_surjective (fun p : Σ W : T, {C' : CycSub E_x (1 * ℓ) // f C' = W.1} => p.2.1)
      fun C => ⟨⟨⟨f C, hfT C⟩, C, rfl⟩, rfl⟩

  rw [entry_eq_finsum q' ℓ hℓ hℓq hα hβ x y]
  rw [finsum_eq_sum_of_support_subset _ (s := T) (by
    intro W hW
    rw [Function.mem_support] at hW
    rw [Finset.mem_coe, hmemT]
    by_contra hx'
    exact hW (if_neg fun h => hx' h.1))]
  have hLHS : (∑ W ∈ T, if W.restrictAlong (heckeAlphaC κ 1 ℓ) hα = x.1 ∧ W.restrictAlong (heckeBetaC κ 1 ℓ) hβ = y.1 then
        (W.ramificationIndexAlong (heckeAlphaC κ 1 ℓ) : ℤ) else 0) =
      ∑ W ∈ T.filter (fun W => W.restrictAlong (heckeBetaC κ 1 ℓ) hβ = y.1),
        (W.ramificationIndexAlong (heckeAlphaC κ 1 ℓ) : ℤ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    have hWx := (hmemT W).mp hW
    by_cases hWy : W.restrictAlong (heckeBetaC κ 1 ℓ) hβ = y.1
    · rw [if_pos ⟨hWx, hWy⟩, if_pos hWy]
    · rw [if_neg fun h => hWy h.2, if_neg hWy]
  rw [hLHS]

  set T' := T.filter (fun W => W.restrictAlong (heckeBetaC κ 1 ℓ) hβ = y.1) with hT'
  have hcount : Nat.card {C : AddSubgroup (E_x.baseChange κ).toAffine.Point //
        Nat.card C = ℓ ∧ ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E_x E_y, ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E_y E_x,
          ψ.ker = C ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _} =
      Nat.card {C : CycSub E_x (1 * ℓ) // (f C).restrictAlong (heckeBetaC κ 1 ℓ) hβ = y.1} := by
    refine Nat.card_eq_of_bijective
      (fun C => ⟨⟨C.1, isAddCyclic_of_prime_card C.2.1, by rw [Nat.one_mul]; exact C.2.1⟩, (hiv _).mpr C.2.2⟩)
      ⟨fun C₁ C₂ h => Subtype.ext (congrArg (fun D : {C : CycSub E_x (1 * ℓ) // _} => (D.1.1 : AddSubgroup E_x.toAffine.Point)) h),
        fun D => ⟨⟨D.1.1, D.1.2.2.trans (Nat.one_mul ℓ), (hiv D.1).mp D.2⟩, rfl⟩⟩
  have hsigma : Nat.card {C : CycSub E_x (1 * ℓ) // (f C).restrictAlong (heckeBetaC κ 1 ℓ) hβ = y.1} =
      Nat.card (Σ W : T', {C' : CycSub E_x (1 * ℓ) // f C' = W.1}) := by
    refine Nat.card_congr
      { toFun := fun C => ⟨⟨f C.1, Finset.mem_filter.mpr ⟨hfT C.1, C.2⟩⟩, C.1, rfl⟩
        invFun := fun p => ⟨p.2.1, by rw [p.2.2]; exact (Finset.mem_filter.mp p.1.2).2⟩
        left_inv := fun C => rfl
        right_inv := fun p => Sigma.subtype_ext (Subtype.ext p.2.2) rfl }
  haveI : ∀ W : T', Finite {C' : CycSub E_x (1 * ℓ) // f C' = W.1} := fun W => hfibfin W.1
  rw [hcount, hsigma, Nat.card_sigma, Finset.sum_coe_sort T' (fun W => Nat.card {C' : CycSub E_x (1 * ℓ) // f C' = W}),
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun W hW => ?_
  obtain ⟨C, rfl⟩ := hfsurj W ((hmemT W).mp (Finset.mem_filter.mp hW).1)
  exact hef C

end Count

end ModularCurve.RoofCountE7c

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q')
    (hα : (heckeAlphaC κ 1 ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ 1 ℓ).toRingHom.IsIntegral)
    (x y : ↥(ssPlaces q' 1 κ))
    (E_x E_y : WeierstrassCurve κ) [E_x.IsElliptic] [E_y.IsElliptic]
    (hx : E_x.j = (x.1).evalAt (jGeomGen κ 1)) (hy : E_y.j = (y.1).evalAt (jGeomGen κ 1)) :
    ssHeckeMatrixC q' κ 1 ℓ hα hβ y x =
      (Nat.card {C : AddSubgroup (E_x.baseChange κ).toAffine.Point //
        Nat.card C = ℓ ∧ ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E_x E_y, ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E_y E_x,
          ψ.ker = C ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _} : ℤ) :=
  ModularCurve.RoofCountE7c.ssHeckeMatrixC_one_apply_eq q' ℓ hℓ hℓq hα hβ x y E_x E_y hx hy

end

end S_ModularCurve_ssHeckeMatrixC_one_apply_eq_natCard_subgroup_dualPair
end P2MW
export P2MW.S_ModularCurve_ssHeckeMatrixC_one_apply_eq_natCard_subgroup_dualPair (solution)
